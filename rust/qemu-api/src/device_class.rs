// Copyright 2024, Linaro Limited
// Author(s): Manos Pitsidianakis <manos.pitsidianakis@linaro.org>
// SPDX-License-Identifier: GPL-2.0-or-later

use std::{ffi::CStr, os::raw::c_void};

use crate::{
    bindings::{self, DeviceClass, DeviceState, Error, ObjectClass, Property, VMStateDescription},
    prelude::*,
    zeroable::Zeroable,
};

/// Trait providing the contents of [`DeviceClass`].
pub trait DeviceImpl {
    /// _Realization_ is the second stage of device creation. It contains
    /// all operations that depend on device properties and can fail (note:
    /// this is not yet supported for Rust devices).
    ///
    /// If not `None`, the parent class's `realize` method is overridden
    /// with the function pointed to by `REALIZE`.
    const REALIZE: Option<fn(&mut Self)> = None;

    /// If not `None`, the parent class's `reset` method is overridden
    /// with the function pointed to by `RESET`.
    ///
    /// Rust does not yet support the three-phase reset protocol; this is
    /// usually okay for leaf classes.
    const RESET: Option<fn(&mut Self)> = None;

    /// An array providing the properties that the user can set on the
    /// device.  Not a `const` because referencing statics in constants
    /// is unstable until Rust 1.83.0.
    fn properties() -> &'static [Property] {
        &[Zeroable::ZERO; 1]
    }

    /// A `VMStateDescription` providing the migration format for the device
    /// Not a `const` because referencing statics in constants is unstable
    /// until Rust 1.83.0.
    fn vmsd() -> Option<&'static VMStateDescription> {
        None
    }
}

/// # Safety
///
/// This function is only called through the QOM machinery and
/// the `impl_device_class!` macro.
/// We expect the FFI user of this function to pass a valid pointer that
/// can be downcasted to type `T`. We also expect the device is
/// readable/writeable from one thread at any time.
unsafe extern "C" fn rust_realize_fn<T: DeviceImpl>(dev: *mut DeviceState, _errp: *mut *mut Error) {
    assert!(!dev.is_null());
    let state = dev.cast::<T>();
    T::REALIZE.unwrap()(unsafe { &mut *state });
}

/// # Safety
///
/// We expect the FFI user of this function to pass a valid pointer that
/// can be downcasted to type `T`. We also expect the device is
/// readable/writeable from one thread at any time.
unsafe extern "C" fn rust_reset_fn<T: DeviceImpl>(dev: *mut DeviceState) {
    assert!(!dev.is_null());
    let state = dev.cast::<T>();
    T::RESET.unwrap()(unsafe { &mut *state });
}

/// # Safety
///
/// We expect the FFI user of this function to pass a valid pointer that
/// can be downcasted to type `DeviceClass`, because `T` implements
/// `DeviceImpl`.
pub unsafe extern "C" fn rust_device_class_init<T: DeviceImpl>(
    klass: *mut ObjectClass,
    _: *mut c_void,
) {
    let mut dc = ::core::ptr::NonNull::new(klass.cast::<DeviceClass>()).unwrap();
    unsafe {
        let dc = dc.as_mut();
        if <T as DeviceImpl>::REALIZE.is_some() {
            dc.realize = Some(rust_realize_fn::<T>);
        }
        if <T as DeviceImpl>::RESET.is_some() {
            bindings::device_class_set_legacy_reset(dc, Some(rust_reset_fn::<T>));
        }
        if let Some(vmsd) = <T as DeviceImpl>::vmsd() {
            dc.vmsd = vmsd;
        }
        bindings::device_class_set_props(dc, <T as DeviceImpl>::properties().as_ptr());
    }
}

#[macro_export]
macro_rules! impl_device_class {
    ($type:ty) => {
        impl $crate::definitions::ClassInitImpl for $type {
            const CLASS_INIT: Option<
                unsafe extern "C" fn(klass: *mut ObjectClass, data: *mut ::std::os::raw::c_void),
            > = Some($crate::device_class::rust_device_class_init::<$type>);
            const CLASS_BASE_INIT: Option<
                unsafe extern "C" fn(klass: *mut ObjectClass, data: *mut ::std::os::raw::c_void),
            > = None;
        }
    };
}

#[macro_export]
macro_rules! define_property {
    ($name:expr, $state:ty, $field:ident, $prop:expr, $type:ty, default = $defval:expr$(,)*) => {
        $crate::bindings::Property {
            // use associated function syntax for type checking
            name: ::std::ffi::CStr::as_ptr($name),
            info: $prop,
            offset: $crate::offset_of!($state, $field) as isize,
            set_default: true,
            defval: $crate::bindings::Property__bindgen_ty_1 { u: $defval as u64 },
            ..$crate::zeroable::Zeroable::ZERO
        }
    };
    ($name:expr, $state:ty, $field:ident, $prop:expr, $type:ty$(,)*) => {
        $crate::bindings::Property {
            // use associated function syntax for type checking
            name: ::std::ffi::CStr::as_ptr($name),
            info: $prop,
            offset: $crate::offset_of!($state, $field) as isize,
            set_default: false,
            ..$crate::zeroable::Zeroable::ZERO
        }
    };
}

#[macro_export]
macro_rules! declare_properties {
    ($ident:ident, $($prop:expr),*$(,)*) => {
        pub static $ident: [$crate::bindings::Property; {
            let mut len = 1;
            $({
                _ = stringify!($prop);
                len += 1;
            })*
            len
        }] = [
            $($prop),*,
            $crate::zeroable::Zeroable::ZERO,
        ];
    };
}

unsafe impl ObjectType for bindings::DeviceState {
    type Class = bindings::DeviceClass;
    const TYPE_NAME: &'static CStr =
        unsafe { CStr::from_bytes_with_nul_unchecked(bindings::TYPE_DEVICE) };
}
