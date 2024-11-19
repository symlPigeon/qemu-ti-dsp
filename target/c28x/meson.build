gen = [
  decodetree.process('insn16.decode', extra_args: [ '--static-decode=decode_insn16', '--insnwidth=16' ]),
  decodetree.process('insn32.decode', extra_args: '--static-decode=decode_insn32'),
]

c28x_ss = ss.source_set()
c28x_system_ss = ss.source_set()

c28x_ss.add(gen)
c28x_ss.add(files(
    'cpu.c',
    'disas.c',
    'translate.c',
    'helper.c'
))

c28x_system_ss.add(files('machine.c'))

target_arch += {'c28x': c28x_ss}
target_system_arch += {'c28x': c28x_system_ss}