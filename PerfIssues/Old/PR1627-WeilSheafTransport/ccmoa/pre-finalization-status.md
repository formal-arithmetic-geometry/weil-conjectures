# PR1627 pre-finalization probe status

The source-local scratch probe imported the shared MOE command and inserted
`#moe_elab` immediately before the direct `powFunctor` declaration. Its term
was a type-annotated copy of the direct `obj`/`map` structure literal.
It ran with Lean 4.35.0, one Lean process, the built current-case imports,
`Elab.async=false`, and `maxHeartbeats=10000000`. It produced no S2 lines
after fifteen minutes and was interrupted. The S2 generated-law value is
therefore unavailable. The previous `moe/source-generated.snapshot` only
contains an unrelated lambda at S2; its generated-law records are S4.

No Kernel counter or causal claim is derived from this incomplete run.
