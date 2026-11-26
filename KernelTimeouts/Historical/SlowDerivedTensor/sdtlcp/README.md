# Round-8 reduced data

Evidence prefixes in the report: `R` fresh root replay, `D` compiled Expr audit, `S` source synthesis trace, `F` control, `A` source audit, `H` prior exact-root path, `U` limitation. The pinned consumer revision is `bdab171985a5e6c6e44fc3920386b89fc5627ca3`. [R,D,S,F,A,H]

`lcp-path.lean` re-extracts the saved `icd_tensorObj_probe`, runs `Kernel.check`, descends 12 binders, and logs original and reduced Expr paths. `lcp-path.out` contains exact checked/stored `Lean.Expr` dumps, application spines, and all canonical/shortcut/field paths. `canonical-parent-paths.txt` has 58 parent paths from `checked-provider-instance-whnf` (append 19 `/fn` edges to reach each canonical constant); `field-app-paths.txt` has 26 checked and 26 stored field paths with argument 4. Repeated path counts are not counts of separate source selections. [R,D]

`lcp-decls.lean` and `.out` audit compiled wrapper, generic field, shortcut, and related declarations. `lcp-reduction.lean` and `.out` preserve the shortcut application and one delta-unfold result, including exact pre/post Expr dumps. [D,R]

`lcp-shortcut-f0.lean` is the copied defining module with a local trace option; `f0-selected-trace.txt` is its focused trace. F1 and F4 add post-definition registration attributes and give the copied anonymous instance an explicit probe name to address those attributes. F2 suppresses canonical registration before the definition; F3 raises canonical priority before it. The `f*-result.txt`, `f2-candidate-trace.txt`, `f2-error.txt`, and `f3-candidate-trace.txt` files hold focused outcomes. [S,F]

| Probe | Lean exit | Measured result | Evidence |
| --- | ---: | --- | --- |
| F0 | 0 | Canonical selected. | [F] |
| F1 | 0 | Canonical selected; later shortcut suppression has no effect on stored body. | [F] |
| F2 | 1 | No matching final candidate; source definition fails. | [F] |
| F3 | 0 | Canonical selected at priority 2000. | [F] |
| F4 | 0 | Canonical selected; later shortcut priority change has no effect on stored body. | [F] |

`lcp-generic.lean`, `lcp-generic-with-import.lean`, and their focused traces replay the generic class-site candidate array without/with the shortcut import. Both source copies encounter later unrelated rewrite errors; use only their class-site trace, not their whole-module exit status. F5 is inapplicable at the shortcut's own definition because an import of itself is cyclic; F6's condition (a matching local concrete monoidal instance) is absent. [S,F,A,U]

The raw Lean outputs are scratch artifacts; reduced compiler diagnostics here have machine paths stripped. No historical serialized Expr or elaborator event is claimed. [U]
