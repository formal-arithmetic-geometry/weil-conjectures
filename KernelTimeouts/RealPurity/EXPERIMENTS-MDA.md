# MDA: RealPurity

Case: `RealPurity`; Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
measurement import pin `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`.
Source declaration: `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`.
Original probe: `probes/mprwe/Original.lean` (SHA256
`9557ddc4eeb4472daea0cf466ad91c635884c0c584f1fc340396c2b613640118`).
Exact root Exprs and local context: `probes/HeadAudit.lean`; fresh selected
Expr records: `mda/selected-root.jsonl.gz` and the focused parent-child
window `mda/focused-window.jsonl.gz`.

## 4.1 Gateway-to-cost

Fresh MDA root `(13603,1)` is the final `exact h` conversion in the rewritten
`hreal'` proposition. It times out after 17,310,168 calls, 103,491.083 ms
comparison-exclusive and 193.428 ms reduction-exclusive. M1 is 7,988,264
calls / 64,759.354 ms; M2 is 4,357,093 / 37,572.787 ms; Matched is
4,964,810 / 1,158.607 ms. The first exact S2 divergence is the
`Field.toCommRing` versus `AlgebraicClosure.instCommRing` instance below
`Eq`/`Polynomial.reverse`/`Polynomial.coeff` on both equality sides.

| Gateway ID | Parent M0 path | Kernel branch / component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree comparison-exclusive ms | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| `13603:4`, parent 1 | `Eq` polynomial side | application / `argument[1]` | `mda_top(13603,4).left_expr/right_expr`, `DFunLike.coe` on both sides | Coefficient coercion | 7,988,264 | 103,490.745 | S: exact ancestor |
| `13603:15`, parent 14 | same | second WHNF / Iota | `mda_top(13603,15).left_expr/right_expr`, `Finsupp.embDomain.match_1` on both sides | Polynomial/Finsupp expansion | 7,988,255 | 103,356.298 | S: exact ancestor |
| `13603:32`, parent 15 | same | application / `argument[3]` | `mda_top(13603,32).left_expr/right_expr`, generated heads `6` / `6` | Dependent polynomial argument | 7,988,252 | 103,038.123 | P: source mapping incomplete |
| `13603:575`, parent 38 | polynomial object route | application / `argument[0]` | `mda_top(13603,575).left_expr/right_expr`, `Matrix.charmatrix` on both sides | Characteristic matrix | 7,987,934 | 95,636.390 in focused run | S: exact object pair |
| `13603:620`, parent 618 | object argument | application / `argument[0]` | raw `Functor.obj` / `Functor.obj` pair in focused window | Functor object exposure | included in ancestor | included in ancestor | S: M1 parent-child |
| `13603:920`, parent 916 | `Quiver.Hom` object argument | application / `argument[2]` | `mda_top(13603,920).left_expr/right_expr`, `WeilSheaf.stalkObj` on both sides | Concrete stalk object | 7,987,785 | 94,886.850 in focused run | S: exact source pair |

Inclusive rows overlap. The focused trace supplies the missing object path:
`Matrix.charmatrix` -> `Functor.obj` -> `Quiver.Hom` argument
`WeilSheaf.stalkObj`. It establishes the concrete entry, not causal
ownership of the whole inclusive subtree by the `stalkObj` definition.

## 4.2 Definition/API path

| Candidate | Role | First seen | Kernel path | Direct M1 calls | Direct M1 exclusive ms | Intervention / evidence |
| --- | --- | --- | --- | ---: | ---: | --- |
| Two local-polynomial APIs | producer candidate | source and S2 | `Eq` to polynomial argument | included below | included below | S for divergence, P for causal role |
| Ring instance leaf | first exact difference | S2 | `Polynomial.reverse`/`coeff` | not isolated | not isolated | N as sufficient cost cause: aligned leaves retain root |
| `DFunLike.coe` and `Finsupp.embDomain.match_1` | gateway candidates | `13603:4`, `13603:15` | application, WHNF | inclusive in table 4.1 | inclusive in table 4.1 | S for entry; P for precise object gateway |
| `WeilSheaf.stalkObj`, dependent-body[1] | amplifier/path owner | call 920, then grouped path | quick dependent body | 1,439,853 | 23,260.620 | S: direct partition |
| `WeilSheaf.stalkObj`, projection[0] | amplifier/path owner | grouped path | projection | 4,288,238 | 20,650.526 | S: direct partition |
| `WeilSheaf.stalkObj`, argument[2] | amplifier/path owner | grouped path | application | 256,945 | 6,932.217 | S: direct partition |
| `WeilSheaf.stalkObj`, argument[4] / function-head | amplifier/path owner | grouped path | application | 1,959,135 | 10,094.481 | S: direct partition; component rows in `mda/validation.md` |
| `Functor.obj` / concrete stalk coercions | downstream object route | S2 aligned leaf audit; new MDA source groups | object/projection | not separately isolated | not separately isolated | P |

`mda_group` source is the nearest source head on an Expr path. The direct
rows partition cost; inclusive subtree rows must not be summed. The displayed
`argument[4]` / function-head grouping adds no separate cost owner.

## 4.3 Root-to-source chain

Source mixes `FrobeniusModule.localPolynomial` and
`WeilGroup.localPolynomial` in the pointwise `IsReal` proof
-> actual and goal polynomials have different concrete argument/instance
routes; first S2 leaf is the ring instance pair
-> `13603:4` coefficient coercion and `13603:15` Finsupp expansion
-> `Matrix.charmatrix` at 575 and `Functor.obj` at 620 in the focused M1
window; exact `WeilSheaf.stalkObj` object pair at 920
-> `WeilSheaf.stalkObj` projection/dependent-body direct M1 time
23,260.620 + 20,650.526 ms, with downstream continuous-map coercions (P)
-> whole-polynomial transport changes the comparison boundary and makes
the local proof cheap, but changes proof construction.

## 4.4 Summary and controls

| Producer | Expansion gateway | Amplifier | Best intervention and effect | Evidence |
| --- | --- | --- | --- | --- |
| Mixed polynomial/object API representation (P); ring leaf itself is N as sufficient cause | Coefficient coercion/WHNF entry, then `Matrix.charmatrix` 575 -> `Functor.obj` 620 -> `stalkObj` 920 (S) | `WeilSheaf.stalkObj` dependent/projection path (S), precise inner field order U | One-factor left/right/both ring-leaf alignment is a negative result: original 17,310,168 vs aligned 17,310,167 calls and timeout; restoration returns timeout. Whole-polynomial transport is a broader API counterfactual, not a one-factor intervention. | Fresh MDA partition and focused trace plus existing CCMOA controls |

The whole-polynomial transport boundary is fragile: direct `exact h` punctures
it. The same mathematical proposition is retained, but the transport changes
the proof construction and root comparison. No valid narrower intervention
currently isolates the object path; its causal source remains P. Imported
pre-finalization Expr is unavailable (U). The diagnostic probe's later
unknown-constant error is downstream of the measured timeout root.

## Audit note

The ring-instance leaf is **N** as a sufficient cause: the aligned root still
has 17,310,167 calls. The polynomial/object producer remains **P** because
whole-polynomial transport changes proof construction. The stalk path is
**S** for measured traversal and additive direct branch groups, but nearest-
head tags do not demonstrate ownership by a single stalk definition.
