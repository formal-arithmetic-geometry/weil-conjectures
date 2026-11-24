# MDA: RealPushforward

Case: `RealPushforward`; Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
measurement import pin `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`.
Source declaration: `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one`.
Original probe: `probes/mprwe/Original.lean` (SHA256
`8be6deae773b28c7168aded66810828ab820b340f7a86ad0e18b0345896421f1`).
The exact root Exprs, implicit arguments and local context are in `probes/HeadAudit.lean`;
the new selected Kernel Exprs are in `mda/selected-root.jsonl.gz`; the
2,000-event parent-child window is in `mda/focused-window.jsonl.gz`, and
the exact object pair is in `mda/object-gateway.jsonl.gz`.

## 4.1 Gateway-to-cost

The fresh MDA root is `(2005,1)`, final `exact this` inferred-type/goal conversion;
it times out after 17,340,236 calls, 95,517.663 ms comparison-exclusive and
270.558 ms reduction-exclusive. M1 is 8,002,209 calls / 58,057.897 ms;
M2 is 4,364,762 / 36,326.143 ms; Matched is 4,973,262 / 1,129.868 ms.
The first structural difference is the `Polynomial.coeff` polynomial argument:
inferred `LinearMap.charpolyRev ...` versus expected
`FrobeniusModule.localPolynomial ...` (source/API, S0-S2). The full expressions
and local telescope are preserved by the head audit and selected-root JSONL.

| Gateway ID | Parent M0 path | Kernel branch / component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree comparison-exclusive ms | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| `2005:6`, parent 3 | `Eq`/coefficient path | application / `argument[1]` | `mda_top(2005,6).left_expr/right_expr`, heads `DFunLike.coe` / `DFunLike.coe` | Polynomial coefficient coercion | 8,002,209 | 95,513.891 | S: exact pair, inclusive ancestor |
| `2005:12`, parent 11 | same | second WHNF / Iota | `mda_top(2005,12).left_expr/right_expr`, `Finsupp.embDomain.match_1` on both sides | Polynomial/Finsupp expansion | 8,002,206 | 95,314.462 | S: exact pair, inclusive ancestor |
| `2005:33`, parent 32 | same | projection / field 0 | `mda_top(2005,33).left_expr/right_expr`, `Polynomial.proj` on both sides | Polynomial representation field | 8,002,199 | 94,602.521 | S: first selected polynomial field; inclusive |
| `2005:484`, parent 34 | same | application / `argument[0]` | `mda_top(2005,484).left_expr/right_expr`, `Matrix.charmatrix` on both sides | Characteristic matrix object path | 8,001,876 | 93,876.9 | S: first selected object head |
| `2005:535`, parent 531 | `Quiver.Hom` object argument | application / `argument[2]` | `mda_top(2005,535).left_expr/right_expr`, `WeilSheaf.stalkObj` on both sides | First concrete stalk object entry | 8,001,838 | 93,204.740 in object run | S: exact source pair, M1 |
| `2005:536`, parent 535 | same | lazy delta / `argument[9]` | raw enter pair `CategoryStruct.comp` / `CategoryStruct.comp` | First child within stalk object | included in ancestor | included in ancestor | S: exact parent-child trace, M1 |

These inclusive subtree times overlap and must not be added. The focused
window establishes the concrete stalk entry at call 535 and its first
child at 536. The earliest object-level entry in the whole root is still
only localized to the polynomial/`Matrix.charmatrix` route; the trace does
not establish that call 535 owns all subsequent M1 cost. The source group
partition below quantifies the stalk path without double-counting ancestors.

## 4.2 Definition/API path

The new `mda_group` rows partition direct comparison-exclusive time. The
`source` key is the nearest source head in the Kernel path, not a proof that
the definition itself caused the work. The selected field map resolves known
category fields; unresolved projections retain their numeric index.

| Candidate | Role | First seen | Kernel path | Direct M1 calls | Direct M1 exclusive ms | Intervention / evidence |
| --- | --- | --- | --- | ---: | ---: | --- |
| `LinearMap.charpolyRev` / `FrobeniusModule.localPolynomial` | producer | S0-S2, `Polynomial.coeff` argument | root to `2005:33` | included below | included below | Polynomial-head alignment: D (API counterfactual) |
| `Polynomial.proj` field 0 | gateway candidate | `2005:33` | projection from `2005:32` | included below | included below | S for entry, P for causal rank |
| `Matrix.charmatrix` | object gateway candidate | `2005:484` | application from `2005:34` | 8,001,876 inclusive | 93,876.9 inclusive | S: exact pair and parent-child path |
| `WeilSheaf.stalkObj` | first concrete source object | `2005:535` | `Quiver.Hom` argument[2] | 8,001,838 inclusive | 93,204.740 inclusive in object run | S: exact pair and parent-child path |
| `WeilSheaf.stalkObj`, projection[0] | amplifier/path owner | call 535, then grouped path | projection | 4,295,783 | 20,329.770 | S: direct M1 partition |
| `WeilSheaf.stalkObj`, dependent-body[1] | amplifier/path owner | grouped path | quick dependent body | 1,442,386 | 18,831.830 | S: direct M1 partition |
| `WeilSheaf.stalkObj`, argument[2] / function-head / argument[4] | amplifier/path owner | grouped path | application | 2,219,977 | 15,227.567 | S: direct partition; individual rows in `mda/validation.md` |
| `DFunLike.coe`, `ContinuousMap`, `Scheme.Hom.toLRSHom` | downstream components | old anatomy path and new Exprs | projection/coercion | not individually isolated | not individually isolated | P; reduction frequency is not causal rank |

The combined application row above is a display grouping only, not an
additional cost owner. Its exact constituent call counts are 257,395,
1,430,735, and 531,847 (sum 2,219,977), and times 5,416.363,
5,027.964, and 4,783.240 ms (sum 15,227.567 ms). The per-row values in
`mda/validation.md` are authoritative.

## 4.3 Root-to-source chain

Direct rewrite of `FrobeniusModule.localPolynomial` in the source proof
-> inferred concrete `charpolyRev` versus declared `localPolynomial`
-> first divergence in the polynomial argument of `Polynomial.coeff`
-> application/coercion `2005:6` and polynomial field `2005:33`
-> `Matrix.charmatrix` object comparison `2005:484`
-> `Quiver.Hom` argument enters concrete `WeilSheaf.stalkObj` at call 535,
then `CategoryStruct.comp` at 536 (fresh focused trace)
-> source-path `WeilSheaf.stalkObj` with direct M1 projection and dependent
body cost (20,329.770 and 18,831.830 ms)
-> nested scheme/continuous-map coercions (P)
-> generic `charpolyRev_eq_localPolynomial` handoff aligns the polynomial
representation before the concrete stalk, reducing the largest aligned root
to 2,873 calls / 13.648 ms comparison (CCMOA control).

## 4.4 Summary and controls

| Producer | Expansion gateway | Amplifier | Best one-factor intervention | Evidence |
| --- | --- | --- | --- | --- |
| Source/API `charpolyRev` versus `localPolynomial` (D) | Polynomial coefficient/coercion entry `2005:6`, then concrete `stalkObj` argument at 535 and `CategoryStruct.comp` child 536 (S) | `WeilSheaf.stalkObj` projection/dependent path (S); exact internal field order U | Same-obligation polynomial-head alignment: 17.34M calls to largest 2,873-call root; restoration of direct concrete rewrite returns timeout (D, API-level counterfactual) | New MDA partition and focused parent-child trace; existing CCMOA controls |

The aligned pair still differs at `Semifield.toCommSemiring` versus
`CommRing.toCommSemiring`, yet is cheap; that leaf is a negative control (N
as primary cost cause). The effective generic-polynomial boundary is fragile:
restoring the concrete rewrite punctures it. The intervention changes M0 and
the root comparison, so it does not demonstrate removal of one particular
original M1 child. No pre-finalization imported Expr was captured (U).

## Audit note

The `charpolyRev`/`localPolynomial` source handoff is **D** as an API-level
counterfactual: alignment and restoration preserve the theorem obligation,
although M0 changes. The polynomial and stalk gateways are **S** from exact
parent-child pairs. Projection and dependent-body times are additive direct
groups; exact internal field ownership remains **P/U**.
