## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.TwoRootNormalModelFunctionField`.
Main declaration: `AlgebraicGeometry.TwoRootNormalModel.functionField_and_normalization`.
This is stage 2: its proof is exactly `sorry`. All eight chart helpers have real bodies,
carry this item's blueprint tag, and are listed in `lean.declarations`. No statement
correction, new DAG node, or dependency-record repair is needed.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Ground field k0 | `(k₀ : Type u) [Field k₀]` |
| Integral finite-type U over k0 | `(U : Scheme.{u}) [IsIntegral U]`, structural map `p`, `[LocallyOfFiniteType p] [QuasiCompact p]` |
| K = k(U) | The existing generic-stalk carrier `U.functionField` throughout |
| n >= 1 | `(n : ℕ) (hn : 1 ≤ n)` |
| Integral Y with integrally closed domain local rings | `[IsIntegral Y]` and `hnormal`, explicitly asserting both local properties |
| P = P1_U | `ProjectiveSpace (ULift.{u} Bool) U`: exactly two homogeneous coordinates; false is the denominator of the x-chart, true that of the y-chart |
| Finite surjective U-morphism q | `q : Y ⟶ ProjectiveSpace ... U`, `[IsFinite q] [Surjective q]`; the U-structure on Y is the composite of q with the displayed structural projection |
| Every affine base open Spec R in U | `V : U.affineOpens`; use its canonical ring `Γ(U,V.1)`, avoiding an irrelevant choice of a ring isomorphic to it |
| Affine source C and A charts | `hcharts V i` includes `IsAffineOpen (sourceChart q V.1 i)` for both Boolean values |
| Specified quotient over the target chart | `presentation q V.1 i r s` is polynomial evaluation over `Γ(U,V.1)` using structural coefficients and the actual pulled-back standard coordinate; surjectivity plus `RingHom.ker = relations ...` is precisely the quotient presentation, not merely the two equations |
| C: a^n=x, b^n=x-1 | `i=false`; variables 0,1,2 are x,a,b in `relations` and `presentation` |
| A: v^n=y, u^n=1-y | `i=true`; variables 0,1,2 are y,v,u; this harmless reordering gives exactly the displayed ideal |
| Compatibility under restriction of base opens | `r s` are sections on the full inverse images of the two standard opens, and `rootOn` restricts them canonically to each V. Conversely the node's compatible coordinate sections glue uniquely to these sections by the sheaf axiom, because base affines cover U. Thus this representation imposes no extra gluing hypothesis |
| y=x^-1 on the overlap | The target coordinates are the canonical `ProjectiveSpace.coordRatio` for the two complementary homogeneous coordinates; this identity is built into them, not replaced by an arbitrary coordinate choice |
| v=a^-1 and u=b/a on the overlap | `hv` and `hu` use actual restrictions to `q ⁻¹ᵁ (standard ... false ⊓ standard ... true)` and assert `v*a=1`, `u*a=b`. The first makes a a unit there, so these are exactly the two division formulas |

Conclusion-by-conclusion correspondence:

| Node | Lean |
| --- | --- |
| P is integral | First existential witness is `IsIntegral (ProjectiveSpace ... U)`; it is a conclusion, not an assumption |
| k(P)=K(x) | `e : RatFunc U.functionField ≃+* P.functionField` |
| The variable is the specified x-coordinate | `e RatFunc.X` equals the germ of `ProjectiveSpace.coordRatio ... false true` |
| Constants K are embedded through P -> U | The first `Spec.map` triangle with `e.symm`, `P.fromSpecFunctionField`, the structural projection, and `U.fromSpecFunctionField` |
| Inclusion k(P) -> k(Y) is induced by q | The existential algebra structure is constrained by the second `Spec.map` triangle, equating its generic-point morphism with `Y.fromSpecFunctionField ≫ q`; this fixes its ring map uniquely |
| a,b are the indicated chart coordinates | Their equalities with `Y.germToFunctionField _ (r false)` and the germ of `s false`. These are the same germs as on every nonempty base affine by restriction naturality |
| a^n=x, b^n=x-1 | The two power equalities using `algebraMap` and `e RatFunc.X` |
| k(Y)=K(x)(a,b) | `IntermediateField.adjoin P.functionField {a,b} = ⊤` with the constrained algebra structure |
| The extension is finite | `FiniteDimensional P.functionField Y.functionField` |
| Every nonempty base affine and each chart | `∀ (V : U.affineOpens) (_ : Nonempty V.1) (i : Bool), ...`; source-chart nonemptiness is supplied in the conclusion for the germ maps |
| S_C, S_A are integrally closed domains | `IsDomain Γ(Y,sourceChart ...) ∧ IsIntegrallyClosed Γ(Y,sourceChart ...)`; `hcharts` identifies these rings with precisely the displayed quotient rings |
| Their fraction field is k(Y) | `IsFractionRing Γ(Y,sourceChart ...) Y.functionField`, using Mathlib's canonical germ algebra for that open |
| They equal the integral closure of R[x] or R[y] | The target ring is `Γ(P,targetChart ...)`, canonically R[x] or R[y] by the recorded standard-chart theorem. Its algebra on k(Y) is explicitly constrained to be `germ ∘ q.app`; the equality `(integralClosure ... : Set Y.functionField) = Set.range (Y.germToFunctionField ...)` says exactly that its integral closure is the embedded source ring |
| The identifications agree on overlaps | Every embedding in the preceding equality is the canonical germ, hence restrictions on intersections have the same image. The last generic-point equality additionally forces the global normalization identification to use those very embeddings |
| q is the normalization of P in k(Y), over P | `E : Y ≅ P.normalizationIn Y.functionField`, `E.hom ≫ P.fromNormalizationIn ... = q`, and `Y.fromSpecFunctionField ≫ E.hom = (P.fromSpecOfAlgebraFunctionField ...).toNormalization` |
| No additional smoothness, primality, root of unity, or base normality | No such binder appears. k0 is arbitrary, and U need not be normal |

Dependencies read and used (the complete signatures and docstrings were opened):

- `def-weil-field`: Mathlib `Field`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`, and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, with its documented integral specialization `Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`. The component-product construction is not appropriate to replace this integral carrier.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`; its affine preimage condition is used unchanged.
- `def-nagata-projective-space-base-change`: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace` and its canonical structural projection. The standard opens and coordinate ratios use the upstream chart interface through `ProjectiveSpace.OfInvertible`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`; `IsIntegrallyClosed` is Mathlib's normal-domain property.
- `def-fin-normalization-extension`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`.

The modules of stated proof dependencies are imported without `public`:
`ProjectiveSpaceStandardCharts` (the canonical affine chart ring theorem),
`Mathlib.Algebra.MvPolynomial.Basic` (polynomial domains),
`LocalDimensionFormula` (the recorded dominant generic-stalk algebra),
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` (finite-dimensional domains are fields),
`Mathlib.AlgebraicGeometry.Noetherian` (locally finite type preserves local Noetherianity),
and upstream `NormalSectionsFiniteProduct` (`Scheme.normal_sections_finite_product`).
The affine fraction-field lemma is already in the publicly used Mathlib function-field API.
`lem-sfb-finite-normal-cover-normalization` has no recorded Lean declaration, so there is
no module to import for it. Its affine argument is included in step 6 of the proof docstring.
No unrecorded theorem is introduced to stand in for that proof dependency.

Sources read: Stacks `properties.tex`, `lemma-normal-integral-sections` (0358);
`morphisms.tex`, `lemma-integral-scheme-rational-functions` (01RV),
`definition-function-field` (01RW), and `lemma-characterize-normalization` (035I).
The current blueprint was searched under `literature/blueprint/latest/`; this auxiliary
node's source is its explicit returned two-root argument, not a separate blueprint unit.

Edge cases checked:

- n=1: relations give a=x, b=x-1, v=y, u=1-y, and the function field extension can be trivial.
- Arbitrary n and every characteristic: no separability, invertibility, or degree n² is asserted; only finite-dimensionality. In characteristics where the chart algebra cannot be a normal domain, the existing integrality/normality hypotheses govern applicability.
- Empty base affines are included in `hcharts`; their zero section rings have the corresponding zero-ring quotient presentation. Domain and fraction-field conclusions are restricted exactly to nonempty affines. Integral U and Y themselves are nonempty by definition.
- Infinity is covered by `i=true` with roots (v,u). The overlap identity only inverts a on the actual overlap, where `v*a=1`; it never inverts a globally.
- Nonaffine and nonnormal U are allowed; the use of global sections on standard preimages encodes only gluing of coordinate sections, not affineness of those whole preimages.
- Universes are explicit. Schemes and the ground field use their common ambient `u`; the two homogeneous coordinates use `ULift.{u} Bool`, so this is relative P1 at any scheme universe. All declarations set `autoImplicit false`.

Searches performed:

1. `msearch.py ... leanfinder "A finite normal two-root chart model over projective line has function field K(x)(a,b) with a^n=x and b^n=x-1 and is the normalization"`: 8 hits, mainly Weierstrass coordinate/function fields and the unrelated arithmetic `FunctionField`; none states this arbitrary normal chart-model assertion.
2. `msearch.py ... loogle "Scheme.functionField, integralClosure, RatFunc"`: 0 hits; reports unknown identifier `Scheme.functionField` in that search service. The actual Mathlib source was read directly.
3. `msearch.py ... grep "twoRoot|two_root|normal.*model|RatFunc" AlgebraicGeometry`: 0 hits.
4. `rg` for `twoRoot|two_root|TwoRoot|two-root` in both project roots and `dag/lean_names_upstream.json`, plus the item id in `lean/WeilConjectures`: no matching existing theorem. The existing `RelativeFermatKummerCurve.exists_finite_kummer_cover` was read in full: it constructs a particular smooth Fermat cover under prime/root-of-unity/normal-base hypotheses, rather than giving this result for arbitrary integral normal models and n. Reusing it as an exact match would change the statement.

Validation: `scompile.py Q144 lem-sfb-two-root-normal-model-function-field <module>`;
the server confirmation compiles cleanly in 3.0 seconds. The wrapper's initial overlay
attempt reported `OSError(28, 'No space left on device')`, but its prescribed current-source
server confirmation succeeded, and the wrapper returned exit 0. No compiler or global
build was run outside the prescribed wrapper. The first attempt found one syntactic
nonempty-instance elaboration issue in an inferred open and an unused lambda variable;
these were corrected by explicitly naming `sourceChart` and naming the unused variable `_z`.

## Second reading by Q144

This is an independent clause-by-clause reading by the maintainer's second reader of the delivery
at 1ed64143f399. It replaces the earlier same-worker self-check. The node is the live
landed split statement, unchanged. Only its `lean` field is new.

Hypotheses:
- Field k0 and integral U of finite type over k0: `[Field k₀]`, `[IsIntegral U]`, and
  `p : U ⟶ Spec k₀` with `LocallyOfFiniteType` and `QuasiCompact`. Finite type is lfp plus qc, so
  this matches the node. The universe `k₀ : Type u` is forced by `Spec (.of k₀)`, so it is no
  restriction. OK.
- n ≥ 1: `hn : 1 ≤ n`. OK.
- Integral Y whose local rings are integrally closed domains: `[IsIntegral Y]` plus `hnormal`. The
  domain half of `hnormal` is redundant but not stronger. OK.
- q is a finite surjective U-morphism to P = P^1_U: `q : Y ⟶ ProjectiveSpace (ULift Bool) U` with
  `[IsFinite q] [Surjective q]`. The U-structure on Y is the one induced by q. OK.
- Charts: `standard U i` is the upstream `ProjectiveSpace.standardOpen`. `targetChart` is its meet
  with π⁻¹V, which is Spec R[x] or Spec R[y]. The node's x is `coordRatio false true`, which is
  T_true/T_false on D₊(T_false) (OfInvertible.lean:57). The node's y is `coordRatio true false`.
  So y = x⁻¹ is built in. OK.
- For every affine V, the source charts are affine: `IsAffineOpen (sourceChart q V.1 i)`. OK.
- The presentation S_C, S_A over the chart: `presentation` evaluates polynomials over Γ(U,V). It
  sends the coefficients through the structural composite, variable 0 to the pulled-back chart
  coordinate, and variables 1, 2 to the root sections. It is surjective, and its kernel is exactly
  `relations`: (X1^n − X0, X2^n − (X0 − 1)) for C and (X1^n − X0, X2^n − (1 − X0)) for A, with
  variables (y,v,u). Together these say S_C ≅ R[x,a,b]/(a^n−x, b^n−(x−1)) and
  S_A ≅ R[y,v,u]/(v^n−y, u^n−(1−y)) as R[x]- resp. R[y]-algebras. OK.
- The presentations commute with restriction: r, s are sections over the full q⁻¹(D₊(T_i)), and
  `rootOn` restricts them. The base affines cover U, so compatible families glue uniquely to such
  sections. The two forms are equivalent. OK.
- On the overlap, v = a⁻¹ and u = b/a: `hv` (v·a = 1) and `hu` (u·a = b) on
  q⁻¹(D₊(T_false) ⊓ D₊(T_true)). OK.
- Empty V: Γ(U,∅) is the zero ring, so the hcharts clause holds trivially (the kernel is ⊤ =
  `relations`). The Lean has no hidden nonemptiness condition. OK.

Conclusions:
- P is integral: the first existential witness. OK.
- k(P) = K(x) with K embedded via P → U: `e : RatFunc K ≃+* k(P)` with
  `e X = germ(coordRatio false true)`. The Spec triangle through `fromSpecFunctionField` and `↘ U`
  fixes e on K to be the generic-point map of P → U. A field map out of RatFunc K is determined by
  its value on K and on X, so e is pinned. OK.
- Inclusion k(P) ↪ k(Y) induced by q: the existential `Algebra` is pinned by the triangle
  Spec(algebraMap) ≫ P.fromSpecFunctionField = Y.fromSpecFunctionField ≫ q. A morphism from Spec of
  a field through the generic point determines the field map, so this algebra is the dominant
  generic-stalk map. It is not an arbitrary one. OK.
- The generators: a, b are the germs of `r false` and `s false`, with a^n = x, b^n = x − 1, and
  `adjoin k(P) {a,b} = ⊤`. Finiteness is `FiniteDimensional`. OK.
- For every nonempty affine V and each i: the chart algebra Γ(P, targetChart) → k(Y) is pinned as
  germ ∘ q.app. The clauses `IsDomain`, `IsIntegrallyClosed` and `IsFractionRing` hold for
  Γ(Y, sourceChart), using Mathlib's germ algebra. The integral closure equals the range of the
  germ. Agreement on overlaps is automatic, because every embedding is a canonical germ. OK.
- Normalization: E : Y ≅ P.normalizationIn k(Y) over P (`E.hom ≫ fromNormalizationIn = q`), and E
  respects the generic points (`… = fromSpecOfAlgebraFunctionField.toNormalization`). It uses the
  pinned algebra above (Normalization.lean:293–309). OK.
- No smoothness, primality, roots of unity, characteristic condition or normality of U appears. OK.

Truth check: q is finite and targetChart is affine, so S is finite over R[x]. S is an integrally
closed domain with Frac S = k(Y), so S is the integral closure. The conclusions follow as in the
node's steps 1–6. In characteristic p with p | n the hypotheses cannot hold, because S_C is not
reduced. The statement is then vacuous, as the S1 review noted.

One definition per notion: there is no existing two-root declaration in side-live lean/ or the DAG.
The helpers belong to this item and have real bodies. `coordRatio` and `standardOpen` are reused
from upstream and not copied. The algebra k(P) → k(Y) is a pinned existential, not a new
definition. `def-sfb-dominant-function-field-map` (dominantFunctionFieldAlgebra) is only a
proof_dep of the node, so it cannot be a stmt_dep. Advisory only.

Imports: stmt_dep modules are imported `public`. Proof-dep modules
(ProjectiveSpaceStandardCharts, LocalDimensionFormula, NormalSectionsFiniteProduct) are imported
without `public` under rule 7. All three exist on live. `lem-sfb-finite-normal-cover-normalization`
has no Lean record yet, so it has no import.

Gates: the proof is `sorry`; the docstrings carry the source and the blueprint tag; the theorem
docstring follows the six steps; there is no pro-étale substitute; `autoImplicit false`; the
universes are bound. The worker's compile is accepted as evidence (scompile, 3.0 s). This review
does not change the Lean.
