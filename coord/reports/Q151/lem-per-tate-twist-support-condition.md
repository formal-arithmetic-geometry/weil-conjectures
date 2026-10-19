## Worker report

The item is stated in `Sheaf.Paper.TateTwistSupportCondition` as
`AlgebraicGeometry.Scheme.pbcTateTwistSupportCondition`. The original node's statement,
statement dependencies, proof and proof dependencies are unchanged. Three dependency
records receive §1(B) coordinate specializations, described below. There are no new nodes
and no statement correction.

The category is literally `AlgebraicGeometry.Scheme.pbcQbarCategory l Ω X`, the recorded
finite-stage pair category. An object's field is `M.stage`, its rational object is `M.obj`,
and its complete integral complex is `M.obj.obj.obj`. The finite field is the existing
canonical small model `pbcFiniteField l Ω M.stage`; the rationalization inverts the existing
`pbcStageUniformizer`. No discrete Qbar sheaf on the small etale site is used.

Hypotheses, individually:

- Prime l: `(l : ℕ) [Fact l.Prime]`.
- Chosen algebraic closure: `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`. Its universe is independent of the scheme universe.
- The field and scheme: `(k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))]`.
- Separatedness: `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together with
  `[QuasiCompact (X ↘ Spec (.of k))]`, as in the project convention.
- The category's admissible scheme data: `[IsNoetherian X]`,
  `[hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]`, and
  `[hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`. Noetherianity and finite dimension
  follow from finite type over a field; invertibility is already required by
  `def-weil-pbc-qbar-category`. These supply that recorded category's actual parameters;
  they do not assume a bound on the dimension of an individual support.
- The complex and arbitrary signed exponent: `(M : pbcQbarCategory l Ω X) (m : ℤ)`.
  There is no auxiliary arbitrary twisting object or lissity hypothesis.

Clauses, individually:

1. `M(m)` is `pbcTateTwist l X Ω M m`. This definition's codomain is the same
   `pbcQbarCategory l Ω X`. Its integral representative is the actual exact sheaf tensor
   by `coefficientTwistLine ... (purTwistIntegralModule X l E) m`, transported through
   `purCoefficientIso`, then mapped to the derived category. The named theorem
   `pbcTateAmbient_mem` supplies exactly the completion, boundedness and constructibility
   proofs needed for restriction; rationalization is `pbcConditionalRational`. Thus the
   membership clause is in the constructed object's type, not an extra tautological
   conjunct about a full-subcategory object's property field.
2. For every `a : ℤ`, the first conjunct asserts invertibility of the component of
   `pbcTateCohomologyMap` at `M.obj`. Its source is scalar-localized
   `H^a(pbcTateAmbient M)`; its target is scalar-localized ordinary sheaf tensor of
   `H^a(M)` with that same signed line. The map is the inverse of the published exact
   functor `mapDerivedCategoryHomologyFunctorIso`, whiskered with the full integral
   inclusion, then extended by `ScalarLocalization.transportNat`. It is a natural
   transformation on the entire rational finite-stage category, including every
   fraction arrow. This is a natural cohomology-sheaf comparison, not a bare numerical
   equality or an arbitrary isomorphism between unidentified objects. As prescribed by
   the common-stage model, the comparison can be computed after transport to any common
   finite coefficient field: all inputs are the fixed coefficient restrictions, the
   published root line and its normalized scalar action.
3. The second conjunct is the natural geometric-fibre tensor isomorphism. For every
   `a`, algebraically closed `κ`, and `x : Spec (.of κ) ⟶ X`, it compares
   `pbcTateRational ... ⋙ pbcRationalCohomologyFibre ... a` with
   `pbcRationalCohomologyFibre ... a ⋙ pbcFibreTensorRight Ω (pbcTateLineFibre ... m κ x)`.
   The fibre functor uses `pbcActualCompletedPull`, the actual
   `purCoefficientModel`, exact `pointCompletedDerivedSections`, ordinary cohomology,
   and `ModuleCat.extendScalars` along the actual finite-field embedding into Ω.
   Its rational extension is uniquely normalized on every unchanged object and every
   scalar-tensor arrow. This is the adic geometric fibre of the cohomology sheaf,
   computed by t-exact geometric pullback; it is not a stalk of a discrete non-torsion
   etale sheaf. `pbcFibreTensorRight` is literally the ordinary TensorProduct of Ω-vector spaces.
   Its functor laws are isolated as a named obligation, retaining independent sizes.
4. The third conjunct says `Module.finrank Ω (pbcTateLineFibre ... m κ x) = 1`
   at every geometric point. The line is the actual same signed coefficient line
   in degree zero; it is not existentially replaced by some one-dimensional space.
5. The fourth conjunct is, verbatim for every cohomological degree `a`,
   `pbcQbarCohomologySupport ... (pbcTateTwist ... M m) a =
   pbcQbarCohomologySupport ... M a`. Here closed support is the closure of the
   nonzero geometric-cohomology-fibre locus. The geometric point over an underlying
   point is the existing `X.algClosurePoint x`, through the standard algebraic closure
   of its residue field, with the actual residue-field morphism to X.
6. The final conjunct is the iff between `PbcSupportCondition ... M` and
   `PbcSupportCondition ... (pbcTateTwist ... M m)`. The definition states all inequalities
   in degree `-i`. For nonempty support it requires `0 ≤ i` and bounds the topological
   Krull dimension by `i.toNat`; empty support satisfies every bound, exactly encoding
   dimension minus infinity.

Dependency declarations used:

- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`,
  `qbarStageFieldEquiv`, and the existing `pbcStageCategory`, `pbcStageLocalization`,
  `pbcFiniteField`, `pbcStageDatum`, `pbcStageUniformizer` specializations it imports.
- `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`, publicly retaining
  `IntrinsicCoefficientTwists` and `CoefficientTwistsDetailed`:
  `WeilConjectures.coefficientTwistLine`, `integralSheafTwist`, and
  `purTwistIntegralModule`. All signed powers, duals and roots are reused.
- `Sheaf.Paper.CompletedCoefficientPresentationTransport`:
  `WeilConjectures.purCoefficientIso`, `purOrdinaryCoefficientModel`, and
  `purCoefficientModel`. These are normalized by finite quotient projections.
- Mathlib `DerivedCategory.homologyFunctor` and the upstream
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`.
- `Sheaf.Paper.PbcRationalTransport`: `CategoryTheory.ScalarLocalization.transport`
  and `transportNat`; `Sheaf.Paper.PbcScalarExtension`:
  `AlgebraicGeometry.Scheme.pbcConditionalRational`.
- `Sheaf.Paper.PbcCompletedPullbackActual`:
  `AlgebraicGeometry.Scheme.pbcActualCompletedPull`;
  `Sheaf.Paper.PointSectionsScalarExtension`:
  `WeilConjectures.pointCompletedDerivedSections`.
- `WeilConjectures.SixFunctors.Etale.Perverse.Basic`: publicly retained original
  finite-coefficient support and cosupport definitions and their dimension convention.
- The two proof prerequisites `lem-per-tate-twist-lisse-line` and
  `lem-per-adic-lisse-cohomology-calculus` have no recorded Lean module in the shared DAG;
  the main theorem's proof docstring retains both nodes and their complete mathematical
  roles. They are proof work, not hypotheses substituted into the statement.

Edge cases checked before writing: m=0 is the actual tensor unit; negative m uses the
published dual line rather than truncating the exponent to a natural number. The zero
complex and vanishing cohomology degrees have zero fibres and empty closed support.
An integral lattice killed by a power of the uniformizer represents the zero rational
object: scalar extension to Ω kills its fibres too, so the support definition does not
mistake integral torsion for nonzero Qbar support. For the empty scheme there are no
geometric points, all fibre clauses are vacuous and
all support inequalities hold. Nonempty support in a negative bound fails; empty support
still passes. Rank zero cannot accidentally serve as the Tate line because the line is
the prescribed root construction and the dimension-one conclusion is explicit. The
scheme and coefficient universes are independent; the small finite coefficient model
is the published Shrink transport and module fibres live in `max (u+1) w`.

Searches actually made:

- `msearch.py ... leansearch "Tate twists preserve supports of cohomology sheaves"`:
  eight generic complex-support/shift hits; no Tate twist or geometric support match.
- `msearch.py ... leanfinder "Tate twist support condition derived category lisse line"`:
  eight generic derived t-structure hits; no exact statement.
- `msearch.py ... loogle "SupportCondition, IsLisse, homologyFunctor, tensor"`:
  no hit; unknown SupportCondition identifier in that search service.
- `msearch.py ... grep "TateTwist|tateTwist|SupportCondition" Mathlib`:
  no hit.
- `rg` in the named Mathlib, upstream WeilConjectures, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: only the generic etale support condition and the
  already published coefficient twists/transport infrastructure; no Qbar support
  specialization or this lemma. A follow-up residue-field search found the already
  published `Scheme.algClosurePoint`; the support uses it directly. Searches for every new declaration name found none.
  The item-id grep in upstream source likewise found none.

All theorem proofs in this delivery are `sorry`, as required for stage 2. Every
construction has real data. The only chosen functor is uniquely characterized on
objects and all pure-tensor arrows, with additivity included; it is not selected from
an unconstrained Nonempty. Sources and full natural-language proofs accompany the
named linearity, rational-fibre descent, constructibility and main obligations.
There is no STATEMENT-DISPUTED flag: the original mathematical statement is retained.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: the existing Mathlib match is correct for ambient
ordinary cohomology, and is used verbatim. It does not directly take an object of the
raw rational finite-stage pair category. `PbcCohomologySheaves` specializes it to the
actual integral full subcategory, extends its maps through the literal scalar
localization, and gives the completed geometric fibres and their uniquely normalized
rational extension. The node changes only in `lean`; `mathlib_match` is retained.

`def-coefficient-twists-detailed`: the currently recorded module is
`FixedFinitePositiveCoefficientTwist`, whose primary declaration has positive finite
coefficients; its publicly imported intrinsic Qbar construction uses another category.
Neither accepts the actual PBC pair object. `PbcCoefficientTwists` publicly retains that
whole interface and transports the same signed line to PBC modules by the actual
coefficient isomorphism, then uses exact derived tensor, the integral subcategory,
raw rationalization and the unchanged pair stage. It also exposes the canonical
cohomology comparison and the fibre of that precise line. The node changes only in
`lean`; the new record's note explains this coordinate mismatch.

`def-per-support-condition`: the recorded generic etale derived-category support
predicate cannot be applied to the adic Qbar pair object (and its upstream docstring
explicitly warns about non-torsion coefficients on the etale site). The repair supplies
the support half needed here in `PbcSupportCondition`, using actual completed geometric
fibres, closed support and the same inequalities/empty-support convention. Its public
import retains both original finite-coefficient support and cosupport declarations;
no new or arbitrary Verdier dual is introduced. The node changes only in `lean`.

## Second reading by Q151

Independent reading by the maintainer's second reader (NT-cc review service, 2026-10-18),
replacing the author's self-audit that stood here (delivery-errors H11). I opened the
node, its source place, the four statement dependencies and their recorded declarations,
and all four delivered modules.

Node statement as a list, with the Lean and verdict:

- X separated of finite type over a field k: `(k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [IsSeparated ..] [LocallyOfFiniteType ..] [QuasiCompact ..]`. OK.
- D^b_c(X, Qbar_l) of def-weil-pbc-qbar-category: `pbcQbarCategory l Ω X`, which is the
  recorded `PbcFiniteStagePairCategory l Ω X hDim.out hInv.out`. Its parameters
  `[IsNoetherian X]`, `hDim` and `hInv` follow from finite type over k (noetherian, finite
  dimension) or are part of the category's definition (l invertible). They are not stronger
  than the node. Ω is any algebraic closure of ℚ_[l] in an independent universe w. OK.
- M and m ∈ ℤ: `(M : pbcQbarCategory l Ω X) (m : ℤ)`. OK.
- M(m) = M ⊗^L Qbar(m): `pbcTateTwist l X Ω M m`, at the same stage, rationalizing
  `pbcTateAmbient` (= `mapDerivedCategory` of `restrict(iso.inv) ⋙ integralSheafTwist m ⋙
  restrict(iso.hom)`). `integralSheafTwist` is the ordinary sheaf tensor with
  `coefficientTwistLine` of `purTwistIntegralModule`: the unit for m = 0, tensor powers for
  m > 0, internal Hom dual for m < 0. This is the node's three cases. Termwise tensor equals
  the derived tensor because the line is locally free of rank one. OK.
- M(m) ∈ D^b_c: carried by the codomain. The membership obligation is
  `pbcTateAmbient_mem` (a sorry theorem with a proof docstring). OK.
- A natural isomorphism H^a(M(m)) ≅ H^a(M) ⊗ L for every a: conjunct 1,
  `IsIso ((pbcTateCohomologyMap ..).app M.obj)`. The map is transportNat of the inverse of
  `mapDerivedCategoryHomologyFunctorIso` for the exact tensor. It is canonical and natural
  on the whole rational stage. It is not an arbitrary iso. OK.
- Fibre at every geometric point is H^a(M)_x ⊗ L_x with L_x one-dimensional: conjunct 2.
  This is a natural iso, for every a and every algebraically closed κ and point
  x : Spec κ ⟶ X, of `pbcTateRational ⋙ pbcRationalCohomologyFibre` with
  `pbcRationalCohomologyFibre ⋙ (− ⊗_Ω L_x)`. Conjunct 3 gives `finrank Ω L_x = 1` for
  the actual line fibre. The fibre is the completed pullback to the point, exact point
  sections, H^a and then extension of scalars to Ω. That is the adic stalk of the Qbar
  cohomology sheaf, and torsion is killed. OK.
- Supp H^a(M(m)) = Supp H^a(M) for every a: conjunct 4, with `pbcQbarCohomologySupport`
  = closure of the set of x whose fibre at `X.algClosurePoint x` is nonzero. OK.
- SuppCon(M) ⟺ SuppCon(M(m)): conjunct 5, with `PbcSupportCondition`: for all i, a
  nonempty support in degree −i requires 0 ≤ i and topologicalKrullDim ≤ i. This is exactly
  dim Supp H^{−i} ≤ i with dim ∅ = −∞. OK.

Edge cases:

- m = 0 is the unit, and m < 0 is the dual (no truncation of m).
- The zero complex and vanishing degrees give an empty support. The empty scheme makes
  the fibre clauses vacuous.
- Nonempty support with i < 0 fails, and empty support always passes.
- Integral torsion has zero Ω-fibre.
- The universes u and w are independent, and no variable is unbound.

Searches: I repeated an rg for `TateTwist|tateTwist|SupportCondition|pbcQbarCohomologySupport`
in Mathlib, upstream WeilConjectures and lean/Sheaf. It found only the generic etale
`SupportCondition` and `CosupportCondition` on torsion etale coefficients, and nothing on
the adic pair category. The new modules duplicate no notion.

Dependency (§1(B)) repairs:

- Each of the three dependency node files changes only in `lean`, with a note.
- def-weil-derived-cohomology-sheaves keeps its `mathlib_match` and uses
  `DerivedCategory.homologyFunctor` verbatim.
- For def-coefficient-twists-detailed, the previous record (Q118 `diagonalTwist`) stays
  imported.
- For def-per-support-condition, the module states only the support half. CosuppCon would
  need a Verdier dual on `pbcQbarCategory` (def-trf-dualizing-complex has no Lean record);
  the item does not use it. The torsion etale `SupportCondition` and `CosupportCondition`
  stay publicly imported. This is recorded as an observation, not a fault.

Gates:

- Every theorem is `sorry`. The definitions carry real data. The only choices are ∃!-
  normalized: the rational fibre functor's integral normalization agrees with
  `qbarStageFieldEquiv`'s Shrink normalization.
- Every declaration has a source docstring and `(blueprint: ...)`.
- No pro-etale substitute or discrete Qbar etale sheaf is used.
- `lean.statement` is verbatim the signature in each of the four records.

Change made: this section only.

## Validation

All four delivered modules passed `scompile.py Q151 lem-per-tate-twist-support-condition`
in dependency order, separately in the private overlay and in the server sandbox/library
confirmation checks. The wrapper exited 0 with no errors or warnings. The final per-file
library checks took 14.2 s, 16.0 s, 12.0 s and 24.4 s respectively. No global build was run.
The metadata audit verified exactly four modules with one owning node each, verbatim
signatures, lines at most 100 characters and only `lean` changes in all four node copies.

`deliver2.py Q151 lem-per-tate-twist-support-condition --no-push` exited 0:
`OK (dry run): commit 43f94b51b1 passes the preflight and compiles; nothing pushed`.
This rerun validated the synchronized `PbcSupportCondition` name and all four current
Lean files. The first dry run had found only a transient signature/name mismatch during
that rename; the synchronized rerun repaired all three reported record discrepancies.
