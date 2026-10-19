## Worker report

Recorded an existing statement, with no new Lean module:
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`,
module `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing`,
local source lines 321–373 (the theorem starts at line 346).
The current source was also read using `scompile.py --source` for that module;
the theorem's signature is unchanged. Its ambient binders are `universe u` and
`variable (Λ : Type (u + 1)) [CommRing Λ]` in namespace `AlgebraicGeometry`.
The node's `lean.statement` is the literal source signature, retaining the
source's namespace-relative name and ambient coefficient variable.

Source checked: current blueprint main-20261015,
`sec-smooth-base-change/sk-thm-vanishing/_section.md`, whose statement is the
node's statement. The upstream docstring explicitly identifies this theorem
with `sk-thm-vanishing`. This attachment records a Lean statement, not a claim
that every theorem on which its existing proof rests has been proved.

Hypotheses and conclusion, clause by clause:

- The affine base `S = Spec A`, for a normal domain `A`, is `D.S₀` with
  `D.isAffine_base`, `D.isIntegral_base`, and
  `D.isIntegrallyClosed_stalk : ∀ x, IsIntegrallyClosed (D.S₀.presheaf.stalk x)`.
  Integral-scheme stalks are domains. This is precisely the integral-normal
  predicate of the recorded dependency `IsNormalScheme`: its two clauses are
  integrality and integrally closed domain stalks. For the node's input set
  `D.S₀ = Spec A`. Conversely any bundled affine integral normal base is
  canonically isomorphic to `Spec Γ(D.S₀, ⊤)`; its global-section ring is a
  normal domain. Thus the affine presentation adds or removes no case.
- The algebraically closed fraction field `L` is `D.S₀.functionField` with
  `D.isAlgClosed_functionField`. On `Spec A`, the scheme function field is a
  fraction field of `A` and is canonically isomorphic over `A` to the given
  `L` by uniqueness of fraction fields. Normality on `Spec A` is equivalent
  to integral closedness of `A`; no Noetherian assumption occurs.
- The total space `X` and morphism `f : X → S` are `D.X₀` and `D.f₀`,
  with `D.isAffineHom` and `D.smoothOfRelativeDimension_one` asserting
  `IsAffineHom D.f₀` and `SmoothOfRelativeDimension 1 D.f₀`.
  `X` is affine because an affine morphism to the affine `D.S₀` has affine
  source; the absence of a separate `IsAffine D.X₀` field drops no hypothesis.
  Relative-dimension-one smoothness implies smoothness.
- The extension of algebraically closed fields `K/L` is `D.K` with
  `D.field`, `D.isAlgClosed`, and the unital ring morphism
  `D.i : D.S₀.functionField ⟶ CommRingCat.of D.K`. A ring map out of a
  field is injective and gives exactly the field-extension structure. It
  is not required to be algebraic, finite, or separable.
- The specified geometric generic map `g` is exactly
  `Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)`.
  With the fraction-field identification above this is the map induced by
  `A → L → K`, not an arbitrary geometric point of the base.
- The fibre `Y`, projections `e : Y → Spec K`, `h : Y → X`, and Cartesian
  square are `D.Y₀`, `D.e`, `D.h`, and
  `D.isPullback : IsPullback D.e D.h g D.f₀`.
  This is the flipped orientation of the dependency's square. An
  `IsPullback` supplies its canonical isomorphism with the chosen categorical
  pullback, with both projection equations; a `ChosenCartesianSquare`
  conversely supplies this universal property. No extra geometric constraint
  arises from choosing a Cartesian identification.
- An integer `d` invertible on `S` is represented by the natural modulus
  `D.d := d.natAbs` and `D.isUnit_d : IsUnit (D.d : Γ(D.S₀, ⊤))`.
  The integer is nonzero, since `A` is a nonzero domain, so its absolute
  value is positive. The unit condition on `d` is equivalent to that on
  `|d|` (their ratio is ±1). The generated ideals `dΛ` and `|d|Λ` are equal,
  even for an arbitrary commutative ring `Λ`. Thus this is normalization
  of the same quotient, with negative integers fully covered.
- The arbitrary commutative coefficient ring is the ambient
  `(Λ : Type (u + 1)) [CommRing Λ]`; neither nontriviality nor any finiteness
  or torsion hypothesis is imposed on `Λ`.
- The constant sheaf `Λ/dΛ` on the small étale site of `Y` is
  `Etale.constantModSheaf Λ D.Y₀ D.d`. Its actual definition, read in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`, applies
  `CategoryTheory.constantSheaf` to
  `ModuleCat.of Λ (Λ ⧸ (Ideal.span {(D.d : Λ)} : Ideal Λ))`.
  This is the standard quotient-module construction, not an unknown
  coefficient object or just an abelian-group replacement.
- The integer degree `q ≥ 1` is `(q : ℤ) (hq : 1 ≤ q)`.
  The conclusion is `IsZero (Etale.higherDirectImage Λ D.h q
  (Etale.constantModSheaf Λ D.Y₀ D.d))`, an assertion in the category
  `Sheaf D.X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  The read definition of `higherDirectImage` is the degree-`q` homology
  of the bounded-below right-derived direct image of the sheaf in degree
  zero, exactly `R^q h_*` of the direct-image dependency. This is vanishing
  of the sheaf, not merely vanishing of global sections.

Dependency declarations inspected and used by the existing interface:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  and `AlgebraicGeometry.SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`:
  `AlgebraicGeometry.IsAffineHom` (the `mathlib_match` of
  `pqf-def-affine-morphism`); ordinary `Scheme`, `IsAffine`, and scheme
  morphisms use the conventions dependency, which fixes no new declaration.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`;
  the existing bundle spells out its integrality and normal-stalk clauses.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`, whose
  input is the `ChosenCartesianSquare` of
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`. Its underlying Cartesian
  square is the `IsPullback` in the bundle; the inverse-image comparison
  itself does not occur in this vanishing assertion.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`.
- `Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic`:
  `Submodule.hasQuotient`, `Submodule.Quotient.module`, `Submodule.mkQ`,
  `Submodule.mkQ_surjective`, and `Submodule.ker_mkQ` (the quotient node's
  Mathlib match); the constant coefficient uses this quotient by an ideal.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, with
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` implemented in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`:
  the recorded category conventions `CategoryTheory.Sheaf`,
  `CategoryTheory.constantSheaf`, and module-valued étale sheaves; the
  locally constant/constructible predicates listed in that broad node are
  not hypotheses of this assertion. The six-functor encoding is the
  authorized `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` form.

The bundling module `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum`
was read in full, including the complete structure definition. In particular,
the bundle does not require a section, geometrically connected fibres, or a
connected/nonempty total space. Those assumptions occur only in intermediate
proof lemmas, not in this theorem. Proof dependencies already have recorded
interfaces; this existing theorem is reused without altering its imports.

Edge cases checked: `d = 0` cannot be invertible over a nonzero domain;
`d = 1` and `d = -1` give zero coefficients; all negative `d` are covered by
absolute value; the zero ring `Λ` is permitted; empty `X` and hence empty `Y`
are permitted (relative dimension is pointwise); `K = L` is permitted;
`q = 1` is included and `q = 0` is excluded exactly as in the source.
No assumption says the characteristic of `Λ` equals the characteristic of
`A`, and no such assumption is needed. The universe is arbitrary; as in
all recorded six-functor statements, schemes have universe `u` and coefficient
modules universe `u+1`. Increasing `u` accommodates any given input sizes.

Searches made (2026-10-17):

- `msearch.py ... leansearch` with query “Higher direct images of the constant
  torsion module sheaf along a geometric generic fibre of a smooth affine
  relative curve vanish in positive degree”: eight unrelated hits on
  structure-sheaf constants, constant-sheaf membership, affine limits and
  smoothness; no Mathlib theorem match.
- `msearch.py ... leanfinder` with query “Higher direct images of constant
  module sheaves vanish along the geometric generic fibre of an affine
  smooth relative curve over a normal domain with algebraically closed
  fraction field”: eight unrelated affine-limit, normalization and
  smoothness hits; no Mathlib theorem match.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Etale.higherDirectImage, AlgebraicGeometry.Etale.constantModSheaf`:
  zero hits (upstream identifier not known to Mathlib's Loogle index).
- `msearch.py ... grep` with query
  `higherDirectImage.*constant|isZero.*higherDirectImage`: zero Mathlib hits.
  Direct `rg` with the same pattern in pinned Mathlib also had no hits.
- `rg` for `sk-thm-vanishing|isZero_higherDirectImage_constantSheaf|universalCurveTest`
  in `WeilConjectures` and `lean/Sheaf`: found this upstream theorem,
  its consumer in `SmoothBaseChange.Induction`, and the side theorem
  `isZero_universalCurveTest_higherDirectImage`. The latter has cyclic
  abelian coefficients only and is not the arbitrary-Λ statement.
- `rg` for `isZero_higherDirectImage_constantSheaf` in
  `dag/lean_names_upstream.json`: no hit; direct source inspection and
  current-server source retrieval establish the declaration instead.

Only the item's `lean` field is changed. No node correction, new definition,
dependency repair, or statement dispute is required. The existing theorem's
proof is retained unchanged; no new theorem is proved in this delivery.

## Second reading by Q115

I read the node statement against the source place
`literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-thm-vanishing/_section.md`
and its proof file. The source introduces the following data and conclusion, in order.

- `X → S`, with `f` affine and smooth of relative dimension one, and `X` affine. The
  existing Lean declaration renders these as `D.f₀`, `[IsAffineHom D.f₀]`, and
  `[SmoothOfRelativeDimension 1 D.f₀]`; `D.S₀` is affine, so the source's `X`-affineness
  follows from affine `f` over an affine base.
- `S = Spec A`, where `A` is a normal domain with algebraically closed fraction field `L`.
  The `CurveTestDatum` fields `[IsAffine D.isAffine_base]`, `[IsIntegral D.isIntegral_base]`,
  `D.isIntegrallyClosed_stalk`, and `[IsAlgClosed D.S₀.functionField]` are exactly the
  bundled affine integral normal base and its algebraically closed function field. An
  affine integral scheme is `Spec` of its global-section domain, so this is a presentation
  change, not an added or dropped hypothesis.
- `K/L` is an extension of algebraically closed fields, with the specified geometric generic
  point `g`. These are `D.K`, `[Field D.K]`, `[IsAlgClosed D.K]`, `D.i`, and the map
  `Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)` in `D.isPullback`.
- The displayed Cartesian fibre square and its projections `Y`, `h`, and `e` are exactly
  `D.Y₀`, `D.h`, `D.e`, and `D.isPullback` (with the same orientation).
- The integer `d` is invertible on `S`. The source declaration stores `D.d : ℕ`; for the
  node's integer use, `D.d = d.natAbs`. The ideals generated by `d` and `|d|` agree, and
  invertibility excludes `d = 0`, so negative, zero, and positive integer cases are covered
  without changing the coefficient sheaf.
- `Λ` is an arbitrary commutative ring, rendered by the ambient
  `(Λ : Type (u + 1)) [CommRing Λ]`. The constant coefficient sheaf is
  `Etale.constantModSheaf Λ D.Y₀ D.d`, and the conclusion for every integer `q ≥ 1` is
  `IsZero (Etale.higherDirectImage Λ D.h q (...))`, in the sheaf category of `Λ`-modules.

The only representation differences are the bundled `CurveTestDatum` versus the displayed
loose diagram and `natAbs d` versus a signed integer `d`; neither changes the mathematical
cases or conclusion. I found no missing or stronger hypothesis, no quantifier reordering, and
no extra characteristic, finiteness, Noetherian, connectedness, section, or separability
assumption. The empty scheme/fibre and zero coefficient ring remain allowed; `d = 0` is
excluded exactly by invertibility; `d = ±1` gives the zero quotient; `q = 1` is included and
`q = 0` is excluded; `K = L` is allowed; and the universe is arbitrary with coefficients in
`Type (u + 1)`.

I inspected every recorded statement dependency: Mathlib smoothness and affine-morphism
notions, the normal-scheme and chosen-Cartesian-square declarations, constant sheaf and
quotient-module constructions, the direct-image declaration, and the étale-sheaf category
conventions. The source declaration and its full `CurveTestDatum` structure were read with
`scompile.py --source`. The Lean/Mathlib/project searches recorded in `searches.jsonl` were
repeated with `leansearch`, `leanfinder`, `loogle`, and `rg`; they found no competing theorem
for this higher-direct-image vanishing. A required `#check` probe through `scompile.py` passed
for `AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`.

No statement correction, dependency repair, new definition, or Lean module was needed. The
node copy now records the exact existing declaration and its source module; the theorem itself
and the worker's report were otherwise left unchanged.
