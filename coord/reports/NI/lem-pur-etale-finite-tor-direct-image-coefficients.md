## Worker report

The module `Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients` states
`AlgebraicGeometry.Etale.finiteTor_directImage_coefficients`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The original statement and all original dependencies and proof steps are unchanged.

Hypothesis and clause correspondence:

- Positive characteristic: `(p l : ℕ) (_hp : 0 < p)`, `[Field k]`, `[CharP k p]`;
  the coefficient prime is `[Fact l.Prime]`, and `_hlp : l ≠ p`.
  Primality of p follows from the field characteristic and positivity, so it is not
  an additional assumption. Neither separable closedness nor finite absolute cd(k)
  is assumed.
- The finite extension is `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The actual integer ring, chosen uniformizer and
  quotient are the recorded `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing l E n`.
  Its definition is the quotient by `(Ideal.span {uniformizer}) ^ n`, the desired
  uniformizer-power ideal. `(n : ℕ) (hn : 1 ≤ n)` retains the positive level.
  The explicit `@isBoundedConstructible` applications supply the already proved
  `Padic.finite_coefficientExtensionRing l E n hn`; finiteness is not assumed anew.
- The k-schemes are `U V : Scheme.{u}` with `.Over (Spec (.of k))` structures.
  Each structure map has `[LocallyOfFiniteType]` and `[QuasiCompact]`, exactly finite
  type. The morphism `(h : U ⟶ V) [h.IsOver (Spec (.of k))]` is a k-morphism.
  There is no separatedness hypothesis.
- All complexes use `Etale.DerivedCategoryModule`, namely the unbounded derived
  category of `Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)`.
  Universes are explicit: scheme universe u, coefficient and module universe u+1,
  as required by the recorded ordinary-etale APIs. Every finite ring and finite
  extension can be represented at this size; the statement imposes no equality
  between site object and morphism universes.
- `∃ c : ℕ` is one nonnegative bound depending on the morphism and coefficients,
  outside all quantifiers over M, K, intervals and B. The first conjunct says
  `IsZero (H^(q:ℤ) (R(lowerStar ...) h (singleFunctor 0 M)))` for every module sheaf
  M and natural q with `c < q`. Since c is nonnegative, these q are exactly all
  integer degrees strictly above c.
- The second conjunct quantifies over K and integer a,b with `a ≤ b`, bounded
  constructibility and `DerivedCategory.hasTorAmplitudeIn A U a b K`. This is exactly
  K in D^b_ctf with the given interval. The conclusion gives bounded constructibility
  of the actual `R(lowerStar ...) h` object on V and its Tor amplitude `[a,b+c]`.
  A specific finite Tor interval already gives the finite-Tor part of D^b_ctf;
  no alternate constructibility or finite-Tor predicate is introduced.
- Every unital finite commutative A-algebra is written as
  `(B : Type (u + 1)) [CommRing B] [Finite B] (φ : A →+* B)`.
  A unital ring homomorphism into a commutative ring is precisely this algebra data;
  neither flatness, injectivity, nonzero B nor étaleness of the algebra is required.
- The last conjunct is scalar preservation for every J on either U or V, encoded by
  `(W : Scheme.{u}), (W = U ∨ W = V) → ...`. It quantifies over the input Tor interval
  `[r,s]`, with `r ≤ s`, and gives bounded constructibility over B and exactly
  `hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J)`. This is the actual
  B-linear left-derived change of rings, not the underlying A-linear tensor alone.
- The scalar comparison is `IsIso ((scalarMate φ h).app K)` in D(V_et,B).
  `scalarMate` is the published geometric-adjunction mate of `scalarPullbackIso`:
  its transpose is scalar/pullback comparison followed by scalar extension of the
  A-geometric counit. There is no arbitrary choice of a comparison map here.
- The following equality gives the required normalization. Its left side is
  `derivedRestrictScalars.map (scalarMate.app K)` followed by
  `scalarRestrictionDirectImageMap.app (scalarExtension.obj K)`. Its right side is
  `scalarTensorIso.hom` followed by the exact recorded
  `rightDerivedLowerStarProjectionMap` at K and `scalarCoefficient φ V = B_V[0]`,
  followed by direct image of the coefficient pullback identification and inverse
  scalar/tensor identification on U. Thus it identifies the specified morphisms,
  including their source and target identifications, rather than asserting only
  that two objects happen to be isomorphic.

Recorded statement dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting all the constructions above
  from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-weil-pbc-scheme-conventions` is a convention-only record. Its Mathlib Scheme,
  finite type and over-base meanings are used directly, with no private replacement.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`; reexported by bounded constructible complexes.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` (finite-value
  constructible cohomology and a finite vanishing interval).
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` reexports the bounded predicate
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. Only this bounded predicate
  is needed; it tests every degree-zero module sheaf, not merely constant sheaves.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`:
  `AlgebraicGeometry.Etale.scalarRestrictionDirectImageMap`.
  Its geometric mate definition and reexported bounded-below restriction isomorphisms
  were read, together with the original
  `WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons`.
- `Sheaf.Paper.PurEtaleScalarMateProjection`:
  `scalarMate`, `scalarPullbackIso`, and `scalarMate_restrict_eq_projection`.
  Its reexported `Sheaf.Paper.EtaleDerivedScalarTensor` supplies `scalarExtension`,
  `scalarTensorIso`, `scalarCoefficient` and the exact tensor normalization.

All available recorded proof-dependency modules are imported without `public`,
except where already reexported by statement dependencies. This includes the
uniform torsion direct-image bound, finite-type constructibility, Grothendieck
abelian and left-exactness interfaces, truncation spectral sequence, finite-constant
projection formula, residue Tor test, derived change of rings, Noetherianity,
finite-Tor etale/pro-etale comparison, scalar preservation, coefficient adjunction,
localized scalar systems and bounded-below full faithfulness. The declaration
docstring includes the eight source proof steps and the nodes used at each step.
The imported restriction module already reexports Mathlib scalar restriction;
finite coefficient arithmetic is reexported by the coefficient module.

Edge cases checked mathematically before writing: K=0 and J=0; empty U or V; identity
h with c=0; arbitrary nonseparated finite-type h; n=1; finite residue coefficient
B, nonflat B=A/(t), a nonflat finite algebra with nilpotents, B=A and B=0; a=b;
negative lower endpoint a; fields with infinite absolute cohomological dimension.
All are admitted. For B=0 the output is the zero derived category and the mate is
invertible. The scalar clause retains interval endpoints rather than adding c.
The direct-image bound ranges over all module sheaves, not just constructible ones.
There are no disputed statements or source corrections.

Searches performed (actual wrapper results):

1. msearch leanfinder: "For finite type schemes over a field derived etale direct
   image preserves bounded constructible finite Tor amplitude complexes and commutes
   with finite coefficient extension". Eight hits on elementary etale morphism
   properties, including `AlgebraicGeometry.IsEtale.of_comp` and `Algebra.Etale.comp`;
   no statement matching this theorem.
2. msearch leansearch: "Derived etale direct image preserves bounded constructible
   complexes with finite Tor amplitude over a field and commutes with finite
   coefficient algebra extension". Eight hits on algebraic etaleness and scheme
   etale objects, including `Algebra.Etale.baseChange`; no match.
3. msearch loogle: `AlgebraicGeometry.Etale.DerivedCategoryModule, CategoryTheory.IsIso`.
   Zero hits because the project-specific name is unknown to this Mathlib service;
   this invalid query is not evidence of absence. Repeated with valid query
   `CategoryTheory.IsIso, CategoryTheory.Functor`: 12 generic results such as
   `Functor.map_isIso`, `Functor.map_inv` and naturality of inverse components;
   none states this etale finite-Tor theorem.
4. msearch grep:
   `(finiteTor|hasTorAmplitude).*(DirectImage|LowerStar|direct_image)|finite_tor_direct_image`.
   Zero Mathlib hits.
5. rg of both live source roots `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `finite_tor_direct_image`, `finiteTor.*DirectImage`, `finiteTor.*LowerStar`.
   Only upstream `finiteTorRightDerivedLowerStar` in
   `ProEtale/FiniteCoefficient/Derived/LocalizationFiniteTor.lean` occurs: this is a
   pro-etale localization functor, not the ordinary-etale combined theorem here.
   Read the ordinary scalar-mate and scalar/tensor modules instead of duplicating
   their existing constructions.

Source reading: the current blueprint reduction-exceptional and scalar-extension
proof files named by this node, and Stacks etale-cohomology.tex
`definition-cd-f` / `lemma-finite-cd` (0F0Z / 0F10): clause (1) is relative and makes
no absolute cohomological-dimension assumption on the field.

Validation: scompile.py compiled the delivered file both as a sandbox module (6.3 s)
and at its final library module path (5.3 s), with no errors or warnings.
An initial compile timed out due to unfolding quotient-ring/derived-functor data;
matching the existing CommRing-to-Ring instance path and marking chosen derived
functors locally irreducible resolved that without any statement change or increased
limit. The declaration uses explicit universes and `set_option autoImplicit false`.
No proof was filled and no library or launcher file was edited.

## Second reading by NI

I reread the node and final module after compilation; this is a second pass by the
same dispatcher worker, not a claim of independent review (the task prohibits
starting other agents, and the maintainer performs the independent review).
The first conjunct has the bound outside M,K,B; the second has both bounded
constructibility and the full Tor interval, with the correct b+c upper endpoint.
The scalar clause is quantified independently of K and preserves the original r,s
on each scheme. The B-linear comparison is the actual counit mate from the
recorded helper, and its equality includes all canonical scalar/tensor and
coefficient-pullback identifications; no weaker existential isomorphism replaces it.
I checked every hypothesis against the node: p>0, ell prime distinct from p,
finite E/Q_ell, positive quotient level, finite-type k-schemes and k-linearity,
finite commutative unital B, and no flatness, separatedness or absolute cd(k)
hypothesis. No statement mismatch was found; no node correction was needed.
