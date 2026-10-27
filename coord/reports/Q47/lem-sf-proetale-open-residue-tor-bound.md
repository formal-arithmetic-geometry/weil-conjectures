## Worker report

The module `Sheaf.Paper.ProEtaleOpenResidueTorBound` states
`AlgebraicGeometry.ProEtale.proEtale_open_residue_tor_bound`, with `sorry` as its
only postponed proof. The accepted stage-1 statement, proof, and dependencies are
preserved. The current standing stage-2 brief explicitly authorizes recording a
reviewed stage-1 split; the inherited stage-1 refusal does not apply to this delivery.
No repair note is present, and the live node has no previous Lean record.

The definitions in the module are only notation-free packaging of this node's
conclusion and specified maps, not replacement definitions of tensor, Tor amplitude,
constructibility, site comparison, or direct image. They have actual data:
`openResidueModule` is the quotient module, `openResidueDirectImageMate` is the
published mate composed with its five standard D+/D compatibility morphisms,
`openResidueProjectionSquare` is the equality of the two specified routes, and
`openResidueFixedTorBoundAssertion` spells out the assertion for a supplied
coefficient module. The theorem supplies precisely the actual residue module.
All five declarations are listed in `lean.declarations`.

Hypotheses and objects, clause by clause:

- The prime ell is `(l : ℕ) [Fact l.Prime]`; the finite extension E/Q_l is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The valuation ring, chosen uniformizer, and A_n are the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing`. Positive level is `(n : ℕ) (hn : 1 ≤ n)`.
  `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness, rather
  than adding it as a hypothesis; `Finite.of_equiv ... Equiv.ulift.symm` passes
  this to the common larger coefficient universe.
- The base field and invertibility are `(k : Type u) [Field k] [Invertible (l : k)]`.
  `[X.Over (Spec (.of k))]` supplies the structure morphism.
  `[LocallyOfFiniteType ...] [QuasiCompact ...]` says finite type, and
  `[IsSeparated ...]` says separated, with no finite-field restriction.
- `(i : Z ⟶ X) [IsClosedImmersion i]`, `(j : U ⟶ X) [IsOpenImmersion j]`, and
  `_hij : IsCompl (Set.range i.base) (Set.range j.base)` express exactly the
  complementary immersions. The closed complement remains in the statement
  even though the open-image assertion does not otherwise use its structure.
- `openResidueModule A r` is `(ULift A) / Ideal.span {ULift.up r}` as a module
  over `ULift A`, and the theorem sets `r` to the quotient image of the
  recorded uniformizer. This is kappa=A/(varpi), with its actual quotient
  scalar action, not an arbitrary residue object or perfect replacement.
- The small sites are `T.smallEtaleTopology` and `Scheme.ProEt.topology T`.
  Scheme object universe is u, site object universe u+1, and site morphism
  universe u; no equality between these universes is imposed. Modules have
  values in `ModuleCat.{u+1} (ULift.{u+1,u} A_n)`, the published common size.
  Integral categories mentioned as background in the node are imported via
  `Sheaf.Paper.SfIntegralConstructible`; this finite-level assertion has no
  integral object or integral-stage conclusion.
- In `openResidueFixedTorBoundAssertion`, `N : ℕ` is exactly the nonnegative
  dimension bound. The following universally quantified `M` ranges over
  *all* etale module sheaves; for every `q : ℕ` with `N < q` it requires
  `IsZero (homologyFunctor ... (q : ℤ) ... (Rj_* (singleFunctor ... 0 M)))`.
  These are precisely the higher module direct images, not just the
  constructible sheaves or underlying abelian direct images.
- `a b : ℤ` and `a ≤ b` give the requested interval. `G` ranges over the
  unbounded pro-etale derived category, with the recorded
  `ProEtale.DerivedCategory.boundedConstructible` and
  `ProEtale.DerivedCategory.torAmplitudeIn ... a b G` as hypotheses. The
  latter is the existing universal test against *every* pro-etale module
  sheaf placed in degree zero, not a residue-only test or etale-origin test.
- Every chosen origin is `F : DerivedCategory.Plus (...)`, with the recorded
  `Etale.DerivedCategory.isBoundedConstructible ... F.obj` and the actual
  isomorphism `e : comparisonUpperStar.mapDerivedCategory.obj F.obj ≅ G`.
  Boundedness implies membership in D+, so this packaging excludes no bounded
  origin; the extra D+ proof is proposition-valued and proof irrelevant.

Conclusions, in the order of the predicate's conjuncts:

1. `IsIso ((Etale.finiteConstantProjectionMap A j F.obj).app M₀)` is exactly
   the canonical etale map displayed by the node. Its source is
   `Rj_*F ⊗^L kappa_X`, target `Rj_*(F ⊗^L kappa_U)`.
   The recorded definition uses the adjunction projection followed by the
   canonical inverse-image identification of constant coefficients.
2. `∀ q : ℤ, (q < a ∨ b + (N : ℤ) < q) → IsZero (...)` states cohomology
   of this precise target vanishes outside `[a,b+N]`, including both endpoints.
3. `Etale.DerivedCategory.isBoundedConstructible ... (Rj_et*F)` records the
   intermediate bounded constructibility used by the residue criterion.
4. `ProEtale.DerivedCategory.boundedConstructible ... (Rj_*G)` is the bounded
   constructibility conclusion in the fixed-coefficient presentation.
5. `ProEtale.DerivedCategory.torAmplitudeIn ... a (b+N) (Rj_*G)` is the final
   all-module Tor estimate for the actual ordinary pro-etale direct image.
6. `∃ hL, IsIso (openResidueDirectImageMate ... F) ∧ IsIso (... ⟨_,hL⟩) ∧
   openResidueProjectionSquare ... hL` supplies the bounded-below witness for
   `L=F ⊗^L j^*kappa_X`, invertibility of the specified qcqs mates at F and L,
   and equality of the two canonical projection routes. The first route is
   `nu_X^*(pi_et)` followed by `b_L`, then `Rj_*(comparisonOpenTensorIso.hom)`.
   The second is the canonical monoidal comparison, then `b_F tensor 1`, then
   the pro-etale adjunction projection. Together with the constant inverse-image
   identification used by `finiteConstantProjectionMap`, this identifies the
   pullback of the target in (1) with `Rj_*G ⊗^L kappa_X`. The chosen origin
   isomorphism e transports `nu_U^*F` to G through the actual direct-image and
   tensor functors; no unspecified comparison is postulated.
7. For every other bounded constructible origin `(F₁,e₁)` of the same G,
   `∃! v : F.obj ≅ F₁.obj, nu_U^*(v.hom) ≫ e₁.hom = e.hom` gives the unique
   compatible comparison. The maps in (1) and (6) are components/composites of
   the published natural transformations. Their naturality applies to this
   lift v; uniqueness makes the lifts compose for three origins, so all
   transported maps are independent of the origin. For morphisms between G
   and another G, full faithfulness lifts the morphism between origins and
   the same naturality squares apply. This uses actual functorial maps, not
   arbitrary chosen isomorphisms.

The fixed-module presentation is the published one, not a weaker test notion.
`AlgebraicGeometry.ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn`
in `Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport` identifies the
Tor predicate with `Scheme.HasProEtaleTorAmplitude` after the canonical exact
intrinsic realization, for every finite ring. The realization is an exact
module-category equivalence and transports ordinary tensor, degree-zero test
objects and cohomology; thus it tests all intrinsic module sheaves as well.
`Scheme.finiteRing_constructibleDerived_origin` identifies this finite-ring
bounded-constructible predicate with intrinsic bounded constructibility. The
ordinary direct image is the fixed-ring presentation of the same module direct
image: both are the right adjoint of the corresponding exact inverse image.
No completion or different tensor is used.

Dependency declarations read and used (imports are explicit):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the actual coefficient data
  publicly imported from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  its named Mathlib properties are `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsClosedImmersion`, `IsOpenImmersion`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its actual derived restriction
  `Etale.rightDerivedLowerStarPlus` is in the published
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`
  and its public existing pro-etale `DerivedCategory.torAmplitudeIn` and
  `DerivedCategory.boundedConstructible` interfaces.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, `Scheme.proEtaleSiteComparisonModules`;
  their fixed-module inverse image is `ProEtale.comparisonUpperStar`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor` (ordinary K-flat total tensor).
- `Sheaf.Paper.SfDerivedDirectImage`: `WeilConjectures.SfIntegralDirectImage`,
  `sfFiniteDerivedDirectImage`; the finite-level intrinsic operation is the
  published `Scheme.proEtaleConstantDerivedDirectImage`, whose fixed-module
  presentation here is `(ProEtale.lowerStar ... j).rightDerivedFunctor`.

All stated proof-dependency modules are also imported. These include
`ExtensionIntegersDvr`, `ComparisonTorInterval`, `EtaleTorAmplitude`,
`FiniteConstantProjectionFormula`, `Etale.Derived.LowerStarProjection`,
`EtaleModuleSheavesGrothendieckAbelian`, `TruncationHypercohomology`,
`OpenImmersionHigherDirectImages`, `ConstructibleSheaf.KernelCokernel`,
`ResidueTorAmplitudeTest`, `FixedComparisonDirectImageMate`,
`FiniteRingConstructibleDerivedOrigin`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`, `ComparisonPullbackExact`,
`ProjectionComparisonEtaleProEtale`, and `CompactSupportComparisonUnit`.
Mathlib proof leaves are imported through `Algebra.Module.FinitePresentation`,
`Topology.Algebra.Valued.LocallyCompact`, `AlgebraicGeometry.Noetherian` and
`AlgebraicGeometry.Morphisms.QuasiCompact`. There is no import-cycle omission.
The theorem docstring gives all seven accepted proof steps and their node names.

Edge cases checked against the statement and source:

- n=1 is permitted; the image of varpi is zero, so the residue quotient is A.
- N=0 is permitted and gives `[a,b]`; `a=b` is permitted, and a,b can be negative.
- G=0, U empty, Z empty, and X empty are included. No nonempty hypothesis occurs.
- For n>1, kappa can have infinite projective dimension over A. No projective,
  perfect, flat or finite-Tor assumption on kappa is present.
- k is arbitrary, with ell invertible, and may be infinite or nonclosed. No
  finite-field/global cohomological-dimension assumption replaces the supplied N.
- The bound quantifies all etale module sheaves, and final Tor amplitude quantifies
  all pro-etale module sheaves, including those without etale origin.
- The theorem never assumes `F tensor kappa` bounded below: it concludes the needed
  witness hL. A bounded constructible F itself has a D+ representative automatically.

Searches (msearch.py, Q47 and this item; repeated during the resumed stage-2 work):

- leanfinder, `Open immersion direct image residue projection formula pro etale Tor
  amplitude bound`: 8 results about scheme etaleness, residue-field maps and
  polynomial factorization; none state this theorem.
- loogle, `CategoryTheory.IsIso, CategoryTheory.Sheaf`: 12 results about sheafification
  and localization; none state residue projection or an open-image Tor bound.
- Mathlib grep, `residue.*[Pp]rojection|[Pp]rojection.*residue|proetale_open_residue`:
  0 hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the same pattern and `openResidue`:
  only unrelated residue projection constructions and affine residue points; no
  existing declaration of this node. Exact blueprint-id search in
  `lean/WeilConjectures` has no hits. The existing general projection theorem,
  Tor comparison, mate and projection comparison are reused, not restated.

No new nodes, dependency repairs, statement correction, or statement dispute.
Only the item's `lean` field is changed. Initial drafting timed out because the
large assertion forced the kernel to unfold concrete lifted quotient scalar data.
Generalizing the proposition's coefficient-module argument, then instantiating it
with the actual quotient in the theorem, fixes this without changing the mathematics.
The final scompile run checks the sandbox and named module separately, both clean
in approximately 6 seconds each, under the standard 60-second limit. All universes
and variables are explicitly bound (`set_option autoImplicit false`).

## Second reading by Q47

No independent worker reading is claimed. This dispatcher assignment forbids
starting other agents; the maintainer's independent delivery review is the second
reading under the current direct-delivery rule. The worker re-read the node,
source proof and final module, including the explicit residue module, all-module
quantifiers, canonical comparison square and arbitrary-origin comparison.
