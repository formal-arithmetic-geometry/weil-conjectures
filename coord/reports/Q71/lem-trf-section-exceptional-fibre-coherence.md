## Worker report

The delivery states lem-trf-section-exceptional-fibre-coherence in
`Sheaf.Paper.SectionExceptionalFibreCoherence`. All five theorems end in `sorry`.
Definitions have actual data. No statement or DAG dependency is changed.

The geometric records only package the diagrams already quantified over in the node:
`ExceptionalSectionPair B d` records a structural map, its closed section and section
identity, Noetherian source and base, compactifiability, separatedness and smooth pure
relative dimension d. `ExceptionalSectionFamily S d` records that pair over the actual
affine line and its two Cartesian fibre pairs. The inherited smoothness, closed-section,
Noetherianity, separatedness and compactifiability of the fibres impose no additional
restriction: they follow by base change from the ambient pair and finite type over a
Noetherian base. `ExceptionalSectionChange` records a Cartesian square and compatible
sections. `ExceptionalFamilyBaseChange` records the induced Cartesian fibre cube;
`point_comm` and `fibre_comm` are its commutativity witnesses, not cohomological hypotheses.
`ExceptionalSectionEtaleMap` and `ExceptionalFamilyEtaleMap` record the specified separated
etale finite-type maps, Cartesian centres and induced fibre maps. A chosen pullback is
not imposed: the maps apply to every Cartesian representative of the diagram.
These records contain no derived objects, comparison maps or coherence assumptions.
They are helpers belonging to this node's diagrams, rather than new independent notions.

Hypothesis and clause correspondence:

- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]` in every theorem.
  The category is the existing `DerivedCategoryModule A T`, the ordinary unbounded
  derived category of `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)`.
  It has no boundedness, constructibility, completion, pro-etale or orientation assumption.
- N >= 1 and NA = 0: `(N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)` in every theorem.
  Invertibility on S is exactly `∀ s : S, IsUnit (N : S.presheaf.stalk s)`.
  In the structural transitivity clause it is the corresponding predicate on B.
- Noetherian schemes, smooth separated compactifiable q of pure dimension d >= 0,
  and a closed section: the fields of `ExceptionalSectionPair`, with `d : ℕ`.
  The affine line is `AffineSpace (ULift.{u} (Fin 1)) S`, with its existing projection.
  `exceptionalFamilyPoint S false/true` are exactly the existing zero/one sections.
  `restriction t` records the Cartesian fibre square and section compatibility.
- Omega_b = b^times A: existing `dualizingComplex (ModuleCat A) b`. Its right adjoint
  and adjunction are the existing `rightDerivedUpperShriek` and
  `rightDerivedUpperShriekAdjunction`, for the chosen compact-support functor.
- C, F, H are the existing `sectionInvariant A map sect` of the one fibre, ambient
  family, and zero fibre. The actual signature of this upstream declaration is the
  unbounded ordinary-etale section pullback, even though its docstring also discusses
  the purity application. No pro-etale section-invariant node is substituted for it.
- The preliminary twist notation has the existing realization
  `Scheme.finiteEtaleTateSheaf A N T hA (d : ℤ)` in the imported finite-twist modules.
  Degree zero is its constant-unit convention. Twists occur in none of this node's
  comparison formulas, so no second twist definition or abstract `HasTateTwist` is added.
- Theta and eta: `P.fibreMap A true` and `P.fibreMap A false` are defined by
  `sectionExceptionalComparison A (P.restriction t)`. That construction uses the actual
  upstream `dualizingComplexBaseChangeMap A square`, i.e. the counit mate of inverse
  compact-support exchange at the coefficient unit, and then pulls it back by the
  section. `sectionCoherencePullbackIso` inserts both inverse-image compositors.
- Arbitrary Noetherian v and the primed diagrams: `v : S' ⟶ S` and
  `e : ExceptionalFamilyBaseChange P P' v`. No smoothness, flatness, etaleness or
  compactifiability is required of v. The three b maps are the actual
  `sectionExceptionalComparison` for `e.ambient`, `e.fibre true`, `e.fibre false`.
- Their invertibility and both fibre identities are exactly the conjuncts of
  `sectionExceptional_fibre_coherence`. In Lean composition order its equation is
  compositor >> i_t'^*(b_F) >> theta_t' = v^*(theta_t) >> b_t.
  The Bool quantifier covers precisely t = 0 and t = 1. The original fibre maps and
  the primed fibre maps are also asserted invertible.
- Successive changes of base: `sectionExceptional_comparison_comp` quantifies over
  the three structural pairs, v, w, their Cartesian changes, and the outer rectangle.
  `hUpper` identifies the outer upper map with the composite, as required by that
  diagram. The equation is b_vw = compositor >> w^*(b_v) >> b_w, for the actual maps.
  Applying it to the ambient pair or either fibre gives all the node's instances.
- Etale locality: `sectionStructuralLocalityIso` takes the uniquely characterized
  isomorphism of `existsUnique_etaleAmbientAdjointLocalityIso`, with the existing
  compact-support adjunctions, and evaluates it at the unit. The theorem uniquely
  specifies it simultaneously by every graph-normalized composite counit. Thus
  `Classical.choose` here takes data determined by uniqueness, not an arbitrary
  isomorphism. The exact/left-derived inverse-image comparison is inserted explicitly.
  `sectionExceptionalLocalityIso` then pulls this actual isomorphism back by the section.
- Both etale-family equations are `sectionExceptional_etale_fibre_coherence`, again
  at true and false. The b maps are isomorphisms by their construction as `Iso`.
  The maps are never quantified over as arbitrary arrows with unspecified normalization.
- Unique normalized kappas: each explicit `κ` is an isomorphism to the actual a^*C;
  `IsNormalized` says its one-fibre restriction, followed by the canonical section/unit
  compositor, is theta. The conjunction `hκ` supplies normalization and uniqueness
  among all normalized isomorphisms; the corresponding hκ' or hκ₁ does the same.
- Delta: `ExceptionalSectionFamily.specialization` is exactly eta after the inverse
  of the zero restriction of kappa, with the canonical identification i_0^*a^*C = C.
- The base-change kappa and delta equations are the two conjuncts of
  `sectionExceptional_normalized_baseChange`. The kappa equation is multiplied on the
  source by b_F. Since b_F is invertible by the first theorem, this is equivalent to
  the node's formula with b_F inverse. The a/v square compositor is written explicitly.
- The etale kappa and delta equations are the two conjuncts of
  `sectionExceptional_normalized_etale`. Its first equation is likewise equivalent
  to the node's formula after composing with the inverse ambient locality isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, scheme morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; Noetherian schemes use the
  established `IsNoetherian` convention, not a new ring predicate.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: the actual unbounded
  `rightDerivedLowerShriekOfCompactification` and chosen `rightDerivedLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` and `.UpperShriek`:
  the exceptional-adjoint theorem and `rightDerivedUpperShriekAdjunction`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: the recorded exact
  module inverse-image statement; the six-functor encoding uses its established
  `upperStar`, `leftDerivedFunctor`, and `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `Scheme.etaleFiniteTwistPullback`
  and the existing finite Tate sheaf construction (only the node's preliminary notation).
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.map`, projection;
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`: zero and one sections and
  their projection identities. The affine-space dependency is a mathlib leaf, used
  through its recorded `mathlib_match`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  `.Proper`: `IsSeparated`, `IsProper`; `.ClosedImmersion`: `IsClosedImmersion`;
  `.Etale`: `Etale`; `.FiniteType` / `.QuasiCompact`: finite-type conditions.
- `WeilConjectures.Compactification.Defs`: `HasCompactification`, `Compactification`;
  the compactifiable dependency's record expressly delegates its defining clause to
  these declarations, so its additional over-field existence theorem is not assumed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: fibre products;
  `IsPullback` is used so that every Cartesian representative is admitted.
- `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`: the recorded
  `smooth_exceptional_base_change`, `smoothExceptionalBaseChangeMap`,
  `smoothDualizingBaseChangeMap`. The arbitrary-square version used here is the existing
  upstream `dualizingComplexBaseChangeMap` from `.Derived.UpperShriekCanonicalMaps`.
  Both are defined as the same inverse-exchange counit mate and coefficient-unit map;
  the former is its chosen-pullback specialization.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `existsUnique_etaleAmbientAdjointLocalityIso`, its full counit characterization,
  `etaleAmbientLeftComparison`; this interface is directly used, not repaired or copied.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions`: `sectionInvariant`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence`:
  `leftDerivedUpperStarCompSectionIso`; `.UpperLowerStar`: `leftDerivedUpperStarComp`.
- Proof-only imports include the recorded unbounded compact-support comparison,
  finite twist, pullback-composition monoidality, and etale-shriek base-change modules.
  The remaining proof prerequisites are Mathlib declarations or available transitively
  from these imports. No unstated proof prerequisite is assumed as a hypothesis.

Edge cases checked: d = 0; the empty base and empty total schemes; N = 1 and A the
zero ring; identity base change; identity etale-family map; successive changes of base;
nonflat v; and different Cartesian representatives of a fibre. No positive dimension,
nonzero coefficient, nonempty scheme, field, or additional restriction on v occurs.
All scheme universes are u and the coefficient universe is u+1, the established ordinary
etale module-category convention. Every universe and variable is explicitly bound.

Searches actually run:

- msearch leansearch, `The counit defined exceptional base change for smooth section families
  commutes with the zero and one fibres and etale locality`: eight hits about condensed
  locally constant sheaf counits, smooth/etale base-change stability and vector-bundle
  zero sections; none states the section-family coherence.
- msearch leanfinder, `Counit defined exceptional base change coherence for smooth section
  families zero and unit fibre etale locality`: eight hits in standard smooth algebra,
  etale presentations and Kaehler differentials; none states this coherence.
- msearch loogle, `CategoryTheory.mateEquiv_vcomp`: the exact generic mate-pasting lemma,
  not a section-family statement.
- msearch grep, `exceptional.*[Bb]ase[Cc]hange|[Ss]ection.*[Ff]ibre`: eight irrelevant
  Mathlib text hits, no exceptional section-family assertion.
- rg in `lean/Sheaf` and `lean/WeilConjectures`, for section/fibre/coherence and the item
  ID: no item declaration. Read the upstream Smooth/Deformation and FamilyObject
  modules: their abstract/nonempty fibre isomorphisms and normalization statements do
  not give this node's actual counit-defined maps and etale/base-change squares.
- The upstream conventions already give `sectionInvariant`; it is reused. The actual
  counit-defined structural comparison already exists; it is reused. The uniquely
  counit-normalized etale locality already exists; it is reused. No existing notion
  has been redefined.

Validation: scompile.py compiled both the sandbox module and the delivery module with
no warnings and no errors. The prescribed deliver2.py dry run reported OK: preflight
and compilation passed (dry-run commit ee3bc18be3a). All theorem proofs are `sorry`; all definitions have real data.
No STATEMENT-DISPUTED finding or statement correction was needed.

## Second reading by Q71

Self-audit, not a claim of an independent reader: I reread the node and all five theorem
signatures against the clause correspondence above, including directions of the fibre
maps, inverse-image compositors, unique normalization, and delta direction C to H.
I corrected the reserved field name `section` to `sect` and used the actual affine
projection morphism rather than its `CanonicallyOver` structure. The final compile is
clean. The dispatcher prohibits starting other agents and assigns independent review to
the maintainer, who must supply the independent reading of this delivery.
