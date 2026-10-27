## Worker report

The module Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow states
AlgebraicGeometry.Etale.exists_etaleCompactSupport_torWindow, with its sole proof `sorry`.
It introduces no definitions and preserves the node's statement and dependency fields verbatim.
The earlier Q05 landing (ledger entry 26718) split the natural-language proof in stage 1;
it did not attach a Lean statement. This delivery performs stage 2, without another split.
No repair note exists for the item in the read repository.

Hypothesis-by-hypothesis rendering:

- The field k is `(k : Type u) [Field k]`; characteristic p>0 is
  `(p ℓ : ℕ) [CharP k p] (hp : 0 < p)`. The prime and distinct-characteristic
  conditions are `(hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)`.
- U,W,V are `Scheme.{u}`, with each `.Over (Spec (.of k))` structure. Each is separated
  over k through `IsSeparated` of its structure map. Finite type is precisely
  `LocallyOfFiniteType` and `QuasiCompact` of that structure map.
- `(j : U ⟶ W) (r : W ⟶ V)` have their respective `.IsOver (Spec (.of k))` instances,
  `[IsOpenImmersion j]` and `[IsProper r]`. No compactification existence hypothesis
  or chosen map is substituted for this given factorization.
- The uniform integer e>=0 is `∃ e : ℕ`, outside the universal U,j quantifiers
  and all coefficient, degree and input quantifiers. Thus the bound is independent
  of U,j,R,a,b,K,P, explicitly capturing "depending only on r" in the fixed field
  setting. U and its separated finite-type structure, and then the open k-immersion
  j, are quantified after this bound; W,V,r are fixed before it. Proof Step 1 chooses
  e from r alone.
- Every geometric fibre is `pullback r v`, for an arbitrary algebraically closed
  field Ω and `v : Spec (.of Ω) ⟶ V`. Torsion sheaves F are ordinary abelian sheaves
  with each local section killed by some nonzero integer n, explicitly
  `∃ n : ℤ, n ≠ 0 ∧ n • s = 0`. There is no common-annihilator or prime-to-p
  restriction. The first conjunct says their cohomology in every integer degree
  `2 * (e : ℤ) < i` is `Subsingleton`, the zero abelian group. This is the
  recorded fibre-bound interface's vanishing convention, not `IsZero` on a bare type.
- R is arbitrary `(R : Type (u + 1)) [CommRing R] [Finite R]` and
  `∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : R) = 0`.
  An exponent at least one is equivalent to annihilation by any power, including
  exponent zero: that case forces R to be the zero ring, which also satisfies n=1.
- a,b are arbitrary integers with `a ≤ b`. K is `DerivedCategoryModule R U`, with
  `DerivedCategory.isBoundedConstructible R U K` and
  `DerivedCategory.hasTorAmplitudeIn R U a b K`. These are exactly the recorded
  ordinary small-etale coefficient category and constructibility/Tor predicates.
- P is an arbitrary `CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat R)) ℤ`.
  `Nonempty (DerivedCategory.Q.obj P ≅ K)` says it represents K. Its termwise
  flatness uses the recorded `exactFunctor` on canonical `tensorRight (P.X q)`;
  constructibility is `Scheme.IsConstructibleEtaleModuleSheaf (P.X q)`; zero outside
  [a,b] is `∀ q, q < a ∨ b < q → IsZero (P.X q)`.

Clause-by-clause conclusions (the conjunction following these hypotheses):

- Termwise extension by zero is `(openImmersionLowerShriek (ModuleCat R) j).
  mapHomologicalComplex (.up ℤ)`, applied to P. Its Q-image is asserted isomorphic
  in the derived category to the `mapDerivedCategory` image of K. This is a
  derived-object isomorphism, not merely an isomorphism on individual cohomology sheaves.
- Each extended term is flat through `exactFunctor _ _ (tensorRight ...)` and
  constructible through `Scheme.IsConstructibleEtaleModuleSheaf`.
- The extended complex still has `IsZero` terms whenever `q < a ∨ b < q`.
- It is K-flat through `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat`, the generic
  interface exposed by def-pc-kflat-complex for this module-valued sheaf encoding.
  Tensoring on either side preserves quasi-isomorphisms; for complexes over this
  symmetric abelian tensor category this is exactly the acyclic-total-tensor condition.
- Dj_!K is bounded constructible and has Tor amplitude [a,b], explicitly using
  `isBoundedConstructible R W` and `hasTorAmplitudeIn R W a b`.
- The last two conjuncts assert bounded constructibility and Tor amplitude
  `[a,b + 2 * (e : ℤ)]` for `(rightDerivedLowerStar (ModuleCat R) r).obj
  ((openImmersionLowerShriek (ModuleCat R) j).mapDerivedCategory.obj K)`.
  This is literally Rr_* Dj_!K. For the compactification
  `⟨W,r,j,rfl,inferInstance,inferInstance⟩ : Compactification (j ≫ r)`,
  `rightDerivedLowerShriekOfCompactification` unfolds to this same composite.
  No arbitrary functor, map, comparison assumption, or condensed/pro-etale category
  occurs. The ordinary compactification convention therefore needs no added equality clause.

Dependency declarations used (full recorded source signatures and docstrings read):

- WeilConjectures.AlgebraicGeometry.DerivedCategories:
  AlgebraicGeometry.Etale.DerivedCategoryModule and the ordinary cohomology/derived
  category convention. The public-import bounded-constructible module exposes it.
- WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf:
  AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf, exposed by
  WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes, together with
  AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible.
- Sheaf.AlgebraicGeometry.EtaleTorAmplitude:
  AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn (its documented existing
  bounded-interval predicate from WeilConjectures.SixFunctors.Etale.Derived.Coefficients).
- Mathlib.Algebra.Homology.HomologicalComplex: CochainComplex, used directly.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: CategoryTheory.exactFunctor,
  exposed by the recorded flatness module specifically for ModuleCat-valued sheaves.
  IsFlatOnSite itself takes the different ringed-site encoding; the record's note
  explicitly specifies this exactFunctor interface. No flatness is redefined.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  CategoryTheory.MorphismProperty.kFlat, publicly exposed by the recorded module
  for ordinary ModuleCat-valued sheaf complexes, exactly as its interface note directs.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
- sk-def-sfb-dc-setting's recorded compactificationOverField signature was read in
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible.
  As the record directs, its geometric setting is rendered as explicit binders.
  The condensed compactification choice is not used for this given ordinary factorization.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  AlgebraicGeometry.Etale.openImmersionLowerShriek, its exactness instance, and the
  inverse-image/restriction identification. These are publicly exposed by LowerShriek.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification, whose defining
  composite is the output above. UpperLowerStarCoherence is public-imported because
  it owns the public rightDerivedLowerStar used in the signature.

The plain proof imports retain the node's existing plan: Mathlib Noetherian,
Morphisms.Etale and ShortComplex.PreservesHomology; ProperGeometricFibreTorsionBound
(exists_proper_geometricFibre_torsion_cohomology_bound); EtaleOver (Scheme.Etale.overEquiv);
RingedSliceExtensionTensor (ringedSlice_extension_tensor); EtaleInverseImageModulesExact
(etaleInverseImageModulesExact); ConstructibleSheaf.OpenClosed
(IsConstructibleSheaf.openImmersionLowerShriek); BoundedAboveFlatSheafKFlat
(CochainComplex.isKFlat_of_boundedAbove_flat); DerivedCategory.FlatModel
(torAmplitudeIn_Q_obj_of_flat); ProperFiniteTorAmplitude
(isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper).
Already public-imported proof dependencies are not imported twice.
The theorem docstring carries all seven proof steps with their node names.

Source checks: read Stacks sites-modules.tex lemma-j-shriek-and-tensor (0E8I),
sites-cohomology.tex lemma-bounded-flat-K-flat (06YQ), and the current blueprint
sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-tor.md.
The statement follows the retained chart-domain proof and its reviewed node verbatim.

Edge cases checked before writing: U empty; j the identity; W or V empty; R the
zero ring; a=b; negative a,b; e=0; empty geometric fibres; torsion sheaves without a
uniform exponent; and nonflat coefficient rings. No `Nontrivial R`, nonempty scheme,
nonnegative degree, reduced scheme, or coefficient-field hypothesis is imposed.
P is quantified as any given flat constructible representative, without asserting
that every finite-Tor object admits a constructible flat representative. Naturals
only encode the nonnegative e, not the degree bounds. Universe u for schemes and
u+1 for coefficient modules follows the recorded ordinary etale category; finite
coefficient rings may be lifted without restricting their algebraic possibilities.

Actual searches for an existing statement:

- msearch.py leanfinder: “Extension by zero of a bounded flat constructible etale
  complex has the same Tor amplitude, and proper direct image increases the upper
  bound uniformly”. Eight hits, including DerivedCategory.isGE_Q_obj_iff,
  isLE_Q_obj_iff and generic derived t-structure bounds; none states the open/proper
  model and uniform compact-support Tor window.
- msearch.py loogle: `"torAmplitude", "Sheaf"`: zero hits.
- msearch.py grep: `torAmplitude|extensionByZero|openImmersionLowerShriek` in
  Mathlib/CategoryTheory: zero hits.
- msearch.py leansearch: “Compactly supported etale cohomology preserves
  constructible finite Tor complexes with a uniform cohomological interval”. Eight
  hits about generic complex support and derived t-structures; no exact statement.
- rg of lean/WeilConjectures and lean/Sheaf for the node id and
  `CompactSupportTor|compact_support_tor|openImmersion.*Tor` found no matching
  declaration. Broader compact-support and Tor searches found existing constituent
  constructions, not the conjunction of open flat model assertions and the
  coefficient-independent fibre bound. Existing generic flat-model, K-flat and
  proper finite-Tor statements are imported, not duplicated.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED finding.
The sandbox and library module-mode compilation initially identified the missing
public owner import for rightDerivedLowerStar; that import was added. A single long
line was wrapped. The final quantifier check placed U,j after the existential e
to record explicitly that the bound depends only on r, as the node states.
Final validation is the clean scompile plus deliver2 preflight.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
