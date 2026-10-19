## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finiteCoefficientOpenDerivedImage`
in `Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage`. Its only postponed proof
is this theorem. The two helper definitions contain real data: the actual Mathlib
pushforward along the existing coefficient map, and the actual section map of
the small-model module Kan adjunction. There are no new independent notions,
new DAG nodes, dependency repairs, or changes to the mathematical statement.

The previous worker's diagnosis confused Q38's completed stage-1 split with a
stage-2 statement. Q38's report explicitly says that no Lean work or compilation
was performed. The shared item's `lean` record was absent. This delivery supplies
that missing record and statement, rather than repeating the unchanged split.

Clause-by-clause correspondence:

- A scheme T and arbitrary open immersion j:U -> T are `{U T : Scheme.{u}}`,
  `(j : U ⟶ T)`, `[IsOpenImmersion j]`. There is no Noetherianity,
  quasi-compactness, separatedness, or constructibility restriction.
- A finite, possibly noncommutative discrete ring is `(A : Type (u + 1))`,
  `[Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]`.
  No `CommRing` assumption is made. The topology binders express the discrete
  convention in the coefficient node; every finite ring has this presentation.
- The coefficient sheaves are exactly `finiteCoefficientRingSheaf S A`, the
  sheafification of the connected-component continuous-function presheaf.
  `FiniteCoefficientModules S A` is the recorded category of LEFT module sheaves.
  `FiniteCoefficientDerivedCategory S A` is its ordinary unbounded derived
  localization. The site objects remain in universe u+1 with Hom universe u;
  coefficients and section modules use the common u+1 universe, and the derived
  Hom universe is the dependency's standard u+2. No site universes are equated.
- The actual module inverse image with transported action is
  `finiteCoefficientModulePullback j A` from the constant-exact node. It is used
  verbatim; neither a constant-scalar replacement category nor another inverse
  image is introduced.
- The site localization is expressed through the existing
  `Scheme.proEtaleOpenComposition j`, which sends W/U to W/T, with its original
  underlying scheme. The existing projection
  `Scheme.proEtaleOpenSectionProjection j V` is V times_T U -> V. The node
  `lem-pur-proetale-open-unit-evaluation` is added to `stmt_deps` solely because
  its already recorded declarations own these two site helpers. Its theorem
  about commutative coefficients is not applied to A.
- The existential natural ring-presheaf isomorphism `d` identifies A_U with the
  restriction of A_T. Its equation on `finiteCoefficientScalarMap` fixes every
  constant section. Sheafification and the local generation by constant
  sections make this the specified coefficient comparison, not a permutation
  or an arbitrary coefficient isomorphism.
- `rho N W` is an additive equivalence from the actual sections of j^*N on W/U
  to N on W/T. Its first conjunct is semilinearity through `d`; its second is
  naturality in W; its third is naturality in N. Together these are the natural
  coefficient-action-preserving restriction identification in the statement.
- `finiteCoefficientOpenDirectImage j A` is defined directly by
  `SheafOfModules.pushforward` along `finiteCoefficientDirectImageMap j A`.
  It therefore has sections G(V times_T U), with A_T(V) acting through the
  published coefficient restriction homomorphism. The published functor named
  `finiteCoefficientModuleDirectImage` requires commutativity, so it cannot be
  applied here; this abbreviation specializes the existing general Mathlib
  construction without copying its definition or inventing a new coefficient map.
- The existential `Additive` witness supplies the routine sectionwise additive
  structure needed for termwise direct image. It is a conclusion, not an extra
  hypothesis, and introduces no alternative direct image.
- `adj` is the module inverse-image/direct-image adjunction. Its first unit
  equation equates every actual section map to `finiteCoefficientOpenUnitSection`.
  That helper is the unit of `SheafOfModules.pullbackPushforwardAdjunction`
  on the original published small models, evaluated on the original section.
  Restriction along c inverse changes only actions, so no new section map is
  chosen. This fixes the unit to the specified Kan adjunction, excluding the
  ambiguity of simultaneously rescaling rho and an otherwise unspecified adjunction.
- The second unit equation says that applying rho to that unit gives
  `N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m`. This is exactly
  N(V) -> N(V times_T U), including its coefficient action.
- `L` with `alpha : Q ⋙ L ≅ j^*.mapHomologicalComplex (.up ℤ) ⋙ Q` is the
  termwise induced derived restriction. The exact localization universal
  property determines this pair up to its unique compatible isomorphism.
  Thus alpha explicitly records Q_U j^* = j^* Q_T in its appropriate direction.
- `R` with `beta` and `R.IsRightDerivedFunctor beta (quasiIso ...)` is the total
  right derived functor of the specified termwise j_*. This is its actual
  universal property, rather than an arbitrary functor equipped with an
  unconstrained map. The presentation uses Q on complexes; precomposing the
  homotopy-category comparison by the quotient is equivalent, since both
  termwise functors and Q factor through homotopy classes.
- `derivedAdj : L ⊣ R` is normalized by the final formula at every K-injective
  representative. Such representatives exhaust the derived category, so this
  fixes its unit to the adjunction induced from `adj` and beta.
- Every K-injective unbounded I is quantified by
  `∀ (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective]`.
  The first conjunct is exactly `CochainComplex.IsKInjective` of its termwise
  pullback. This is Mathlib's null-homotopy condition for every chain map from
  an acyclic complex, as recorded by the Hom-derived dependency. There is no
  boundedness or termwise injectivity assumption.
- The next conjunct is `IsIso (beta.app (j^*.mapHomologicalComplex.obj I))`.
  Its source is Q_T(j_*j^*I); its target is R(Q_U j^*I). Together with alpha,
  this is precisely the representation of Rj_*j^*(Q_TI) in the node.
- The final equation is
  `derivedAdj.unit.app (Q.obj I) ≫ R.map (alpha.hom.app I) =
   Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫ beta.app (j^*I)`.
  The complex adjunction unit has degree q equal to `adj.unit.app (I.X q)`.
  The earlier section equation makes this the termwise restriction map. Since
  beta at j^*I is invertible, identifying the target by beta turns the derived
  unit into exactly Q_T(I -> j_*j^*I), as requested.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`, the existing locally ringed space predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientPresheaf`, `finiteCoefficientRingSheaf`,
  `finiteCoefficientScalarMap`, `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientModules_hasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModelRingUnit`, `finiteCoefficientModulePullback`, its additive
  instance and its exactness theorem. All signatures retain arbitrary Ring coefficients.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientDirectImageMap`, its actual sheafification construction and
  `finiteCoefficientInverseImageMap_isIso`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, the inverse-image
  node's recorded module, reexports the original site constructions used here.
  The relevant original module `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
  supplies `Scheme.proEtaleBaseChange`, `proEtaleModuleToModel`,
  `proEtaleModuleFromModel`, and the site/sheaf adjunctions. Its commutative
  `sfIntrinsicConstantModuleAdjunction` is deliberately not applied to A.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`:
  only `Scheme.proEtaleOpenComposition` and `proEtaleOpenSectionProjection`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory.Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, `quasiIso_iff`; the bounded-below
  clause of that dependency is `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`.
  The full signatures and docstrings were checked, including the underlying
  `CochainComplex.IsKInjective` class in HomotopyCategory.KInjective.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
  Its right-Kan universal property is rendered by `IsRightDerivedFunctor`.
- Proof imports retain the recorded localized K-injective restriction,
  arbitrary-ring-sheaf Grothendieck property, general Grothendieck K-injective
  resolution instance, right-adjoint K-injective preservation, and slice
  sheafification interfaces. The unstated proof node
  `lem-sfb-proetale-object-inverse-image-restriction` has no module to import;
  its role is recorded in proof step 1, not silently assumed as a new Lean axiom.

Sources read: the archived blueprint ancestor's full Proof, Stacks
sites-cohomology.tex, Section 08FH and Lemma 08FI (restriction preserves
K-injectives), and derived.tex Lemmas 070Y and 070K (existence/computation of
right-derived functors). They agree with the item's split proof and require
neither commutative coefficients nor termwise injectivity for this lemma.

Edge cases checked: U=T makes composition/restriction and both units identity
under their canonical comparisons. U empty gives the zero restricted module
category and unit I -> 0. The zero ring gives zero module categories throughout.
A noncommutative ring such as M_2(F_2) is covered: all maps use left actions and
ring homomorphisms, never a commutative tensor formula or reversed scalar order.
Disconnected schemes are covered because `d` is normalized on locally generating
constant sections and the underlying continuous-function presheaf is retained.
Unbounded complexes are quantified explicitly; no injectivity of each term is used.

Searches for an existing complete statement and the notions it uses:

- `msearch.py ... leanfinder` with query "Open restriction of a K-injective
  complex of finite proetale module sheaves and derived direct image adjunction
  unit" returned Scheme.Modules.restrictAdjunction and its unit/counit formulas,
  and SheafOfModules.pushforwardSections_unitHomEquiv. The former uses Zariski
  structure-sheaf modules, and the latter is generic infrastructure. None states
  this finite pro-etale arbitrary-ring conjunction.
- `msearch.py ... loogle '"IsKInjective"'` returned the generic K-injective
  definition, invariance under homotopy equivalence/isomorphism, shift lemmas,
  bounded-below termwise-injective examples, and the null-homotopy constructor.
  These are used as infrastructure, not another statement of this item.
- `msearch.py ... grep 'restrict.*KInjective|derivedη_fac|mapDerivedCategoryAdjunction'
  Algebra/Homology` returned no hits. Direct source inspection found the generic
  derived-unit formulas in Mathlib.CategoryTheory.Functor.Derived.Adjunction,
  which require the site and coefficient comparisons supplied here.
- `rg` in the upstream WeilConjectures tree for the exact item id returned no
  match. Concept searches in SixFunctors/ProEtale found clopen idempotent and
  derived open extension-by-zero results, not this statement.
- `rg` in the side Lean tree found `ProEtaleOpenUnitEvaluation`, read in full:
  its module coefficient theorem is commutative, so it is reused only for its
  coefficient-independent site definitions. Searches also found the published
  finite-coefficient direct image (commutative interface), read in full, and the
  noncommutative coefficient ring map, which is reused verbatim here.
- Full-name searches for all three new declarations in side and upstream Lean
  returned no collisions. The dependency records, their modules, signatures
  and docstrings were read before drafting. No second definition of an existing
  general construction is introduced.

Validation: `scompile.py Q35 lem-exc-proetale-open-derived-image` compiled the
entire delivered module cleanly (7.0 seconds for the module), without errors or
warnings. The compilation also validates the original small-site object/Hom
universes and the section type of the Kan unit against the actual pullback.
All variables and the sole universe u are explicitly bound; autoImplicit is false.
The source has no lines longer than 100 characters. Required dry-run preflight
and delivery results follow in the task transcript.

Additional required LeanSearch check: `msearch.py ... leansearch` with query
"A K-injective complex of proetale module sheaves restricts to a K-injective
complex on an open subscheme and its derived direct image unit is the termwise
restriction map" returned eight hits: Zariski Scheme.Modules restriction/unit
lemmas, complex-shape `HomologicalComplex.restrictionMap`, and ModuleCat.Tilde.
These have different sites or restrict complex indices, so none states this
item. Direct Mathlib grep also located `Adjunction.derivedη_fac_app` at line 103
of CategoryTheory/Functor/Derived/Adjunction.lean; the generic formula was read.

The required `deliver2.py Q35 lem-exc-proetale-open-derived-image --no-push`
completed successfully: `OK (dry run): commit df4c6f1fdc passes the preflight and
compiles; nothing pushed`. Its staged paths were exactly the item's module,
node record and Q35 report. The former unchanged-node failure did not recur.

## Repair self-check (2026-10-17)

The return at immutable head `d3fc6eab7ddd` rejected the repository-relative
report filename as an `--apply-fixes` input. This submission uses the complete
sandbox delivery packet through `deliver2.py`, which stages this report at
`coord/reports/Q35/lem-exc-proetale-open-derived-image.md`; that repository path
is an output of delivery, not a file passed to `--apply-fixes`.

The saved packet's initial repair dry run passed preflight and compilation
(`2230b2d7b2`). The self-check confirms that the recorded signature is verbatim,
the natural statement is unchanged, the only node changes are `lean` and the
documented added statement dependency, both helper definitions have real data,
and the sole postponed proof is the named theorem. Explicit variables and the
100-character line limit were checked again. The Lean module is retained.

## Second reading by Q35

Independent second reading of the immutable delivery: the item JSON, all eight
statement dependencies, the blueprint proof place, the side pro-etale framework,
the delivered module and every declaration used were read. The Lean signature is
verbatim equal to the node statement field and binds only `u`; its `Scheme.{u}`
site and `Type (u + 1)` coefficient universes match the dependency interfaces.
The finite/discrete `Ring A` hypotheses are exactly the finite discrete-ring
convention required by `finiteCoefficientRingSheaf`; there is no commutativity,
Noetherianity, quasi-compactness, constructibility, boundedness, or termwise
injectivity assumption. The conclusion checks clause by clause: the canonical
constant-preserving coefficient isomorphism `d`, additive section comparison
`rho` with scalar, object, and module naturality, the actual transported module
pullback and pushforward, both ordinary unit equations, K-injective preservation,
the factorization `alpha` through derived localization, the right-derived
comparison `beta` and its K-injective isomorphism, and the final derived-unit
identity. The direct image is the actual `SheafOfModules.pushforward` along
`finiteCoefficientDirectImageMap`; no pro-etale substitute or arbitrary map is
introduced. The two helper definitions contain real constructions, and the only
postponed theorem proof is `sorry`.

I checked the exact side declarations for `finiteCoefficientModulePullback`,
`finiteCoefficientDirectImageMap`, `finiteCoefficientModelRingUnit`,
`Scheme.proEtaleOpenComposition`, and
`Scheme.proEtaleOpenSectionProjection`, plus the K-injective and right-derived
interfaces. Their docstrings cite source places and `(blueprint: ...)`, and the
module docstring does too. Searches in the side and upstream Lean trees and the
Mathlib search results found no duplicate complete notion; the generic Zariski
module restriction results are not this pro-etale finite-ring statement. Edge
cases checked are `j = id`, empty `U`, the zero ring, a noncommutative finite
ring such as `M_2(F_2)`, disconnected objects, and unbounded complexes; all are
covered by the quantified statement and canonical maps.

The delivered file was recompiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q35 lem-exc-proetale-open-derived-image snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleOpenDerivedImage.lean`.
Server confirmation and the local side overlay both returned exit 0 with no
errors or warnings. No lake/global build, live Lean write, repository edit, git
mutation, claim, merge, or delivery was performed. This replacement only makes
this required second-reading section substantive; no Lean or JSON correction is
needed.
