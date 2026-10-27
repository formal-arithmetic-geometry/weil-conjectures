## Worker report

Item: lem-cbc-etale-clopen-mate-normalization. New module:
lean/Sheaf/AlgebraicGeometry/EtaleClopenMateNormalization.lean.
Namespace: AlgebraicGeometry.Etale.ClopenMateNormalization.

The module states this node in three named postponed theorems: lift_clopen
(the geometry in proof step 1), etaleClopenMateNormalization (ordinary and derived
normalization, with the canonical D+ to D compatibility), and
etaleClopenMateResolution (every representative/resolution and its chain transpose).
Every theorem has sorry as its proof and a source and full natural-language proof
docstring. All helper definitions contain actual constructions.
No node statement or dependency is changed. No new node or dependency module is needed:
all helpers belong to the specified comparison in this node, under the standing
missing-helper authorization, and all are listed in lean.declarations.

Hypotheses and clauses, checked against the node and more-etale.tex,
lemma-shriek-proper-and-open (Tag 0F7B), first paragraph:

- Finite commutative Lambda: Λ : Type (u + 1), [CommRing Λ], [Finite Λ].
  Scheme objects are Scheme.{u}; these are the existing small-etale module universes.
- Square: {V W S T : Scheme.{u}}, k : V ⟶ W, r : V ⟶ S,
  p : W ⟶ T, i : S ⟶ T, h : k ≫ p = r ≫ i.
  Both theorems bind [IsOpenImmersion k], [IsOpenImmersion i],
  [QuasiCompact k], [QuasiCompact i], [IsProper r], [IsProper p].
  No Cartesian-square hypothesis is introduced.
- W_S, b, q, s: pullback p i, pullback.fst p i, pullback.snd p i,
  pullback.lift k r h in alpha. lift_clopen states the open and closed immersion
  properties used in constructing the component projection.
- Small-etale constant-coefficient module sheaves: everywhere
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ).
  D+ is DerivedCategory.Plus of this category. Exact inverse image and open
  extension are upperStar and openImmersionLowerShriek, with mapDerivedCategoryPlus.
  R is lowerStar.rightDerivedFunctorPlus; the ambient version is its K-injective
  total rightDerivedFunctor.
- Cartesian open comparison: alpha begins with the inverse of the recorded
  openImmersionLowerShriekBaseChangeMap for (IsPullback.of_hasPullback p i).flip.
  Its defining conjugate formula and open-unit normalization were read in the
  upstream BaseChangeSquare and the compatibility dependency module.
- Identity/zero component projection: projection is the ordinary s inverse-image
  unit transported through inverse(openImmersionLowerShriekToLowerStar s).
  That inclusion is invertible because s has closed range; hence this is identity
  on the selected component and zero off it, rather than an arbitrary splitting.
- J_b J_s G_s G_q to J_k G_r: alpha composes the projection with the canonical
  openImmersionLowerShriekComp inverse, openCongr for lift_fst, upperStarComp
  inverse and lift_snd. openCongr is equality elimination on the actual functors.
- Proper-support delta: supportComparison selects the ordinary witness of the
  recorded properOpenInterchangeCoherence theorem. Its first condition is the
  equation after inclusion into the common (ir)_* = (pk)_*, which uniquely
  determines this isomorphism and preserves the underlying section. Thus choice
  is only from a uniqueness-normalized isomorphism, not an undetermined object.
  Its relation to properSupportSheafComposition was checked in the coherence
  theorem's proof and docstring. No replacement support functor is defined here.
- Underived proper mate: mate is mateEquiv for the actual upperStarLowerStarAdjunctions;
  the first conjunct of etaleClopenMateNormalization states mate = delta.hom.
- Derived proper mate: derivedAlpha and derivedAlphaPlus localize the actual alpha
  through Localization.liftNatTrans, inserting the exact composition isomorphisms.
  derivedMate and derivedMatePlus are mateEquiv for the induced underived
  adjunctions. No arbitrary derived transformation is supplied as a hypothesis.
- Named normalized finite comparison: normalizedComparison selects the second
  witness of properOpenInterchangeCoherence; its derived-unit condition uniquely
  determines the arrow. The second main conjunct identifies it with derivedMatePlus.
  Its normalization includes the refinement V = S, r = identity by the dependency's
  explicit refinement clause, so that case is retained by this equality.
- All bounded-below inputs and all representatives: etaleClopenMateResolution
  takes any L : DerivedCategory.Plus, any complex J with [J.IsKInjective], and
  e : DerivedCategory.Q.obj J ≅ DerivedCategory.Plus.ι.obj L. It imposes no
  termwise lower bound on J. I is any K-injective complex and t : k_!J ⟶ I is
  any quasi-isomorphism. [QuasiIso t] and [I.IsKInjective] are exactly the existing
  IsKInjectiveResolution conjunction in class-binder form.
- Resolution arrow: resolutionArrow maps delta degreewise, with the canonical
  mapHomologicalComplexCompIso on each side, then applies p_* to t.
  The first representative conjunct says derivedMate at L equals Q of this arrow
  with its explicit source and target identifications: r_* and p_* K-injective
  rightDerivedFunctorObjQIso, exact open mapDerivedCategoryFactors, the representative
  e, and inverse Q(t). In particular no isomorphism of representatives is suppressed.
- D+ interpretation: the third main conjunct identifies inclusion of derivedMatePlus
  with derivedMate through sourceCompatibility and targetCompatibility, assembled
  from mapDerivedCategoryPlusCompatibility and rightDerivedFunctorPlusCompatibility.
  Since the D+ inclusion is fully faithful, the ambient representative equation is
  precisely the desired D+ equation, even for J and I unbounded termwise.
- Transpose: transposeArrow is degreewise alpha at r_*J, then k_! of the ordinary
  r-adjunction counit, then t. The second representative conjunct identifies its
  termwise p-adjunction homEquiv with resolutionArrow. This is the equivalent
  chain-map transpose in the node, with the actual maps and specified t.

Dependency declarations read and used (including proof-plan imports):

- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, pullback.lift, fst, snd.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType, QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and its base-change/of_comp APIs.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- WeilConjectures.AlgebraicGeometry.DerivedCategories:
  the recorded D, D+, cohomology and module-sheaf encoding.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  lowerStar, upperStar, upperStarLowerStarAdjunction, upperStarComp.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  openImmersionLowerShriek, openImmersionLowerShriekUpperStarAdjunction,
  preservesFiniteLimits_openImmersionLowerShriek.
- Mathlib.CategoryTheory.Adjunction.Mates: CategoryTheory.mateEquiv;
  Mathlib.CategoryTheory.Adjunction.Basic: composite adjunction.
- Sheaf.AlgebraicGeometry.KInjectiveResolutions:
  CochainComplex.IsKInjectiveResolution, CochainComplex.IsKInjective, QuasiIso.
- Sheaf.AlgebraicGeometry.ProperSupportSheafComposition:
  AlgebraicGeometry.Etale.properSupportSheafComposition.
- Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence:
  properOpenInterchangeCoherence, ProperOpenUnderivedFamily,
  ProperOpenDerivedFamily and properOpenInterchangeConditions. The current source
  factors the originally recorded large conjunction into this named predicate;
  the source's actual complete signature and conditions were read.
- Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility:
  derivedExtensionZeroBaseChangeUnderivedCompatibility and its open-unit equations.
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
  AlgebraicGeometry.etaleInverseImageModulesExact.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  Functor.mapDerivedCategoryFactors and exact-functor localization.
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  Adjunction.mapHomotopyCategory and mapHomologicalComplex.
- Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist:
  CochainComplex.etale_kinjective_resolutions_exist.
- Sheaf.CategoryTheory.KInjectiveTotalDerived:
  CategoryTheory.exists_rightDerived_of_enough_isKInjective.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp:
  Adjunction.preservesKInjectiveComplexes.
- Mathlib.Algebra.Homology.DerivedCategory.KInjective: K-injective Hom bijection.
- Mathlib.CategoryTheory.Functor.Derived.Adjunction:
  Adjunction.derived and derivedε_fac_app.
- Additional existing canonical constructions: upstream openImmersionLowerShriekComp,
  isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range,
  mapDerivedUpperStarLowerStarAdjunction, Adjunction.derivedPlus,
  Functor.rightDerivedFunctorObjQIso, rightDerivedFunctorPlusCompatibility,
  mapDerivedCategoryCompIso and mapDerivedCategoryPlusCompIso.

Edge cases checked mathematically against the typed formulas: empty V or S,
zero module, zero finite ring, identity square, all horizontal identities,
V = S and r = identity with a non-Cartesian refinement. The zero ring requires
no Nontrivial instance. There is no cartesianness assumption on the original
square and no injectivity-of-terms assumption on the supplied representatives.
All universes are explicit; autoImplicit is false. No statement dispute was found.

Searches actually run using msearch.py:

- leanfinder: "The proper adjunction mate of the clopen open base change comparison
  equals the proper support composition on K injective resolutions". Eight hits,
  including InjectiveResolution.toRightDerivedZero_eq, sheafification compatibility,
  PullbackConstruction.adjunction and sheafAdjunctionCocontinuous_homEquiv_apply_val;
  none state this proper/open clopen normalization.
- loogle: "CategoryTheory.mateEquiv". Twelve hits: general mate equivalence,
  unit/counit and composition identities, not this geometric theorem.
- grep: "clopen.*mate|properSupport|proper.*open.*mate", CategoryTheory: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf: clopen transfer, open base change,
  ProperOpenInterchangeCoherence and tower/semilinear analogues were inspected.
  None states the finite-etale ordinary-mate plus arbitrary K-injective resolution
  assertion of this item. grep of the item id in WeilConjectures returned no hit.
  Existing canonical constructions were reused, not redeclared.

Validation: prescribed scompile.py compiled the complete delivered module both
as a sandbox module and under its final library module name, cleanly (9.4 and
8.6 seconds in the last run). A dependent equality transport was repaired using
openCongr. Explicit return types on derived mates and chain arrows prevent
expensive inferred-type unfolding; no time limit was changed. Every proof remains sorry.
The maintainer's independent review is the second reading; this worker has not
fabricated a second-reader report or started another agent.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
