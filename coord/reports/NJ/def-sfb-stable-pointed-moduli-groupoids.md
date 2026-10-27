## Worker report

Item: def-sfb-stable-pointed-moduli-groupoids. Group NJ, stage 2, 2026-10-22.
One module: `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`. The item node
changes only in `lean`. No new nodes, dependency modules or statement correction.
No mathematical statement dispute was found.

The module gives actual data for all the moduli constructions. Its five named
well-definedness obligations have `sorry` proofs and source/proof docstrings:
`StablePointedModuli.hom_operations`, `StablePointedModuli.pullback_properties`,
`AbelianLevelModuli.hom_operations`, `abelianLevelBaseChange_isIso`, and
`AbelianLevelModuli.pullback_frame_condition` (all in `AlgebraicGeometry`). These
are the well-definedness clauses of the item's specified composition and pullback
constructions, not new moduli existence assertions. They have their exact
construction statements in the module; the item's DAG statement specifies the
corresponding composition, stable pullback and proper-base-change frame pullback.
The construction data do not come from these proofs: fibre products, projection
maps, sections, derived exchange, constants, frames and arrow compositions are
explicit. Only proof fields use these obligations. No arbitrary map or object is
selected from a mere existence assertion.

### Clause-by-clause reading

1. A scheme `S` is `Scheme.{u}`; `StablePointedModuli S g r` has an actual base
   `Over S`, a scheme `curve`, its `projection`, labelled `Fin r` sections and
   their section equations. Both parameters are natural numbers, so `r ≥ 0` is
   built in. The field `genus_at_least_two : 2 ≤ g` retains the stated genus bound,
   even over the empty scheme. `stable` is exactly the recorded
   `IsStablePointedCurve` predicate, including the projective-bundle convention.
2. `genus` quantifies over **every** algebraically closed field `Ω : Type u` and
   every `a : Spec Ω ⟶ base.left`. Its scheme is `pullback projection a`, with
   structural map `pullback.snd projection a`. It applies the recorded
   `RingedSpace.moduleCohomology C.toRingedSpace 1` to the unit module, restricts
   scalars along `Ω → Γ(Spec Ω,O) → Γ(C,O)`, and takes `Module.finrank Ω` equal
   to `g`. Thus it uses coherent **Zariski** cohomology on possibly nodal fibres,
   with the source's scalar action; it does not use the smooth-curve genus
   predicate or étale cohomology for this condition.
3. `StablePointedModuli.Hom` is an actual base arrow and a cartesian square with
   `markings : ∀ i, X.sections i ≫ map = base.left ≫ Y.sections i`. A cartesian
   square is exactly an isomorphism from its source curve to the specified
   pullback over the source base. Composition is pasting with maps
   `a.map ≫ b.map`; the pullback universal property supplies precisely the
   canonical associativity identification in the node. The category identities
   and associative laws are the componentwise category laws.
4. `StablePointedModuli.forget` is the total-category projection.
   `StablePointedModuli.Fiber S g r T` is the core of its actual fibre over `T`;
   arrows are the labelled `T`-isomorphisms. The core takes isomorphisms, not
   isomorphism classes: automorphisms are retained. `StablePointedModuli.Smooth`
   is the full subcategory cut out by the recorded `AlgebraicGeometry.Smooth`
   on the projection.
5. `StablePointedModuli.pullback` is the genuine scheme fibre product. Its sections
   are `Scheme.Hom.baseChangeSection`, with the recorded projection equations.
   `pullbackArrow` is the first projection on curves and the given base arrow.
   It is a cartesian labelled square, not a freely chosen family comparison.
6. `CategoryTheory.IsFibredInGroupoids` reuses `Functor.IsFibered` and requires
   that every arrow is `Functor.IsStronglyCartesian` over its image. The first
   conjunct supplies a lift of each base arrow. Strong cartesianness supplies
   exactly the node's unique factorization of two arrows with a compatible
   base arrow. Stacks 003T explicitly identifies its second lifting condition
   with all arrows being strongly cartesian; its first then gives a fibration.
   Morphisms are Mathlib `BasedFunctor` (functors commuting with projections).
   `ModuliTwoIso` consists of actual natural isomorphisms with every component
   `IsHomLift` over the identity of the base object.
7. `GroupoidTwoFiberProduct f g` uses `Core (Comma f g)`. Because the three
   categories are groupoids, its object arrow is an isomorphism and all comma
   arrows are invertible. The comma equation is
   `f.map v ≫ φ' = φ ≫ g.map w`, exactly the node's equation in Lean order.
   `moduliTwoFiberProduct` for categories over a base takes the full iso-comma
   subcategory whose comparison lies over an identity. Its projection and
   cartesian arrows are inherited from the indicated factors; this is the
   fibrewise 2-product, not the ordinary pullback of sets of coarse points.
8. `AbelianLevelPrime S` is a natural prime `ℓ`, the proof `3 ≤ ℓ`, and
   `∀ x : S, IsUnit (ℓ : S.presheaf.stalk x)`. This is the stated local-ring
   invertibility condition and imposes no global trivialization or field base.
   The coefficient ring is `ULift.{u+1} (ZMod ℓ)`: the lift is the published
   étale coefficient size convention, canonically the same ring as `ZMod ℓ`.
9. `abelianLevelCohomology f ℓ` is degree one of the actual right derived
   `Etale.lowerStar` on the constant coefficient module sheaf.
   `abelianLevelConstant T g ℓ` is the sheafification of the constant module
   `Fin (2*g) → A`. `AbelianLevelModuli.family` is smooth, stable, unpointed and
   genus `g`; `frame` is an actual isomorphism between these two module sheaves.
   Fixed-ring coefficient sheaves use `Sheaf ... (ModuleCat A)`, the existing
   encoding in the recorded PBC API. These are equivalently sheaves of modules
   over the constant ring sheaf; no arbitrary ring sheaf is replaced by a
   constant one. In particular the frame is module-linear. No symplectic
   pairing, polarization, determinant or component choice occurs.
10. The alternative sheafified-presheaf description of this same higher direct
    image is the recorded `sbc-lem-higher-direct-image-presheaf` comparison. The
    underlying abelian comparison is imported from
    `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`; its
    sections are the indicated degree-one étale cohomology groups with the
    cohomology pullback restrictions. We use the direct-image definition, not
    a separately chosen sheafification or an arbitrary isomorphic sheaf.
11. `abelianLevelBaseChange` explicitly composes the right-derived/single
    comparison, exact inverse image/homology comparison, the recorded
    `Etale.derivedBaseChangeMapPlus`, its single-complex comparison, and the
    canonical `Scheme.upperStarConstantSheafIso`. Hence it is the degree-one
    exchange for the actual commutative family square, not an unspecified
    isomorphism. Its `IsIso` proof obligation is precisely proper base change
    for constant torsion coefficients, with the stated nonzero integer.
12. `AbelianLevelModuli.HomCondition` says that inverse image of the target
    frame followed by this exchange equals the constant-module comparison
    followed by the source frame. Over an identity base arrow this is exactly
    `α* λY = λX`. The category retains the actual family cartesian arrow.
    `AbelianLevelModuli.Fiber` retains all frame-preserving automorphisms.
13. `AbelianLevelModuli.pullback` uses the specified family fibre product and
    the composite: inverse constant comparison, inverse image of the frame,
    degree-one exchange. Properness is supplied from the family's actual
    `IsProjectiveBundle` proof by the recorded `projectiveBundle_proper`.
    `abelianLevelBaseChange_isIso` supplies a proof of invertibility of this
    explicit exchange. Its nonzero hypothesis is `ℓ.property.1.ne_zero`.
    `AbelianLevelModuli.pullbackArrow` is the actual family first projection,
    with the frame equation given by the same specified composite.
14. `discreteModuli (yoneda.obj Q)` presents `h_Q`: an object over `T` is
    `h_T → h_Q`, canonically an `S`-map `T → Q` by Yoneda. Morphisms have the
    precomposition condition and fibres are discrete. `discreteModuliMap`
    is composition of those natural transformations. `IsRepresentedByScheme`
    is existence of a based functor from this groupoid that is an equivalence.
    Thus it forces trivial automorphisms and does not assert representability
    of any stable or level groupoid.
15. `IsCoarseModuliScheme F Q π` uses the actual based map `π`. Its first
    conjunct is bijectivity, for every **algebraic space** `Z/S`, of composition
    on `yoneda.obj Q ⟶ Z.obj.obj` and based maps `F → h_Z`. The source of the
    map is the set of `S`-maps from `Q` into `Z`, by Yoneda. Its second conjunct
    is bijectivity of the **induced** `mapSkeleton.obj` of the fibre functor at
    every `Spec Ω → S`. Mathlib's skeleton is the quotient by isomorphism;
    the target skeleton of a discrete representable fibre is canonically
    `Q(Ω)`. No unrelated set bijection substitutes for the induced map.
16. `IsModuliStack` is the total-category sieve-descent formulation, described
    in more detail below. It uses the **big étale** topology on `Sch/S`, not
    the Zariski, small étale or fppf topology on the moduli category. It retains
    both the isomorphism-sheaf condition and effective descent for objects.
17. `HasSpaceBaseChange` supplies a based equivalence of the actual scheme
    2-base change with the discrete groupoid of the recorded `AlgebraicSpace`.
    Its projection is compared by an actual vertical natural isomorphism with
    `discreteModuliMap a`. `IsRepresentableByAlgebraicSpaces` quantifies this
    over all test schemes and all maps to the target.
18. `HasAlgebraicSpaceDiagonal` is the standard equivalent diagonal criterion:
    for every pair of maps from schemes `T,U`, their 2-fibre product is an
    algebraic space. Its projection to `T ×_S U` is induced by the two factors;
    a based equivalence transports this map. These are precisely the scheme
    tests for representability of the diagonal, not a separatedness or
    representability-by-schemes requirement.
19. `IsDeligneMumfordModuliStack` conjoins the stack predicate, this diagonal
    predicate, and the existence of a scheme `U` and a map `h_U → F` such that
    **every** scheme 2-base change has an algebraic-space presentation whose
    specified projection is étale and surjective. `SpaceMapIsEtale` uses the
    recorded `AlgebraicSpace.IsEtale` charts and `AlgebraicGeometry.Etale` on
    the induced scheme maps. `SpaceMapIsSurjective` is joint surjectivity of
    these chart maps on underlying scheme points. These predicates assert
    no atlas, coarse scheme or scheme representative for these moduli categories.

### Total-category stack interface

Mathlib's `Pseudofunctor.IsStack` has a **pseudofunctor** argument. This module
works with the item's actual **total categories** and does not assume a chosen
split cleavage or invent a second pseudofunctor. `IsModuliStack` states the
same descent condition directly on the total-category projection:

For each covering sieve `R` on `T`, a diagram `D : R.arrows.category ⥤ F.obj`
with `D ⋙ F.p = R.arrows.diagram` is a compatible cartesian section over the
sieve. All arrows are cartesian by the CFG conjunct. The cocone has an apex
over `T`, and the equation on every leg fixes its projection to be the
canonical arrow in `R`. A colimiting cocone expresses gluing and unique gluing
of arrows together. To compare with the node's formulation, object descent
extends the compatible local objects to an apex; the Isom-sheaf property gives
unique arrows from this apex to another such cocone. For cocones with a
different base, their base arrows first glue uniquely because representables
are étale sheaves, then the same Isom-sheaf condition applies to the pullback
of the other apex. Conversely such colimiting cocones give effective descent,
and their unique arrows give the Isom-sheaf equalizer. Covering-sieve descent
and Čech descent for the generating étale covers are equivalent. Thus this
formulation adds no colimit-preservation hypothesis on `F.p` and omits neither
of the node's stack axioms. It uses existing Mathlib sieves, diagrams,
cocones and `IsColimit`, not a private copy of those notions.

### Dependency declarations read and used

The statement dependencies were read from their node records and their actual
source signatures/docstrings. The relevant interfaces are:

- `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `AlgebraicGeometry.IsStablePointedCurve`; its section construction is the
  published `Scheme.Hom.baseChangeSection` and its two projection equations.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle`, inherited through `stable`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom` and
  `Scheme.SpecToEquivOfField`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; Mathlib's `Field` and `ZMod`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (both recorded fibre-product nodes).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, applied to the actual unit
  module over `moduleRings C.toRingedSpace`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and its
  objects `Scheme.Etale`; its big `Scheme.etaleTopology` supplies stack descent.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf` and `.Sheafification`:
  `constantSheaf`, whose data are `Functor.const ⋙ presheafToSheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `Etale.upperStar` and their adjunction; the published coherence modules
  supply `Etale.derivedBaseChangeMapPlus` and its exact-functor comparisons.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology`
  and `Etale.rightDerivedGlobalSections`; together with the recorded
  `Etale.cohomologyMap` of `.UpperLowerStar.TopologicalInvariance` these are
  the interpretation of the equivalent presheaf description, not a second
  higher-direct-image object.
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`:
  `Etale.nonempty_higherDirectImage_iso_sheafification_abelian` and its
  `_single` specialization (the recorded comparison of the equivalent description).
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is the
  recorded general `SheafOfModules` encoding. The specific **constant**
  coefficient setting here uses the published equivalent `Sheaf ModuleCat`
  encoding in PBC, preserving module-linear maps and isomorphisms.
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`:
  `CategoryTheory.geometric_inverse_image_constant_module` gives the arbitrary
  site constant-module comparison. The actual scheme-map comparison used
  here is the published canonical `Scheme.upperStarConstantSheafIso` from
  `WeilConjectures.ConstructibleSheaf.Defs`, in the fixed-ring encoding.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`:
  `Etale.isIso_baseChange_of_isProper` and its constant torsion-ring form
  `Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring` are the named
  proper-base-change inputs to the degree-one exchange obligation.
- `Sheaf.TraceFormula.ProjectiveBundleProper`:
  `AlgebraicGeometry.projectiveBundle_proper`, with precisely the bundle
  convention carried by the stable family; no H-projective assumption added.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and its scheme-test chart definition. No private
  notion of algebraic space is introduced.
- The size convention is metatheoretic. Schemes and geometric fields have
  explicit universe `u`; fixed étale coefficients use `u+1`; the generic
  category interfaces retain independent object and morphism universes.

### Edge cases checked before and during writing

`r=0` uses `Fin 0`, so no artificial section or label permutation is present.
The minimal genus is `g=2`, including a reducible nodal stable fibre; the genus
uses all of its Zariski `H¹`, not genus of a normalization or smooth locus.
No extra smoothness condition is imposed on the compactified category.
Over an empty base the fibrewise genus condition is vacuous but the stated
`g≥2` bound and actual empty family data remain; no nonemptiness is imposed
on `S` or `T`. There is no Noetherian or finite-type assumption on either base.
The allowed level `ℓ=3` is included wherever it is locally invertible;
characteristic `ℓ` is excluded exactly by the local-unit condition, without
excluding any other characteristic. `ℓ=2` and nonprimes fail the level datum.
The rank is `2*g`, and the entire isomorphism set is retained: no symplectic
or determinant restriction and no connected-component choice occurs.
Automorphisms remain in the stable and smooth groupoids; representation is
only a predicate and would imply their triviality. Coarse point comparison
uses algebraically closed fields and the actual induced map on isomorphism
classes. Empty étale covers in the stack predicate enforce the usual descent
condition over the empty scheme. Arbitrary base arrows, including identities,
are handled by the same explicitly constructed exchange map and pullback.

### Searches and source reading

Fresh required wrapper searches, with results retained in sandbox `searches.jsonl`:

- LeanFinder: `groupoid of stable pointed curves moduli stack and abelian level
  structure`: eight unrelated groupoid/Galois/Weierstrass results; no moduli definition.
- Loogle: `CategoryTheory.Functor.IsFiberedInGroupoids, CategoryTheory.Groupoid`:
  zero hits and unknown first identifier. Direct source inspection instead
  found and reused `Functor.IsFibered`, `IsStronglyCartesian`, `Groupoid`,
  `Core`, `BasedFunctor` and the fibre API.
- Grep: `StablePointed|Moduli|moduli|IsFiberedInGroupoids`: only the arithmetic
  moduli reference in Weierstrass material, not these moduli categories.
- LeanSearch: `stable pointed curves moduli groupoid abelian level structure`:
  eight unrelated group, manifold groupoid and modular-form results.
- Direct `rg` in `lean/WeilConjectures` for `Moduli|moduli|StablePointed|AbelianLevel`
  and the item's blueprint id: no definition of this moduli problem.
- Direct `rg` in `lean/Sheaf` found the existing stable-curve predicate and its
  consumers. Searches for the new moduli/interface names found no duplicate.
  The generic pseudofunctor stack interface was read in
  `Mathlib.CategoryTheory.Sites.Descent.IsStack`; it has a different input
  interface from the total-category convention specified here.

Read the current node, all its statement dependencies, and the recorded
signatures/docstrings, including the full stable-pointed-curve and
algebraic-space definitions. Read the local Stacks sources at categories.tex
003T and 003R; stacks.tex definition-stack-in-groupoids; algebraic.tex the
algebraic-stack diagonal/atlas definition and definition-deligne-mumford;
etale-cohomology.tex Tag 03Q8. The primary Pikaart--de Jong paper was read
online at https://arxiv.org/pdf/alg-geom/9501003, §§1.1 and 2.3.3--2.3.7.
Its unrestricted abelian frame convention agrees with the node; no
representability result in that paper is asserted in this definition module.

### Validation

All compiler probes and delivered-module checks use the prescribed `scompile.py`
against the live server build, with module mode and explicit universes.
The final module compiled cleanly in both sandbox and library-name modes
(29.3 s and 26.1 s respectively), with no warnings or errors. The required
delivery wrapper repeats the per-file compile and runs server preflight. No direct repository edits,
git commands, launcher-script changes or global builds were performed.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
