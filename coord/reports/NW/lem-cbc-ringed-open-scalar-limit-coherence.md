## Worker report

Delivered module: `Sheaf.Paper.RingedOpenScalarLimitCoherence`.
Main declaration: `AlgebraicGeometry.Scheme.ringedOpenScalarLimitCoherence`.
There is one postponed theorem, whose proof is `sorry`; every helper has real data.
The node's mathematical statement, dependencies, proof and all other fields are unchanged.
No new DAG nodes or dependency repairs are needed.

### Hypotheses and objects

- An arbitrary scheme T is `{T : Scheme.{u}}`. The open j is the object
  `(U : T.ProEt)` with `[IsOpenImmersion U.hom] [QuasiCompact U.hom]` explicitly
  bound on the theorem. Any open immersion determines this site object, since it is
  weakly etale. No condition is imposed on T beyond being a scheme.
- `R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}` and `(a : R ⟶ S)` are the
  arbitrary commutative ring sheaves and their actual map. `proEtaleModuleCoefficients`
  forgets only commutativity. The literal slice categories are
  `ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)`, and likewise S.
  The coefficient and site universes follow the fixed size convention, with objects
  in u+1 and morphisms in u. They are never identified.
- The base scalar functor is the existing `SheafOfModules.scalarRestriction a`, an
  abbreviation of Mathlib's recorded `SheafOfModules.restrictScalars`. The slice map
  `cbcSliceCoefficientMap U a` is exactly `overPullback.map a`.
  `cbcSliceScalarRestriction U a` is the same recorded scalar functor with an explicit
  type over the literal restricted ring sheaves, to keep their presentation visible.
  It constructs no replacement coefficient map or module category.
- `localizedSystemExtension.{u+1,u,0} R U` (and S) is JR (and JS): precisely the
  recorded direct-sum extension presheaf followed by the recorded module sheafification.
  `localizedSystemRestriction` is the recorded `overFunctor` restriction to the slice.
- The eight `HasDerivedCategory.{wA}` instances choose the four unbounded derived
  categories of sheaves and of strict towers, as in the dependency's interface. These
  are choices of localization, available with the standard construction, and impose no
  boundedness condition. Towers use `ℕᵒᵖ`; index n represents the positive level n+1.
- `LUR`, `LUS`, `LTR`, `LTS` and their `eta` maps are arbitrary presentations of the
  total right derived limits. The four `IsRightDerivedFunctor` binders assert precisely
  this universal property for termwise inverse limit and quasi-isomorphisms. They are
  not arbitrary functors. `cbcTowerDerived` and `cbcTowerFactors` are the existing
  termwise postcomposition and exact-functor localization factorization, with explicit
  levelwise finite-limit and finite-colimit instances.

### Every clause of the conclusion

1. `e : JS ⋙ rT ≅ rU ⋙ JR` is the requested natural isomorphism (Lean writes functor
   composition in application order). Its first conjunct gives its value on every
   generator `cbcExtensionGenerator U S N V phi x`: it is the identical generator for
   R after scalar restriction. This generator is the actual summand inclusion followed
   by the unit of module sheafification. These generators locally generate, so the
   equation fixes exactly the identity-induced sheafification map, including its scalar
   action. It does not merely assert that some natural isomorphism exists.
2. `d : rT ⋙ qR ≅ qS ⋙ rU` has identity section maps. It is the concrete restriction
   identification understood in the node. `CbcAdjunctionCompatible e d adjS adjR`
   spells out both identities: scalar restriction of the S unit followed by `d.inv`
   and restriction of e is the R unit; e followed by JR of `d.inv` and the R counit is
   scalar restriction of the S counit. Both adjunctions are the uniquely summand-unit
   normalized `localizedSystemAdjunction` already recorded for the dependency.
3. The next compatibility conjunct uses `NatIso.mapHomologicalComplex` and the actual
   `Adjunction.mapHomologicalComplex` for both units and counits in every degree.
   The following conjunct uses `cbcDerivedTowerSquare` and
   `cbcDerivedTowerAdjunction` for the exact same equations on derived strict towers.
   The latter is exactly the recorded `exactDerivedAdjunction` applied to the actual
   tower adjunction `adj.whiskerRight ℕᵒᵖ`. No derived adjunction is arbitrarily chosen.
4. The four `HasExactLimitsOfShape (Discrete ℕ)` conjuncts assert exact countable
   products in all four module categories, on T and on its open slice, for R and S.
5. The four `IsIso (piComparison F N)` clauses assert invertibility of the canonical
   product comparisons. There is no `Nonempty I` hypothesis, so the empty product is
   included. Scalar restriction retains the actual section groups and restriction maps;
   hence, after the canonical sectionwise product identifications, its comparison is
   the identity on the underlying abelian sheaves, not a chosen product automorphism.
6. The four lambda witnesses are natural isomorphisms with the domains and codomains
   of the node's comparisons, using the same four L functors throughout. Each satisfies
   `CbcLimitNormalized`, which explicitly compares it with the ordinary-limit cone map
   and the two universal derived-limit units on every strict tower complex X:
   F(eta_X), then lambda, then the target limit of the exact tower factorization,
   equals the exact functor factorization, then the canonical ordinary-limit comparison,
   then eta_(FX). The ordinary comparison is `limit.lift` of the image limit cone, so
   every projection is F of the corresponding projection.
   This is the dependency's K-injective resolution normalization, not a choice of a
   triangle isomorphism. To compare it with the signed Roos normalization of
   `exactProductFunctorStrictLimit`, choose a K-injective I. Its eta is invertible,
   and the dependency's resolution clause identifies lambda with
   `F lim I → lim FI → Rlim FI`. The displayed square therefore pins lambda on I.
   Naturality and a K-injective resolution pin it on every derived object. Conversely
   the dependency's signed two-summand formula has this same square, by its resolution
   formula and naturality of eta, so these are precisely its normalized lambdas.
7. Each of these same four lambdas satisfies `CbcAugmentationCompatible`. A strict
   augmentation is literally a natural transformation from the constant diagram at
   an arbitrary unbounded complex Q to `X.asFunctor`. Its canonical derived map is
   `Q.map (limit.lift X.asFunctor ⟨Q, gamma⟩) ≫ eta.app X`. The equality states that F
   carries that map to the corresponding map for the image cone. All augmentations,
   including strict quotient augmentations and their completion units, are included.
8. The final `∀ M : DerivedCategory ...` is the displayed coherence equation, in Lean's
   left-to-right order: rT(lambdaJS), then lambdarT, then LTR(e_tower), equals e_(LUS M),
   then JR(lambdarU), then lambdaJR. `cbcDerivedSquare` and `cbcDerivedTowerSquare`
   transport the same e using the existing exact-derived natural-isomorphism and
   composition transports. All witnesses are natural isomorphisms, and the equality
   holds on every object; it is thus an equality of natural composites and is natural
   for every derived morphism, including roofs.

No flatness of a, boundedness of complexes, or quasi-compactness/quasi-separatedness of
T is added. Exactness of scalar restriction comes from the recorded ordinary/derived
coefficient adjunction; the concrete specialization instances simply reuse that result.
Sheafification and localized-functor instances are explicit specializations of existing
instances, with no instance disabled and no universe equality hypothesis.

### Dependency declarations read and used

- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `lem-weil-proetale-weakly-etale-localization`: `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `def-weil-extension-by-zero-presheaf`: `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`, `SheafOfModules.extensionByZeroPresheaf`.
- `def-weil-presheaf-modules-sheafification`: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, `PresheafOfModules.sheafification`.
- `lem-pur-site-restriction-module-adjunction-exact`: `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `SheafOfModules.localizedSystemExact`.
- `lem-sf-exact-functor-derived-triangulated`: `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`, `CategoryTheory.Functor.mapDerivedCategory`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`, `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `lem-cbc-ringed-open-extension-products`: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`, `AlgebraicGeometry.Scheme.proEtaleRingedExtensionByZero_products`.
- `lem-cbc-exact-product-functor-strict-limit`: `Sheaf.Paper.ExactProductFunctorStrictLimit`, `CategoryTheory.exactProductFunctorStrictLimit`.
- `lem-weil-proetale-countable-products-exact`: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.

`SheafOfModules.scalarModules`, `scalarRestriction`, and their finite-limit/colimit
instances in `Sheaf.Algebra.Homology.ScalarInternalHomData` are existing abbreviations
and instances for those recorded module categories and restriction functors, rather than
new notions. The natural-isomorphism and composition transports are
`Functor.mapDerivedCategoryNatIso` and `Functor.mapDerivedCategoryCompIso` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Proof inputs also use the recorded levelwise abelian tower category, sectionwise module
limits, and exact derived adjunction. The theorem docstring carries all eight node proof
steps verbatim, wrapped for line length. All helper docstrings identify this owning node.

### Edge cases and verification

- Empty U or T: direct sums and extension are zero; all four product and augmentation
  assertions still apply. The product index is allowed to be empty.
- Identity open: the same generator/unit equations give the canonical identity square.
- Identity coefficient map: the displayed normalization still fixes the comparisons;
  one cannot replace them with a rescaled natural automorphism.
- Zero ring sheaves: module categories are zero and all clauses remain meaningful.
- Nonflat `ℤ → ℤ/2`: only scalar restriction is used, so no tensor exactness is assumed.
- Unbounded complexes and arbitrary strict tower transitions remain in the binders.
  The least index n=0 is the positive level 1, not a missing zeroth quotient.
- The normalization uses an actual ordinary-limit cone and every derived-limit unit;
  it never assumes scalar restriction preserves K-injectives.

The final explicit compile is clean: sandbox 37.4 seconds, library 33.6 seconds, with
no errors or warnings. Compilation uses only the prescribed `scompile.py`, against the live published library,
for both the sandbox and library module presentations. Earlier elaboration failures were
repaired by fixing the literal slice category presentation and explicit universe instances,
not by imposing extra equalities. The final dry run and push are recorded by deliver2.py.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

### Searches

- `msearch.py ... leansearch "restriction of scalars commutes with extension by zero
  and inverse limit"`: eight hits, including `PresheafOfModules.restrictScalars` and
  `ModuleCat.preservesLimit_restrictScalars`; none state the complete result.
- `msearch.py ... leanfinder "Extension by zero commutes with restriction of scalars
  and normalized derived inverse limits"`: eight hits on ordinary module
  extension/restriction adjunctions and an adic completion factorization; no match.
- `msearch.py ... loogle "SheafOfModules.restrictScalars,
  SheafOfModules.extensionByZeroPresheaf"`: zero hits; the latter project name is
  unknown to the Mathlib service.
- `msearch.py ... grep "restrictScalars|extensionByZero"
  Algebra/Category/ModuleCat/Sheaf`: ten hits in ChangeOfRings and PushforwardContinuous;
  restriction exists, the complete scalar/open/normalized-limit result does not.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id, scalar/open/limit
  combinations, and the proposed declaration names: no complete existing statement.
  The finite constant-coefficient special case does not give arbitrary ring sheaves,
  and existing individual normalized-limit comparisons do not state this square.
- Read Stacks proetale.tex Tag 09BP and sites-modules.tex Tags 03DI/03DJ/03CY, plus the
  current main-20261015 blueprint's completed-extension-zero-comparison proof. These
  identify precisely the actual extension and normalized derived-limit constructions.

## Second reading by NW

A same-worker second pass was made with the node and final module open. The dispatcher
explicitly forbids starting another agent, and the maintainer supplies the independent
review, so this does not claim an independent worker review. The pass checked all eight
clauses above against the node and inspected the actual helper data, not just their names.
It caught the need to bind the open-immersion and quasi-compactness instances explicitly
on the theorem (unused section assumptions would otherwise be omitted by Lean), retained
both counit and unit equations at all three requested levels, and checked the order of all
six morphisms in the final equality. It also checked that the same four normalized lambda
witnesses occur in the augmentation clauses. The literal ringed slice categories now occur
in every derived category and quasi-isomorphism class, avoiding an implicit change of
localization presentation. No statement correction or additional hypothesis was needed.
