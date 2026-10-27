## Worker report

This delivery states `lem-sfb-ringed-dg-scalar-adjunction` without changing its
natural-language statement. The two theorem declarations in
`Sheaf.CategoryTheory.RingedDgScalarAdjunction` cover the general ringed-site
adjunction and its open-site compatibility. Their proofs are `sorry` and their
docstrings give the proof plan. Two definition modules supply the missing
ringed-site dg notions and the open-restriction comparisons. Their definitions
contain real data and no `sorry`; the existential structures are specifications
of data, not chosen objects extracted from an unproved existence assertion.

Hypotheses and clauses, with namespace `CategoryTheory.RingedSiteDg` throughout:

- A site of arbitrary object and morphism universes: `{C : Type c}`,
  `[Category.{v} C]`, `{J : GrothendieckTopology C}`. The coefficient universe is
  independent (`u`); `[EssentiallySmall.{u} C]` expresses smallness relative to
  it. No equality of site and coefficient universes is imposed.
  `J.HasSheafCompose (forget₂ CommRingCat RingCat)` is the standard coefficient
  forgetful-sheaf interface used by the shared sheaf tensor API.
- A sheaf of commutative rings: `O : Sheaf J CommRingCat.{u}`. `Coeff O` is
  exactly Mathlib's `SheafOfModules` for its underlying ring sheaf (the
  `mathlib_match` of def-weil-sheaf-of-modules-category and the body of the
  recorded `CategoryTheory.ringedSiteModules`, not a new module-sheaf notion).
- A sheaf dg algebra and its algebra map: `A B : Algebra O`, `φ : A ⟶ B`.
  `Algebra O = Mon (CochainComplex (Coeff O) ℤ)`. The existing direct-sum total
  tensor differential is `d(a)⊗b + (-1)^|a| a⊗d(b)`. Thus a monoid map is a
  degree-zero unital multiplicative chain map; algebra commutativity is not
  assumed. The ordinary cochain-complex differential already satisfies `d²=0`.
- Right dg modules: `Module A = Mod (Complex O)ᴹᵒᵖ (mop A.X)`. Reversing tensor
  order gives the actual right action `M⊗A→M` and its signed Leibniz rule.
  `underlying`, `action` and `actionDegree` are the existing module-object
  forgetful functor and action, not arbitrary complexes or maps.
- The localized category: `quasiIsomorphisms A` is exactly `QuasiIso` of the
  underlying chain map; `Derived A` is its formal-inverse localization, and
  `Q A` its actual localization functor. This is the equivalent direct model
  of the node's homotopy-then-quasi-isomorphism localization: a dg cylinder
  identifies homotopic maps after its projection becomes invertible.
  No arbitrary category together with an assumed equivalence is used.
- Standard triangulation: `ScalarSystem.source` and `.target` are
  `DerivedStructure A` and `DerivedStructure B`. Those fields include actual
  `Pretriangulated` and `IsTriangulated` structures on the fixed localization,
  with standard shift comparisons and `distinguished_iff`. The latter
  specifies exactly the isomorphic images of dg cone triangles.
  `ShiftComparison.action_eq` fixes the unchanged right action on shifts;
  `ConeComparison` fixes both projected actions, the inclusion and the signed
  Mathlib cochain-cone connecting map. `HEq` in its first projection only
  transports `(p+q)+1=(p+1)+q`, not a mathematical relaxation.
- Restriction: chain-level `restriction φ = Mod.comap φ.hom.mop` keeps its
  entire underlying complex and changes only the action. Therefore the same
  cohomology sheaves, underlying cone complex, inclusion and connecting map
  are retained. `ScalarModel.restrictionIso` factors this actual restriction
  through `Q B` and `Q A`. `.restrictionShift` and `.restrictionExact` assert
  shift compatibility and exactness of the derived functor.
- Ordinary tensor: `TensorPresentation` is the representing object for
  balanced right-B-linear maps out of the existing total tensor `M⊗_O B`.
  `IsBalanced` imposes both `(ma)⊗b=m⊗φ(a)b` and right B-linearity.
  This universal property determines the ordinary sheafified balanced tensor
  up to its unique map-preserving isomorphism. `OrdinaryExtension.tensor`
  specifies the universal maps at every object; `.naturality` fixes its maps.
  Its adjunction has unit `m↦m⊗1` and action counit `n⊗b↦nb`.
- Existence of derived extension: `Nonempty (ScalarSystem φ)` asserts that
  all this data exists. `.model.extension` and `.model.comparison` have
  `IsLeftDerivedFunctor` at precisely `quasiIsomorphisms A`, i.e. the total
  left derived/right Kan universal property. It is not an arbitrary left
  adjoint chosen instead of the derived tensor. `.extensionShift` and
  `.extensionExact` give exactness.
- Natural Hom bijection: `.model.adjunction : extension ⊣ restriction` has
  Mathlib's `Adjunction.homEquiv` and its naturality. The counit equation in
  `ScalarModel.counit` identifies its value at every actual module with the
  comparison followed by the localized ordinary action map, including the
  restriction-factorization transport. `inverseTranspose` is exactly
  `extension.map f ≫ adjunction.counit.app N` for every derived M, N and f.
- Restriction to open subspaces: `ringed_dg_scalar_adjunction_open` quantifies
  over `X : TopCat.{c}`, its open site essentially small relative to the
  independent coefficient universe u, its ring sheaf O, A, B, φ, a scalar model s,
  and every `U : Opens X`. `OpenScalarSystem` supplies the restricted dg
  algebras, map and scalar model, with `OpenCompatibility`.
  `overComplex` uses the existing `SheafOfModules.overFunctor` to the slice
  open site (canonically the opens of U). `OpenRestriction.algebraIso`,
  `.multiplication`, `.underlyingIso` and `.action` specify the genuine
  restriction on each section, including multiplication and module action.
  `.derivedIso` specifies its localized functor. `OpenCompatibility.map_eq`
  fixes φ on restriction; `.restrictionIso` and `.extensionIso` identify both
  scalar functors. `.unit` and `.counit` are the two commuting adjunction
  squares, so the adjunction maps themselves commute with restriction.
- Left modules: `opposite` uses the signed braiding of cochain complexes,
  `oppositeMap φ` is its functorial map, and `LeftModule A` is `Module (opposite A)`.
  Applying the universally quantified first theorem to `oppositeMap φ` and
  the open theorem to the corresponding opposite models gives every left
  assertion, including the Koszul conversion `ma=(-1)^(|m||a|)am`.

Dependency declarations read and used:

- def-weil-size-convention: the universe convention, no standalone Lean term.
- def-weil-sheaf-of-modules-category:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  its transparent body is the Mathlib `SheafOfModules` used here.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`. Its underlying cochain-complex and cohomology notions
  are reused. `DerivedCategory (Coeff O)` alone cannot encode a dg A-action,
  so the actual localization is formed at the action-preserving maps.
- def-weil-triangulated-category: Mathlib `Pretriangulated`, `IsTriangulated`,
  `Functor.CommShift` and `Functor.IsTriangulated`, used directly.
- The existing independent-universe tensor structure is
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, `.cochainModulesSymmetric` and
  `.cochainModulesPreadditive`. The complex tensor and its Koszul symmetry
  come from `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`.
- The general-site restriction uses
  `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`,
  `CategoryTheory.module_overFunctor_preservesZero`; it is not restated.
- Every already stated proof dependency is imported by its recorded module
  or Mathlib match, as a plain import: `Localization.Predicate`,
  `Localization.Triangulated`, `Functor.Derived.PointwiseLeftDerived`,
  `Functor.Derived.Adjunction`, and the upstream modules
  `DerivedCategory.ResolvingClassEssentialConstancy`,
  `DerivedCategory.LeftDerivedPointwiseKanBridge`,
  `LeftDerivedExactWhenDefined`, `DerivedCategory.EssentiallyConstantPro`,
  `NatTransFromResolvingClass`. The two sheaf-dg homotopy/resolution proof
  inputs do not yet have recorded Lean modules; their roles remain in the
  theorem's complete proof docstring.

Edge cases checked on the statements and definitions: zero coefficient ring;
zero module and zero algebra; empty space and empty open; the identity algebra
map; degree-zero ordinary algebras; unbounded complexes; negative shifts and
odd homogeneous degrees. No nonzero, flat, bounded, commutative-dg or connective
assumption has been inserted. In odd degrees the right action is unchanged by
shift, the cone first-component action uses degree p+1, and the opposite uses
Koszul symmetry. The cone differential and connecting-map signs are exactly
Mathlib's cochain convention. Neither tensor functor nor restriction is
replaced by an unconstrained functor.

Searches run with msearch.py (actual JSON results are in both new nodes):
LeanFinder, "Derived extension of scalars for sheaves of differential graded
algebras is left adjoint to restriction of scalars" (8 ordinary sheaf-module
adjunctions, no dg statement); Loogle, "DGAlgebra, DGModule" (unknown
DGAlgebra, zero hits); grep, "DGAlgebra|DGModule|DifferentialGraded" (zero hits);
LeanSearch, "Sheaves of differential graded modules extension restriction
derived adjunction" (8 hits, ordinary scalar/sheaf adjunctions and the generic
`Adjunction.derived`, which assumes the already constructed interfaces).
Read the generic derived-adjunction signature and the sheaf-module definitions.
`rg` in Mathlib, WeilConjectures and Sheaf, the upstream declaration-name table,
and the DAG found no general ringed-site right-dg interface or theorem.
`blueprint_refs.py search 'sheaf dg'` and `search 'ringed site dg'` gave zero
blueprint matches; `ancestor` returns null. Searches by the assigned node id
in WeilConjectures found no occurrence. The source was read in local sdga.tex,
including dg algebra/module definitions, shifts, cones, localization, derived
tensor and the identity-topos adjunction. The latest blueprint unit and the
node's premise chain were read. No source-based correction was required.

## New nodes

`def-sfb-ringed-site-dg-modules` defines the general ringed-site right dg
algebras/modules and the normalized scalar-system data, without asserting
existence. Its source is sdga, the definitions and constructions underlying
0FT5, 0FTF and 0FTR. The three search kinds above do not supply these notions.
The project's `CategoryTheory.DgAlgebra` specializes to complexes of ordinary
Z-modules, so it cannot express coefficient sheaves on an arbitrary site.
The existing `def-sfb-sheaf-dg-module-localization` is for left modules on a
topological space and includes homotopy/perfectness conventions; it has no
Lean declaration and does not supply the general ringed-site right-module
interface needed by this item. This new interface uses the same standard
cochain tensor and localization primitives; it does not define an alternative
notion of ordinary sheaf modules or of triangulated categories.

`def-sfb-ringed-site-dg-open-restriction` defines the distinct site-restriction
and comparison data for that interface. Its source is the restriction-to-opens
construction in sdga and the same tensor/action adjunction. It reuses
`overFunctor`; its new data specifies restricted dg actions and the adjunction
squares, which no existing ordinary-module restriction declaration supplies.
The new nodes contain the real universal maps and their characterizing
properties. Their structures do not assert their inhabitation. The item cites
both, and the second cites the first. There are no dependency-node repairs and
no statement corrections.

## Validation

All delivered files are compiled separately through the required scompile.py
wrapper against the published live library. The final deliver2.py dry run and
delivery also compile and run the server preflight. Only theorem `sorry`
warnings are permitted. No global build, direct git command, shared-source
write or launcher-script edit was used. No independent second reader was
started: this dispatcher brief prohibits additional agents and the maintainer
performs the independent delivery review.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
