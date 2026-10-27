## Worker report

The module `Sheaf.CategoryTheory.GlobalModuleAbelianCohomology` states
`CategoryTheory.CoefficientDerivedSections.global_module_abelian_cohomology`.
Its only theorem has proof `sorry`; it introduces no definitions or axioms.
The node's statement, dependencies, and proof remain unchanged.

Source checked: `literature/stacks-project/sites-cohomology.tex`,
`lemma-cohomology-modules-abelian-agree` (Tag 03FD), first equality. The source
explicitly treats the case without a final site object at the end of its proof.
The node's accepted four-step proof is included in the theorem docstring.

Hypotheses and clauses, matched to Lean:

- A small site in the common coefficient universe is `{C : Type u}` with
  `[SmallCategory C]` and `J : GrothendieckTopology C`. The recorded
  `Precoverage.IsSiteForCoverings` interface presents sites by actual coverings;
  `J` is their associated Grothendieck topology, retaining exactly their sheaves.
  Working with the resulting topology requires no extra site axiom. Objects,
  arrows, module sections, and ring sections all lie in the common universe `u`.
  The chosen localization morphism universes `w` and `z` are independent explicit
  universes, with `HasDerivedCategory` witnesses for the two derived categories.
  These are the size convention and the existence of the localizations, rather
  than restrictions on coefficient rings or sheaves.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`.
  `F : coefficientModules R` is exactly the recorded `ringedSiteModules`
  specialization to the underlying ring sheaf of `R`.
- The underlying abelian sheaf is `(SheafOfModules.toSheaf _).obj F`.
  Module morphisms use this same forgetful functor, never a second category.
- Global sections are the existing `coefficientSections R`, transparently
  `SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}`.
  `Sheaf.Γ` is the right adjoint to the constant sheaf functor and is canonically
  the limit of the underlying presheaf, hence the compatible families required
  by the node. There is no `HasTerminal C` assumption.
- The node says to let `RΓ` be the unbounded right derived functor.
  `H : DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u}`
  with the unit `η` and `[H.IsRightDerivedFunctor η (HomologicalComplex.quasiIso ...)]`
  makes this precise, using Mathlib's localization/left Kan extension definition.
  These parameters specify what `RΓ` means, rather than assuming the desired
  comparison. `coefficientComplexSections R` is termwise global sections.
  Uniqueness of right derived functors identifies this presentation with the
  K-injective construction underlying the recorded zeroth-hypercohomology
  definition. In particular the unit is invertible on K-injective complexes.
- Nonnegative integer degrees are `n : ℕ`, embedded in `ℤ` on the unbounded side.
  This covers every integer `n ≥ 0`, including zero.
- `DerivedCategory.singleFunctor (coefficientModules R) 0` embeds `F` as `F[0]`.
  The functor on the left of `e n` is this embedding followed by `H` and
  `DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)`.
- The right side of `e n` is `SheafOfModules.toSheaf _ ⋙
  (Sheaf.Γ J AddCommGrpCat.{u}).rightDerived n`. Mathlib's `Functor.rightDerived`
  uses injective resolutions of abelian sheaves, as requested; enough injectives
  is inferred from their Grothendieck abelian category instance.
- `e : ∀ n : ℕ, ... ≅ ...` gives natural isomorphisms of functors into
  `AddCommGrpCat`. Thus every component is an additive isomorphism and the
  comparison is natural in every module morphism.
- The first equation identifies the degree-zero augmentations. Starting from
  `Γ(F)`, the inverse single-complex homology isomorphism, the inverse
  single/map-complex comparison, and `homologyFunctorFactors.inv` identify
  ordinary sections with `H⁰(Q Γ(F[0]))`. Applying `H⁰(η)` and `(e 0).hom`
  equals the ordinary abelian `toRightDerivedZero`. Consequently under the
  canonical degree-zero identifications the comparison is the identity on
  the very same compatible families, rather than an unspecified isomorphism.
- A global scalar is `a : RingCat.sectionsSubring (R.obj ⋙ forget₂ ... )`,
  literally a compatible family of ring sections. Its module endomorphism is
  `SheafOfModules.Hom.mk (PresheafOfModules.sectionsSMul F.val a)`.
  The existing construction acts at each object by `a(U) • x`; commutativity of
  `R` makes it linear. The second equation says that `(e n).hom.app F`
  intertwines the functorial action of this endomorphism on the two sides.
  This is precisely the node's specified global-scalar linearity.
- Canonicity is fixed in every degree by the last equation. `I` is any module
  injective resolution and `K` any abelian injective resolution of `F_ab`.
  `φ` is any chain map from the forgotten `I.cochainComplex` to
  `K.cochainComplex` commuting with the original augmentations; the displayed
  hypothesis inserts only the canonical single-complex/forgetting comparison.
  The left composite passes through `Hⁿ(η_I)`, inverts `H(Q I.ι')`, applies
  `e n`, and uses `K.isoRightDerivedObjCochainComplex`.
  It equals the homology map of the sectionwise chain map `Γ(φ)`, after the
  standard localization-to-complex homology identification. Thus the iso is the
  comparison computed by all compatible resolution lifts. This spells out
  “canonical” and the node's third and fourth proof steps, rather than imposing
  a separate mathematical conclusion. The inverse of `Q I.ι'` exists because
  the augmentation is a quasi-isomorphism; no forgotten injectivity is used.
- There is no flatness assumption, no injectivity assumption on `F_ab`, and
  no acyclicity assumption on `F`. The resolution objects in the canonical
  formula are universally quantified tests of the comparison, not hypotheses
  restricting `F`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its associated topology uses
  the usual `GrothendieckTopology` and `Sheaf` definitions.
- `def-weil-size-convention` is explicitly a metatheoretic convention, with no
  declaration to import; the universes and localization binders implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`:
  `coefficientModules`, `coefficientSections`, `coefficientComplexSections`, and
  the proof input `derivedSectionsScalarCoherence`, all in namespace
  `CategoryTheory.CoefficientDerivedSections`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` and `CochainComplex.isKInjective_of_injective`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, which composes the
  K-injective right derived global sections construction with zeroth homology.
  This module publicly exposes the construction underlying the meaning of `H`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`,
  `Functor.toRightDerivedZero`, `InjectiveResolution.isoRightDerivedObj`, and its
  naturality/map formulas. `rightDerived` is used on the right, not `Sheaf.H`,
  because the node specifically chooses the injective-resolution definition.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `Mathlib.CategoryTheory.Abelian.Injective.Resolution`: `Injective`,
  `InjectiveResolution`, and resolution lifting; their extended integer-indexed
  complexes and quasi-isomorphisms are `I.cochainComplex` and `I.ι'`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`:
  `InjectiveResolution.isoRightDerivedObjCochainComplex`, the existing bridge
  from the natural-number resolution definition to its extended complex.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`:
  `PresheafOfModules.sectionsSMul`.
- The proof imports retain the accepted plan: `constantSheaf`,
  `sheafification_sections_local`, equivalence preservation of injectivity,
  enough injectives, bounded-below K-injectivity, and resolution lifts.

Edge cases checked before writing: the empty site (all compatible families and
cohomology groups are trivial), a site without a terminal object (only the
constant-sheaf right adjoint is used), objects with empty coverings (the sheaf
condition and compatible families still apply), zero coefficient ring and zero
module, the point site with `R = ℤ/nℤ` (no integer flatness can be assumed),
`n = 0` (the explicit augmentation equation), and arbitrary larger coefficient
universes. A site small within a larger common universe is obtained by lifting
its small model into that universe; the statement imposes no equality between
unrelated geometric-site universes.

Searches, before writing:

- LeanFinder through `msearch.py`: “Cohomology of derived global sections of a
  sheaf of modules agrees naturally with the cohomology of the underlying
  abelian sheaf”. Eight hits: `Sheaf.H`, cohomology presheaves, and Ext-resolution
  identifications; no global module/abelian comparison.
- Loogle through `msearch.py`: `SheafOfModules.toSheaf, rightDerived`.
  Zero hits; the service reports that the unqualified identifier `rightDerived`
  is unknown. Read its actual namespaced declaration in the pinned source.
- LeanSearch through `msearch.py`: “Global cohomology of a sheaf of modules
  equals that of its underlying sheaf of abelian groups”. Eight hits on
  forgetting module structures and `Sheaf.H`; none state this comparison.
- Mathlib grep through `msearch.py`: `cohomology.*forget|forget.*cohomology|
  toSheaf.*rightDerived`, subdirectory `CategoryTheory`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for global/abelian
  cohomology, derived sections, and the exact node id: existing evaluation
  comparisons and references in future proofs, no matching global statement.
  Read `ModuleAbelianEvaluationComparison.lean`: it evaluates at an object and
  cannot be substituted on sites without a final object. Read the scalar
  comparison and zeroth-hypercohomology sources in full; reuse their notions.

No new nodes, dependency repairs, statement corrections, or disputed claims.
Validation: `scompile.py` compiles the module on the server in module mode,
against the published live library. No local or global library build was run.

## Second reading by Q141

Self-check only; no second worker was started, as required by the dispatch brief.
The maintainer supplies the independent review. Reopened the original statement
and the final file and checked all binders and all three equations. The first
compile exposed a precedence error in the scalar equation; parenthesizing the
right-derived functor before `.map` repaired it. Added the compatible-resolution
formula to distinguish the canonical comparison in higher degrees. The formulas
all have the expected direction: unit from ordinary to derived, inverse
localization of the module resolution toward `F[0]`, comparison toward abelian
cohomology, and the abelian resolution iso toward homology of `Γ(K)`.
The node's natural-language statement remains verbatim and its only changed
field is `lean`. Every variable and universe is explicitly bound; the file sets
`autoImplicit false`. Its sole `sorry` belongs to the named theorem with the
accepted four-step source proof in its docstring.
