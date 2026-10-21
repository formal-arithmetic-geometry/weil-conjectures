## Worker report

The delivery states `AlgebraicGeometry.ProEtale.proEtaleInjectiveSupportGlobalModel`
in `Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel`. Its single proof is
`sorry`. There are no new definitions, dependency repairs, or statement corrections.
The item's JSON changes only in `lean`.

The theorem includes the sheaf adjunction with its specified counit, preservation of
injectives, the canonical natural identification of global supported sections, the
natural derived comparison, and its normalization on every injective model by the
standard right-derived units. These normalization equations exclude arbitrary
isomorphisms of the same objects.

Hypothesis and clause correspondence:

- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
- Schemes and the two immersions: `{X Z U : Scheme.{u}}`, `(i : Z ⟶ X)`,
  `(j : U ⟶ X)`, `[IsClosedImmersion i]`, `[IsOpenImmersion j]`.
- Quasi-compact complementary open: `[QuasiCompact j]` and
  `hPair : IsCompl (Set.range i) (Set.range j)`. No Noetherian, separated,
  quasi-compact-X, or constructibility assumption is imposed.
- All ordinary constant-A module sheaves: `Sheaf (Scheme.ProEt.topology T)
  (ModuleCat.{u + 1} A)`. This is exactly the presentation already used by
  `def-pur-flasque-support` and `lem-pur-support-localization-triangle`.
  The recorded `finiteCoefficientRealization T A` is an equivalence with
  `FiniteCoefficientModules T A`; this delivery introduces no second module category.
- Exact i_* and i^*, j^*: the published finite-coefficient `lowerStar`/`upperStar`
  operations, imported through the recorded constant-ring operations and supported
  kernel modules. Exactness is supplied by the dependencies, not added as a hypothesis.
- i^!₀M = i^*ker(M → j_*j^*M): the existing `finiteClosedUpperShriek A i j`.
- S = Ri^!₀ on D⁺: `(finiteClosedUpperShriek A i j).rightDerivedFunctorPlus`.
  The support counit is the existing `supportModelInclusion A i j hPair`, obtained
  from inverse canonical supported comparison followed by kernel inclusion.
  This is the sheaf counit whose derived form appears in the localization triangle.
- Right adjunction and injective preservation: `∃ adj : lowerStar ... i ⊣
  finiteClosedUpperShriek A i j`, `adj.counit = supportModelInclusion ...`, and
  `(finiteClosedUpperShriek A i j).PreservesInjectiveObjects`.
- Every bounded-below injective representative: `I : HomotopyCategory.Plus ...`
  and `(∀ r : ℤ, Injective (I.obj.as.X r))`. Mathlib's homotopy category keeps the
  underlying complex in `.as`, so this quantifies over all such complexes and their
  chain maps modulo homotopy. Every bounded-below complex is included through
  `HomotopyCategory.Plus.quotient`. Any isomorphism `Qh I ≅ K` transports the
  displayed computation to that K by functoriality.
- Same lower bound: `∀ n : ℤ, CochainComplex.IsStrictlyGE I.obj.as n →
  CochainComplex.IsStrictlyGE (F.mapHomologicalComplex ... |>.obj I.obj.as) n`.
- Termwise injective i^!₀I: the following `∀ r : ℤ, Injective (... .X r)` clause.
- Represents SK: `IsIso (F.rightDerivedFunctorPlusUnit.app I)`, with
  F = `finiteClosedUpperShriek A i j`. This is the standard unit from
  `Qh(FI)` to `S(Qh I)`, not an arbitrary representative isomorphism.
- Computes derived global sections: the next `IsIso` is the global-section
  right-derived unit at `F.mapHomotopyCategoryPlus.obj I`. Its target is
  `RΓ(Z,Qh(FI))`; applying RΓ to the preceding unit gives `RΓ(Z,S(Qh I))`.
- Γ(Z,i^!₀I) = Γ(X,i_*i^!₀I) = ker(I(X) → I(U)) = Γ_Z(X,I):
  `c : F ⋙ Sheaf.Γ ... Z ... ≅ supportSections i A`. Its normalization, for
  every sheaf M, reads: c followed by the actual `kernel.ι` of restriction is
  `(globalSectionsLowerStarIso ... i).inv.app (F.obj M)`, followed by global
  sections of `supportModelInclusion`, followed by terminal evaluation
  `Sheaf.ΓNatIsoSheafSections`. Thus all three links are fixed by the actual
  direct-image, support, and restriction constructions. `supportSections i A`
  is exactly the recorded kernel-of-restriction functor, using the canonical
  open complement of i. Since j has the same complementary image, the equality
  of kernels is the canonical one for the same support.
- Equality of complexes and naturality in chain maps: apply
  `NatIso.mapHomologicalComplex c (.up ℤ)`, together with
  `Functor.mapHomologicalComplexCompIso`. A natural isomorphism of additive
  functors acts termwise, so its chain differential is the image of d_I, and
  its chain maps commute with every given chain map. These are structural
  consequences of the type of c, not new assumptions. As the node's proof step 5
  specifies, 'equality' here means canonical identifications, rather than literal
  equality between carriers chosen by different categorical limit constructions.
- Consequently canonical natural RΓ(Z,SK) ≅ RΓ_Z(X,K): e is a natural isomorphism
  from `F.rightDerivedFunctorPlus ⋙ ΓZ.rightDerivedFunctorPlus` to the recorded
  `derivedSupportSections i A`. The last equality fixes it on all injective models:
  `αΓ(FI) ≫ RΓ(αF(I)) ≫ e(Qh I) = Qh(c_I) ≫ αSupport(I)`.
  `Functor.mapHomotopyCategoryPlusCompIso c` is the canonical termwise identification
  on the right. All three α are asserted invertible, including the supported-section
  one. Thus solving this equation gives exactly the inverse-comparison/chain-map/
  comparison construction in node proof step 6. K-injective Hom comparison extends
  this naturally to all derived objects, as in node step 7.
- Degree r in ℤ yields an isomorphism of A-modules: applying the existing
  `DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) r` to `e.app K`
  is a `ModuleCat A` isomorphism. Nothing identifies a module with a sheaf.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`; only the latter is required here.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategoryPlus`,
  `finiteCoefficientRealization`, `finiteCoefficientRealization_isEquivalence_ring`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the constant-ring
  comparison, pullback/pushforward and adjunction, reexporting the published
  finite-coefficient operations. The theorem follows the finite sheaf presentation
  used by the recorded support dependencies; it does not use the Type-u-only
  arbitrary-ring abbreviation to restrict the Type-(u+1) coefficient ring.
- `Sheaf.AlgebraicGeometry.ProEtalePairFlasque`: `finiteSupportedClosedComparison`,
  `finiteSupportedSections_sections`, `finiteSupportedClosedComparison_isIso`.
  Its imported `ProEtaleSupportedSections` supplies `finiteSupportedSections`,
  `finiteSupportedSectionsι`, `finiteClosedUpperShriek`.
- `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`: `supportClosedDerivedPlus`,
  `supportShriekModelComparison`, `supportLocalizationTriangle`. Its public
  dependency `SupportTriangleConstruction` supplies `supportModelInclusion` and
  the additive support-functor instances. The sheaf adjunction in this module is
  private, so it is not a usable existing statement of this full node.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `Sheaf.supportedSectionsFunctor`, `ProEtale.supportRestrictionArrow`,
  `ProEtale.supportSections`, `ProEtale.derivedSupportSections`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `.TStructure`: `DerivedCategory.Plus`.
- Proof imports include the recorded `RingedSiteModulesGrothendieckOfUniverses`
  (`SheafOfModules.isGrothendieckAbelianOfUniverses`), `ProEtaleRingedOpenClosed`
  (`Scheme.proEtale_ringed_open_closed`), the closed full-faithfulness declaration
  reexported by `SupportLocalizationTriangle`, and the Mathlib enough-injectives,
  bounded-below injective-representative and K-injective Hom modules.
  The recorded right-adjoint injective-preservation module is imported explicitly.
- Additional existing canonical infrastructure: finite-coefficient
  `.UpperLowerStar.GlobalSections`, `globalSectionsLowerStarIso`; upstream
  `.Mathlib.CategoryTheory.Sites.GlobalSections`, `Sheaf.Γ_additive`;
  Mathlib `Functor.rightDerivedFunctorPlus`, `.rightDerivedFunctorPlusUnit`,
  `Functor.mapHomotopyCategoryPlusCompIso`.

Edge cases checked before writing:

- Z empty: both supported sheaves and supported sections are zero; c and e are the
  unique isomorphisms of the corresponding zero functors.
- Z = X and U empty: supported kernel and closed inverse image are identity up to
  the published canonical comparisons; c reduces to Γ, and e to its derived version.
- X empty, zero complexes, and the zero coefficient ring are allowed. No `Nontrivial`
  or `Nonempty` hypotheses occur.
- Arbitrary integer lower bounds, their negative shifts, and all cohomological
  integer degrees are allowed; no concentration in degrees ≥ 0 is imposed.
- A disconnected X and a closed component give the expected projection to the closed
  component. No connectedness condition or choice of splitting occurs.
- Non-quasi-compact complements are correctly excluded by the stated `[QuasiCompact j]`.
  X itself is unrestricted. Site object universe u+1, morphism universe u, and
  module/coefficient universe u+1 follow the recorded support interfaces.

Searches (run with the prescribed msearch.py wrapper):

- leanfinder: "Closed immersion supported inverse image preserves injectives and
  derived global sections agree with derived sections with support". Eight unrelated
  scheme-image, open-restriction and ideal-sheaf hits; no statement match.
- loogle: `"PreservesInjectiveObjects"`. Eleven generic injective-preservation results,
  including `Functor.PreservesInjectiveObjects` and the adjunction preservation
  theorem; none states the supported-global-section comparison.
- grep in Mathlib/AlgebraicGeometry:
  `sectionsWithSupport|support.*[Ii]njective|[Ii]njective.*support`. Two unrelated
  injective-coercion hits in ClosedImmersion and IdealSheaf; no match.
- leansearch: "A closed immersion supported inverse image preserves injectives and
  its derived global sections are derived sections with support". Eight closed
  immersion/image lemmas; no match.
- rg in the project's WeilConjectures and Sheaf trees: supported-section,
  support/injective and global-comparison expressions. The existing supported kernel,
  closed restriction, global direct-image and private underived comparison are reused
  or identified above. `ProEtaleSupportedExteriorProduct` contains a private
  `normalization_closedUpperShriekCompΓIso` for its separate supported coefficient
  adjunction; it does not expose or state this complete injective-model theorem.
  `RetractedSupportLocalizationComparison` describes the downstream comparison,
  not the present generic injective-model calculation.
- The exact item-id search in WeilConjectures returns no declaration.

Sources read: Stacks etale-cohomology.tex, section-cohomology-support (09XP), and
lemma-sections-with-support-acyclic (09XQ), including the full Hom proof. Also read
all statement-dependency node statements and recorded signatures/docstrings, the
proof-dependency records, coord/pefw-upstream-framework.md, and the stage rules.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: all compilation is through scompile.py; no direct git command, library
edit, global build, or launcher-script edit was made. Final compile and delivery
preflight results are recorded below after they complete.

## Worker self-review

A second in-thread read checked both normalization equations and their source and
target objects. The global-section c points from Γ(Z,i^!₀M) to the kernel, while
`globalSectionsLowerStarIso.inv` points to Γ(X,i_*i^!₀M), as required. The derived
unit equation starts at QΓ(Z,i^!₀I) and ends at RΓ_Z(X,QI) on both sides.
No independent agent was started, as required by the dispatcher; the maintainer's
independent review remains the delivery review.

## Validation results

- scompile.py passed the sandbox check in 31.0 seconds and the standalone library
  module check in 35.1 seconds, with no errors or warnings.
- deliver2.py --no-push returned `OK (dry run)` at temporary commit b0b7bbe8d65:
  maintainer preflight and per-file compilation both passed, with nothing pushed.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
