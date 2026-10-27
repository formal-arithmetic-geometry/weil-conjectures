## Worker report

The module `Sheaf.CategoryTheory.CechAugmentationNormalizedNaturality` states
`lem-sfb-cech-augmentation-normalized-naturality`. Its recorded declarations, together,
render all clauses; the primary declaration is the resolution-lift/naturality theorem.
Every theorem proof is `sorry`. The named theorem `columnUnit_comm`
supplies the chain-condition proof needed by the real definition `columnUnit`. Definitions are explicit compositions of existing
functors and maps. There is no data chosen from an unproved existence theorem.
The node changes only in `lean`; no statement correction, new node or dependency
repair is required. No STATEMENT-DISPUTED issue was found.

### Hypotheses and objects

- The presented small sites are `{C X : Type u}`, `[SmallCategory C]`,
  `[SmallCategory X]`, `J : GrothendieckTopology C` and
  `L : GrothendieckTopology X`. This uses the Grothendieck-topology presentation
  of the sites supplied by `def-weil-pbc-sites-and-cohomology`.
- `R : Sheaf J RingCat.{u}` and `S : Sheaf L RingCat.{u}` are the coefficient
  sheaves. `_hR` and `_hS` express commutativity on every section; hence these
  are commutative ring sheaves without replacing the recorded RingCat interface.
- The module categories are the existing `ringedSiteModules.{u} R` and
  `ringedSiteModules.{u} S`, definitionally Mathlib's `SheafOfModules`.
- `f : RingedToposMorphism R S` is the recorded geometric morphism, with the
  induced module direct image `f.modules`. `[IsIso f.ringMap]` is the Cartesian
  coefficient identification. `fInverse`, its additive and finite-limit/colimit
  preservation instances, and `_fAdj : fInverse ⊣ f.modules` specify its exact
  module inverse image. A left adjoint to this fixed direct image is uniquely
  identified with the induced module pullback by its adjunction.
- `V : Sheaf J (Type u)` and `[Epi (terminal.from V)]` give the covering
  epimorphism; both V and W have this instance in `alpha_refinement`.
  A map `r : W ⟶ V` is automatically over the terminal sheaf.
- The canonical fibre powers, slice rings and actual restrictions are those of
  `sheafCoverNerve`, `elementRing`, `elementModulePullback`, and the recorded
  `CoherentCechImageModel R`. No representability assumption on V is imposed.
- `I : InjectiveResolution K` and `I' : InjectiveResolution K'` have the actual
  nonnegative complexes `cocomplex`, degreewise injectives, and the
  quasi-isomorphisms `ι` from `CochainComplex.single₀`.
- `HasDerivedCategory.{wX}`, `HasDerivedCategory.{wY}` and, for a slice,
  `HasDerivedCategory.{wA}` implement the size convention. These morphism
  universes are independent. `QN` is extension by zero along
  `ComplexShape.embeddingUpNat` followed by the existing `DerivedCategory.Q`.
  `Abelian.HasKInjectiveResolutions` is the existing computing infrastructure on
  the small-site module category (available from its Grothendieck abelianness);
  it is not a bounded or completed replacement for the ordinary derived category.
  Slice K-injective resolution existence is a conclusion of `slice_normalization`.
  The explicit `HasSheafify` and `WEqualsLocallyBijective` instance binders on
  J and L cache the ordinary small-site sheafification facts. Mathlib supplies
  both for these small sites; spelling them out prevents repeated reconstruction
  during elaboration and imposes no additional mathematical condition.
- Finite totals are exactly `D.totalFunctor`, `D.bicomplex` and `D.total` of the
  recorded coherent model. These use nonnegative indices, finite diagonals and
  the differential `d_Cech + (-1)^n d_I`, and then extension by zero to integers.

### Clauses

1. `augmentation_exists` states existence and uniqueness of b subject to
   `D.IsAugmentation G V I b`. That existing predicate specifies every component
   as G of the localization unit followed by the (0,q) summand inclusion.
2. `comparison G I` is e_I inverse, as an actual isomorphism: apply RF to
   Q of the resolution inclusion, use `rightDerivedFunctorObjQIso` on the
   K-injective extension of I, and use Q of `mapExtendIso` to identify the
   termwise model with the extended nonnegative model. The latter is necessary
   because G of a chosen zero object is canonically isomorphic to that zero,
   rather than definitionally equal. There is no arbitrary comparison iso.
3. `alpha D G V I b` is exactly `(comparison G I).hom` followed by QN(b).
   Its theorems always require the full `IsAugmentation` predicate.
4. The first conjunct of `cech_augmentation_normalized_naturality` is
   existence of t with `I.ι ≫ t = single₀.map u ≫ I'.ι` for every u.
   The second conjunct quantifies over **every** t satisfying this equation.
   It asserts both the actual chain augmentation square and
   `alpha_I ≫ Q(totalMap t) = RF(QN(single₀.map u)) ≫ alpha_J`.
5. `totalMap` is the existing total functor applied to t, extended by zero.
   `signed_total_homotopy` quantifies over every input `s : Homotopy t₀ t₁`
   and gives a homotopy between the actual total maps. Its inclusion equation
   is the whole map from the (n,q+1) summand into (n,q), with coefficient
   `((-1 : ℤ)^n) • G.map (((D.cochains V).map (s.hom (q+1) q)).f n)`.
   The separate bottom-row equation makes it zero from (n,0) to every degree.
   These equations specify the complete homotopy on every finite diagonal.
6. `lift_independence` asserts equality of Q(totalMap t₀) and Q(totalMap t₁)
   for any two lifts of u, without assuming a homotopy as extra input.
7. `resolution_comparison_laws` states `IsIso` for every identity lift between
   any two resolutions of K, and the identity and composition equations for
   the actual total maps. The primary naturality theorem with u = identity
   identifies their augmentations. Thus these are derived isomorphisms,
   not just maps on individual cohomology groups.
8. `refinement_laws` uses the existing `D.totalRefinement G r I`, which is
   induced by actual maps of Čech nerves and D's adjunction-characterized
   restrictions. It states the augmentation square, identity law,
   contravariant composition law, and commutation with every chain map t.
   These chain equations hold even without a covering condition; their
   specialization is exactly the node's refinement/comparison assertion.
   `alpha_refinement` states the displayed derived alpha equality for
   covering epimorphisms V and W and the same canonical comparison.
9. `columnUnit` applies G termwise to the existing localization augmentation
   natural transformation; it has no free map parameter.
   `projection_normalization` gives the actual chain projection to column zero:
   it is identity on each (0,q) summand and zero on every positive-column
   summand. It states `b ≫ π = columnUnit`, identifies this with G of the
   ordinary adjunction unit under `D.imageIso`, and states both its identity
   adjoint transpose and `pull(unit) ≫ counit = identity`, termwise.
10. `alpha_projection` requires the same identity/zero summand characterization
    of π and identifies projected alpha with the canonical comparison followed
    by QN(columnUnit). It does not take a transpose of a map on the target topos.
11. `SliceNormalization` packages the derived slice adjunction and its precise
    normalization; `slice_normalization` states its existence. The package
    includes additivity, exactness and slice K-injective resolutions as
    conclusions, and `restricted_injective` for every restricted resolution.
    `hom_formula` is the normalized derived Hom-transpose formula on actual
    chain maps. `unit_formula` identifies the derived unit with Q of the
    termwise unit, the canonical right-derived comparison, and the exact
    pullback factorization. `counit_formula` identifies the derived counit
    after that same comparison with Q of the termwise counit.
    `triangle` states the resulting derived normalization. The comparison on
    the restricted resolution is invertible because `restricted_injective`
    makes that complex K-injective. Together with `alpha_projection` and the
    ordinary column-unit equation, this is exactly the last clause of the node.

The component and law helpers are stated at the additive generality at which
these elementary identities hold. Specializing G to f.modules gives the fixed
ringed-topos statement, with all its geometric hypotheses present in the primary
declaration. No independent totalization, inverse image, slice site, module
category, or derived category is introduced. `SliceNormalization` is a package
of the conclusion of this node, not a new independent construction chosen from
mere existence. Its Hom formula fixes the derived adjunction normalization.

### Dependency declarations and sources read

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; for the resulting topology
  and its sheaves the statement uses Mathlib `GrothendieckTopology` and `Sheaf`.
- `def-weil-size-convention` is the recorded metatheoretic convention; there is
  no declaration to import. Explicit universes implement it here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `overMap` and `overFunctorMap` were read. For
  nonrepresentable V the statement uses the recorded element-site specialization.
- `Sheaf.CategoryTheory.RingedSheafSliceConstruction`: `elementProjection`,
  `elementTopology`, `elementRing`, `elementModulePullback`, `elementMap` and
  `elementModulePullbackOver`, re-exported by the coherent model.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`:
  `RingedSheafSliceAdjunctionData`, `ringed_sheaf_slice_adjunction`; supplies
  the exact localization and extension-by-zero adjunction in the proof plan.
- `Sheaf.CategoryTheory.CoherentCechImageModel`: `sheafCoverNerve`,
  `CoherentCechImageModel`, `cochains`, `bicomplex`, `totalFunctor`, `total`,
  `totalRefinement`, `IsAugmentation`, and its defining adjunction/unit fields.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`: the recorded
  double-complex interface, with Mathlib `HomologicalComplex₂.total`,
  `ιTotal`, and the nonnegative total functor used by the coherent model.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `Injective`, `InjectiveResolution`; comparison maps and homotopies are in
  `Mathlib.CategoryTheory.Abelian.Injective.Resolution`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
  and `.ShortExactPullback`: `Functor.rightDerivedFunctorObjQIso`,
  `rightDerivedFunctorUnitQ` and the existing `rightDerivedFunctor`.
  These are the universal unbounded right-derived pair; the recorded generic
  `rightDerivedFunctorOfQuasiIsoResolutions` interface is also imported as a
  proof dependency. No new right-derived functor is defined.
- `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`:
  `HomologicalComplex.mapExtendIso`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`, the termwise unit and counit.
- Proof imports also include the recorded
  `CochainComplex.homotopy_of_comp_quasiIso_of_injective`,
  `CategoryTheory.derivedAdjunctionOfResolvingClass` and
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- The proof-only nodes `lem-sfb-cech-injective-column-model` and
  `lem-weil-pbc-injective-resolution-lift-exists` had no Lean record at reading.
  Neither is needed to type this statement, so no phantom import is supplied.
  The comparison-lift clause is stated directly on Mathlib's actual resolutions.
  No downstream `DerivedCechImageTotalization` import is used: that node cites
  the present item, and adding its module would prevent its future proof import.

The source read was `literature/stacks-project/derived.tex`, the labelled
lemmas `lemma-derived-adjoint-functors` (09T5) and `lemma-K-injective` (070I),
and `literature/stacks-project/sites-modules.tex`,
`lemma-localize-ringed-topos` (04IE) and `lemma-relocalize-ringed-topos` (04J4).
The node's ten proof steps are distributed across the theorem docstrings.

### Edge cases

Checked zero modules and zero maps; no nonzero or characteristic assumption is
introduced. At total degree zero the only summand is (0,0), with vertical sign 1.
The signed homotopy is zero on resolution degree zero, including possible maps
to other Čech columns. For n odd the two horizontal terms have opposite signs;
for n even the same cancellation holds with reversed signs. Negative total
degrees are the canonical extension-by-zero terms. All remaining diagonals are
finite. Identity covers/refinements and composite refinements are explicit.
An initial covering sheaf in a degenerate topos is not excluded. Neither
nonemptiness of section sets nor representability of the cover is imposed.
The identity and arbitrary-lift cases are retained. A chain map over identity
need not be a strict isomorphism: only its image on total derived objects is
asserted to be invertible. Source and target derived morphism universes remain
independent, as does the slice-derived universe.

### Searches

The prescribed msearch wrapper was used for all three searches:

- LeanFinder query: `Derived Cech augmentation naturality in injective resolutions
  and refinements with localization counit normalization`. Eight hits, including
  `InjectiveResolution.toRightDerivedZero'_naturality`,
  `InjectiveResolution.isoRightDerivedObj_hom_naturality` and related statements.
  They concern individual derived functor values and do not state this signed
  total, refinement and counit-normalization result.
- Loogle query: `CategoryTheory.InjectiveResolution, Homotopy`. Four hits:
  `descIdHomotopy`, `descCompHomotopy`, `descHomotopyZero`, `descHomotopy`.
  They supply the resolution-comparison ingredients, not the total theorem.
- Mathlib grep query: `cech.*augmentation|Cech.*[Nn]aturality`, restricted to
  CategoryTheory, returned zero hits.
- Project `rg` searches covered `cech.*(augmentation|Augmentation)`,
  `Cech.*(Naturality|naturality)`, `cech_augmentation`, the node id, and the
  proposed namespace/declaration names in both `lean/WeilConjectures` and
  `lean/Sheaf`. Existing Čech augmentation naturality statements and the
  downstream `DerivedCechImageTotalization` module cover parts of the result,
  but none covers the complete node. No proposed full name was occupied.

Compilation is exclusively through the prescribed scompile.py wrapper. The
completed module compiled cleanly in sandbox mode (55.8 s) and library mode
(57.3 s), within the unchanged 60-second limit. Expected sorry diagnostics
are filtered by the wrapper; no other warnings or errors remain. The delivery
is checked again by deliver2.py --no-push before pushing.

## Second reading by Q58

This is a second pass by the same dispatcher worker; the task explicitly
prohibits starting another agent. The maintainer's independent reading remains
part of delivery review. I reread the node and the complete module together.

The primary theorem retains f, Cartesian coefficients, commutative ring sections,
exact module inverse image, covering epimorphism, actual resolutions and every
lift of u. The entire naturality square is an equality of derived morphisms.
The helper list is essential: the primary theorem alone does not claim to render
the node's homotopy, refinement or normalization clauses. Those are all named in
lean.declarations and matched above. The actual refinement direction is W -> V
and Tot(V) -> Tot(W), and composition is rho_r followed by rho_r'. The signed
homotopy formula uses resolution-degree descent with the Čech degree fixed.
The separate bottom-row clause rules out unmentioned terms when q=0.

I strengthened the characterization of the projection in alpha_projection to
include identity on the zero-column summands and zero on positive-column
summands, matching projection_normalization; it cannot be an arbitrary map
with only a condition on b. I also checked that the derived unit formula
includes the inverse exact-pullback comparison, while the derived counit
formula includes the forward comparison. The ordinary transpose is taken
before applying f_*, as the node requires. Exactness and K-injective existence
on the slice are conclusions in SliceNormalization, not added hypotheses.
No natural-language statement field changed.
