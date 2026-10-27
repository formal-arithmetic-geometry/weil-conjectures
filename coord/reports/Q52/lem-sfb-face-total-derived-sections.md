## Worker report

Q52 repair of immutable returned head `692a77926edd`, item
`lem-sfb-face-total-derived-sections`, stage 2.

The returned H3 is repaired by removing the old `Geometry` structure entirely.
The new shared definition node `def-sfb-enlarged-face-ringed-total-model` owns
`Sheaf.AlgebraicGeometry.EnlargedFaceRingedTotalModel`. Its
`CategoryTheory.EnlargedFaceRingedTotal.Model W` is the pinned model of the
actual enlarged étale diagram. The item's `Model` is just an abbreviation of
this shared declaration, not a second notion. The theorem now concludes
`Nonempty (Model W) ∧ ∀ G : Model W, ∃ R C, Nonempty (UnitCompatibility C)`.
In particular the heart-unit citer and sibling items can use the very same G;
they are not forced to identify a fresh existentially chosen category.

The sandbox node was regenerated from the current read-only main node, retaining
all current fields and adding only `lean` and permitted statement dependencies.
The general dependency `lem-sfb-semisimplicial-ringed-total-category` is not
modified or rebound. The item's mathematical statement is unchanged: the repair
makes its already specified enlarged-site category literal in Lean.

### Every hypothesis and clause

- Scheme and base algebraic space: explicit binders `S : Scheme.{u}` and
  `Z : AlgebraicSpace S`.
- Augmented semisimplicial algebraic space: `W : SemiSimplexCategoryᵒᵖ ⥤ Over Z`.
  Its nonempty ordinals and increasing injections have no degeneracy maps.
  Each object in `Over Z` retains its augmentation and all commuting triangles.
- Flatness on scheme charts: `flat_faces` and `flat_augmentation` use the existing
  `AlgebraicSpace.MapIsFlat`. Quantifying over all increasing injections is
  equivalent to quantifying over elementary faces, since they generate these
  arrows under composition, with identities flat as well.
- The actual enlarged ringed total category and augmentation: the shared `Model`
  fixes every object, arrow, covering, ring and structural comparison as described
  below. `G.rings.total G.sheaf`, `G.presentation`, and `G.total` are the recorded
  general total-site and augmentation interfaces. Existence of a model is asserted
  separately, and all following clauses hold for every model.
- Arbitrary module and arbitrary nonnegative injective resolution: all fields in
  `Computation` quantify over `M : (G.rings.total G.sheaf).modules` and every
  `I : InjectiveResolution M`. Its Mathlib `cocomplex` is nonnegative;
  `resolutionMap` extends it by actual zero terms to integer degrees.
- Every étale algebraic space V: `V : Z.EnlargedEtaleSite` with no restriction
  to scheme objects. `spaceSections` now literally forgets modules on the fixed
  enlarged ringed site and evaluates at `AsSmall.up.obj V`; it uses no freely
  supplied module equivalence. `G.sections` is this fixed section functor.
- Vp is the actual fibre product: `columnSections` evaluates on
  `AlgebraicSpace.enlargedBaseChange (W.obj p).hom V`.
  `G.componentEquivalence p` is defined by `modulesOfEq (G.fibres p)`, equality
  transport for the entire ringed site. It is not a field of Model.
- Whole derived comparison: `Computation.comparison` is an isomorphism of
  derived abelian-group objects between `RΓ(V)(Ra_*(single M))` and
  `localize ((model M I V).double.total (.up ℕ))`.
- Entire section double complex: `SectionModel.column` identifies each column
  as a complex with sections of the evaluated injective resolution, while
  `columnSections` identifies that section functor with the actual one at Vp.
- Actual transposed face maps: `Rows.transpose` is the inverse-adjunct formula
  using `presentation.transition` and augmentation composition. The displayed
  horizontal differential is exactly `SectionModel.horizontal`, the sum over
  `Fin (p+2)` with coefficient `(-1 : ℤ)^i.val`.
- Vertical differential: the column complex isomorphism retains the differential
  induced by I. `HomologicalComplex₂.total (.up ℕ)` uses `ε₁=1` and
  `ε₂=(-1)^p`, so its differential is dh+(-1)^p dv.
- Pth derived column: `columnDerived` retains an isomorphism of derived objects
  computing the right-derived column section functor on the exact derived
  component evaluation of M. The advisory that this field contains `Nonempty`
  of an isomorphism is acknowledged; its endpoints are the specified full
  derived column, not separate cohomology groups or arbitrary maps.
- Canonical normalization: `row_formula` pins the row augmentation by inclusion
  into bidegree (0,q). `row_quasiIso` asserts it is a quasi-isomorphism.
  `normalization` equates its localized composite with `comparison.inv` to the
  explicit `rowExtension.hom ≫ resolutionComparison`, using the actual
  right-derived units and inverse localized resolution map.
- Naturality in M and in V: `resolutionMap_column` and `resolution_naturality`
  retain the actual mapped resolution comparison under every module morphism.
  `restrictionMap_column` and `restriction_naturality` retain the actual sheaf
  restrictions and their right-derived natural transformation at every site arrow.
- Compatible replacements: `CompatibleReplacementInvariant` ranges over
  integer-indexed double complexes with p>=0 and q>=c for one common integer c.
  It provides totalizations and asserts the total of each whole-diagram column
  quasi-isomorphism is a quasi-isomorphism. `Computation.replacements` supplies
  this property. Inverting individual arrows in localization gives the required
  zigzags, with both directions and negative bounds included. No family of
  isolated cohomology groups is substituted for a compatible diagram.
- F=a*H and the canonical derived unit: `G.unit H` is explicitly Q of the actual
  ordinary adjunction unit, followed by the single-complex comparison and the
  right-derived unit of the actual augmentation direct image.
  `UnitCompatibility.formula` pins the augmented restriction in each degree
  through termwise adjunction and inclusion into column zero. `unit` equates
  its localization with `baseResolutionComparison ≫ RΓ.map (G.unit H)`.
  `replacement_unit` transports that same equation through a compatible
  quasi-isomorphic target replacement. Along with `replacements`, this gives
  the stated invariance under compatible common-bound zigzags.
- Detection: `Computation.detection` quantifies over every morphism of
  `DerivedCategory.Plus G.base.modules` and asserts invertibility if its derived
  section map at every enlarged étale object is invertible.
- There are no hypercover, quasi-coherence, nonemptiness, separatedness, or
  quasi-compactness hypotheses on the module, spaces, or diagram.

### The pinning required by H3

`Objects X` is `AsSmall.{u+1} X.EnlargedEtaleSite`, a literal object/arrow lift,
not a skeleton selected using an existence theorem. `coverage X` is the actual
chartwise-étale, jointly-surjective covering formula. `ringPresheaf X` is the
actual extended commutative regular-function sheaf, followed by the explicit
ring functor `liftRings`; its objects are ULift rings and its maps are lifted
ring homomorphisms. Thus `site X : Site.{u+1}` has prescribed C,J,ring.
The model uses the dependency's common size convention: modules and section
abelian groups have universe u+1, localization universe u+2. The lift is explicit
at every section and introduces no equality between different site universes.

`Model.objects`, `arrows`, `identities`, `compositions`, and `coverings` pin the
site pseudofunctor to these exact enlarged sites, actual `enlargedBaseChange`,
and exactly `enlargedIdentityIso`/`enlargedCompositionIso`. `fibres` identifies
the entire ringed fibre site with `site (W.obj p).left`. `cartesian_ring` fixes
all nonvertical ring restrictions using the lifted chart-normalized
`cotangentStructuralMap_existsUnique` map. Vertical restrictions are already
fixed by the fibre site equality. There is consequently no independent choice
of the total ring presheaf or its semilinear structure maps.

The reused `Presentation` pins face direct/inverse image, geometric adjunction,
ring map, unitors and compositors (`face_direct`, `face_inverse`,
`face_adjunction`, `face_ring`, `faceId_eq`, `faceComp_eq`). The existing scalar
insertion and representative normalizations pin module comparisons as well.

The base is literally `site Z`. `augmentation_direct` and
`augmentation_direct_map` fix base-change precomposition on every sheaf and
morphism. `augmentation_ring` fixes the adjoint structural map at every enlarged
object by the chart-normalized lifted map. `augmentation_direct_composition_eq`
pins the direct-image compositor by evaluating the inverse projection-preserving
site compositor contravariantly. This is the defining section formula of the
existing `enlargedDirectCompositionIso`, including its orientation.
`augmentation_comparison` is exactly its adjunction mate, not an arbitrary iso.
Finally `AugmentationPresentation` retains the dependency's normalized total
augmentation, component, and transition comparisons.

### Dependencies read and used

The original eight statement dependencies are retained and their recorded
signatures/docstrings were read. Main declarations reused include
`Scheme`, `AlgebraicSpace`, `InjectiveResolution`, `DerivedCategory`,
`HasDerivedCategory`, `HomologicalComplex₂.total`, `Flat`, and
`SemisimplicialRingedTotal.{Site,RingDiagram,Presentation,Augmentation,
AugmentationPresentation}`.
The existing landed node `def-sfb-space-morphism-properties` supplies
`MapIsFlat`. The prior delivery's direct addition of
`def-trf-space-etale-module-functors` is no longer needed and is removed: the
pinned model now uses the dependency's normalized scalar pullback directly,
rather than arbitrary comparisons to that module functor.

The new shared definition uses:
`Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` for
`enlargedCotangentStructure` and `cotangentStructuralMap_existsUnique`;
`Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization` for
`enlargedIdentityIso`, `enlargedCompositionIso`, and the defining formula of
`enlargedDirectCompositionIso`; and
`Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory` for the full normalized
site, systems, face and augmentation interfaces. The actual enlarged coverage
and fibre-product declarations come from the recorded enlarged-site module.

Statement dependencies are public imports. Existing proof-only imports remain
private. The main proof docstring gives the finite ordered-simplex contraction,
injective argument, signed total comparison, actual unit calculation, and
objectwise-section cone/sheafification detection argument.

### Edge cases and searches

Checked: p=0 has two cofaces with signs +1,-1; the one-vertex component is
included and the empty ordinal is absent. The finite-simplex contraction
includes m=0, p>m, and augmentation degree -1. Empty spaces, empty fibres,
empty covering families, zero modules and zero resolutions impose no excluded
case. Identity and composite arrows use the prescribed site unitors/compositors.
A constant identity diagram has alternating horizontal zero/identity maps.
Negative common internal bounds, odd shift signs, finite total diagonals,
and no horizontal upper bound remain included. `autoImplicit false` binds
every variable and universe explicitly.

The original searches (LeanFinder derived sections on flat semisimplicial
ringed total sites; Loogle total/injective resolutions; Mathlib grep;
LeanSearch semisimplicial total derived sections; direct rg in both source
libraries) found no exact comparison. The repair additionally searched for
existing shared `FppfFaceTotalModel`, `fppfFaceSite`, `SpaceFaceModuleSystems`,
`SpaceFaceRingedTotalCategory` and enlarged face-total models in DAG and both
Lean libraries. None was landed in the current read clone. The prescribed
server source lookups for NW/Q68 candidate module names also returned source
unavailable. No existing owner was bypassed. `blueprint_refs.py search enlarged
etale total` returned zero blueprint nodes; ancestor lookup returned None.
The new node contains the actual LeanFinder, Loogle, LeanSearch, Mathlib grep
and source/DAG grep records (including zero hits and unknown project name in
Mathlib-only Loogle) from this repair.

No `STATEMENT-DISPUTED` issue or mathematical statement correction is needed.
All data definitions have actual bodies. Only named proof obligations use sorry,
with source and natural-language proofs; the structural map choice is from the
existing unique chart-normalized characterization, not a mere Nonempty witness.

## New nodes

`def-sfb-enlarged-face-ringed-total-model` is a shared definition of the pinned
actual enlarged face ringed total site and coherent augmentation. It owns
`Sheaf.AlgebraicGeometry.EnlargedFaceRingedTotalModel`, including explicit size
transport and all geometric normalization fields. Its sources are Stacks
03G0/03G2/03G7/03G8 and 09WC/09WF/0D70/0D72, with injective-order-map indexing.
The search results above found no available landed NW/NP/Q68 owner, so this node
supplies the missing shared specialization without altering the general
semisimplicial total-category dependency.

## Second reading by Q52

A separate read-only worker, `/root/second_reading`, independently read the repaired
model, comparison module, dependency interfaces and Stacks
`spaces-simplicial.tex` lines 2060–2225 (0D7B/0D7C/0D7D/0D7F). This review was
started specifically to satisfy the return's explicit requirement of a real
independent second reading. It did not run compiler commands; compilation is
separate evidence from this worker.

The independent reader confirmed that the enlarged coverage is literal, the
structural-map choice uses a valid unique characterization, the direct-image
composition orientation is correct, the existing Presentation supplies the face
and scalar pins, and equality of entire ringed fibres replaces free module
equivalences. It confirmed that the universal conclusion allows the heart-unit
citer to share exactly the same G. It checked the ordered finite-simplex
adaptation and found no source correction necessary. It identified stale
coefficient-universe docstrings and a Grothendieck size annotation left from the
old model; both were corrected during the repair.
