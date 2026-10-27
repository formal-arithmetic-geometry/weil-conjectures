## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOrbitPairFiniteNorm` states
`AlgebraicGeometry.Scheme.Modules.proper_orbit_pair_finite_norm`, with its proof `sorry`.
It retains the node statement. Only `lean` and the addition of the already landed
`def-sfb-pencil-orbit-bundle-norm` to `stmt_deps` are changed. No new node, dependency repair,
or statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any field F: `(F : Type u) [Field F]`. A proper F-scheme:
  `(Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of F)) [IsProper p]`.
- Any finite group acting by F-automorphisms: `(G : Type v) [Group G] [Finite G]`,
  `(ρ : G →* Aut Y)`, and `hρ : ∀ g, (ρ g).hom ≫ p = p`. No injectivity hypothesis.
  Mathlib's multiplication on Aut is reverse categorical composition, so `ρ (g*h)`
  is g after h, exactly the source's left action convention.
- Any invertible module and two global sections: `(M : Y.Modules) [M.IsInvertible]`
  and `(a b : M.sections)`. The existing equivalence between compatible section families
  and top-open sections identifies these with Γ(Y,M).
- `U V : Y.Opens`, `hU`, `hV` identify the opens with `nonvanishingLocus M` of the two
  top-open values. This existing locus is the complement of maximal-ideal times the stalk,
  equivalently nonzero residue-field value. `haffU`, `haffV : IsAffineOpen ...` are precisely
  the two affineness assumptions. They do not assume any other open is affine.
- `hsep : Disjoint (⋃ g, ...) (⋃ g, ...)` is the disjointness of the two inverse-image
  unions of complementary loci, exactly the two orbit zero loci.
- C is the existing `pencilOrbitBundle (fun g ↦ ρ g) M`, constructed from the full finite
  enumeration `pencilGroupElements G` and the actual pullback/sheaf tensor, including a
  unit tail. The parentheses differ from the proof's convenient left parentheses only by
  canonical associators/unitors; the node's C has no prescribed parentheses. A and D are
  `orbitTensorNormSection ... a/b`. This helper applies `unitHomEquiv` and
  `homOfGlobalSection` to the existing `pencilTranslateSection`, changing only the global
  section encoding; it does not choose a section or define another tensor product.
- `∃ hC : C.IsInvertible` proves the asserted invertibility, with the proof explicitly
  passed to `pencilCoordinateMorphism`. `hab` and `hAD` are the two `Epi` assertions for
  `freeHomEquiv.symm (pencilSectionPair ...)`, precisely generation by the two indicated
  sections, using the recorded generating-sections definition. These are conclusions,
  not extra assumptions.
- The first two conjuncts after these witnesses are exactly Z(A) and Z(D) equal to the
  two orbit zero unions. They use `nonvanishingLocus` complements on both sides.
- The next two conjuncts assert `IsFinite` of the ordinary and norm coordinate morphisms.
  `pencilCoordinateMorphism` is just the existing
  `ProjectiveSpace.homOfGeneratingSections (ULift (Fin 2))` with its explicit invertibility
  proof, so these are exactly [a:b] and [A:D], over Spec F.
- The next two conjuncts give inverse-image equalities with U and V as `Y.Opens` at
  standard coordinate indices 0 and 1. The following `∀ i : ULift (Fin 2)` gives both norm
  chart equalities as `⨅ g, (ρ g).hom ⁻¹ᵁ (if i.down = 0 then U else V)`. There are exactly
  two indices, so this is exactly the two requested equalities. These are equalities of
  open-subscheme data, rather than merely equality of the underlying sets.
- The following `∀ i` states `IsAffineOpen` of both ordinary and norm chart inverse
  images, accounting for all four opens. Combined with the chart equalities this gives
  affineness of U, V, and both translated intersections.
- For every h, `orbitTensorPullbackReindexIso ρ M h (pencilGroupElements G)` is built
  recursively from `boundaryPullbackTensorIso`, canonical pullback composition
  `tensorPullbackSectionComp`, the action's actual `map_mul` equation, and the unit
  comparison. Its target is the same list with each label g replaced by g*h.
- The existential isomorphism e from that relabelled list to the original list must satisfy
  `PencilTensorPermutation`. This inductive Prop admits only identity on the empty list,
  tensoring on the left, adjacent braiding with associators, and composition. Its indices
  preserve the labels even if their automorphisms coincide. Thus e is an actual symmetric
  tensor permutation with the specified source and target; coherence ensures this is the
  canonical factor permutation. It is not an arbitrary isomorphism characterized only by
  A and D. The composite with the explicitly constructed pullback-reindex map is the
  stated canonical isomorphism h*C ≅ C.
- Its two displayed section equations send the actual normalized pullbacks of A and D
  to A and D. The final equality is `(ρ h).hom ≫ f_N = f_N` in the category of schemes.
  This includes the full scheme structure, not just pointwise equality.
- No ampleness, dimension, reducedness, smoothness, faithfulness, or nonemptiness condition
  is imposed.

Dependency declarations read and used:

- Mathlib: `Field`; `AlgebraicGeometry.Scheme` and its Hom; `IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField`;
  `IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`;
  `SheafOfModules.GeneratingSections` (the Epi/freeHomEquiv form) in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and the monoidal/symmetric instances for Y.Modules.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and `tensorPullbackSectionComp`, with
  the underlying actual `tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` retains the recorded
  ordinary sheafification tensor from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`:
  `SheafOfModules.monoidalCategory`, `symmetricCategory`. The Y.Modules tensor uses this
  same ordinary tensor; no cochain object is substituted.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `ProjectiveSpace.homOfGeneratingSections` is the coordinate construction wrapped by
  `pencilCoordinateMorphism`. `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections`
  exports `ProjectiveSpace.standardOpen` publicly for the displayed chart assertions.
- Landed `def-sfb-pencil-orbit-bundle-norm`, in
  `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`: `pencilGroupElements`,
  `pencilTranslateTensor`, `pencilOrbitBundle`, `pencilTranslateSection`. The same unchanged
  module supplies `pencilSectionPair` and `pencilCoordinateMorphism`; these only package
  the existing pair and projective construction. Its existence theorem is not used.
- The same public import provides `boundaryPullbackTensorIso` and
  `boundaryPullbackComparison` from
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`; these definitions
  use canonical left-adjoint uniqueness and the monoidal ordinary pullback, with no
  square-zero assumption on these two generic comparison definitions.
- All stated proof dependencies are present through the explicit proof imports, the
  imported parent module, and their upstream imports: invertible_pullback_tensor,
  nonvanishing_tensorPullback, tensor_section_affine_open,
  invertible_generating_sections_fibre_criterion,
  homOfGeneratingSections_chart_preimage, projectiveSpace_standardCharts,
  projectiveSpace_functor_of_points, and the symmetric sheaf monoidal structure.
  The Mathlib leaves are `isAffineHom_iff`/`HasAffineProperty.iff_of_openCover`,
  `IsProper.of_comp`, and `IsFinite.iff_isProper_and_isAffineHom`; projective properness is
  `ProjectiveSpace.instIsProper` in the already imported projective-space framework.

Import-cycle packaging note: the existing orbit definitions are still housed in
AmpleCurveTwoSectionPencil together with a theorem whose DAG proof now uses this item.
The new module necessarily imports that unchanged definition-owning module. A future
maintainer proof-import addition from that parent back to this module must be omitted
under stage 2 §3(7)'s cycle exception (or the definitions moved by a separately authorized
library repair). No base module is edited or duplicate orbit construction introduced.

Edge cases checked before writing: the empty scheme satisfies the same assertion with no
Nonempty binder; the zero section has empty nonvanishing locus, so on a nonempty Y the
separation assumption forces the other orbit zero union empty; the argument and statement
still apply. A group is nonempty by its identity, including the trivial group; its unit-tail
norm is the original module/section up to canonical unitors. Nonfaithful actions leave all
indexed factors present, and permutation labels are not collapsed. Positive characteristic,
finite fields, nilpotents, and arbitrary dimension are unrestricted. The group universe v
is independent of scheme/field universe u, and finiteness prevents any index-size issue.
Aut multiplication was read directly (`Aut_mul_def`) to verify the g*h direction.

Searches for an existing statement and duplicate helpers:

- `msearch.py ... leanfinder` query: "A finite group action on a proper scheme and an orbit
  separated pair of line bundle sections with affine nonvanishing opens yield finite
  invariant norm coordinate maps to the projective line". Eight hits: affine-limit section
  lemmas, StructureSheaf.normalize_finite_fraction_representation, Hilbert 90, and
  PreGaloisCategory.has_decomp_quotients; none states this construction.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite, AlgebraicGeometry.Proj"`: zero hits.
- `msearch.py ... grep "normSection|orbitBundle|finiteNorm|orbit_pair" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of the same concepts and the exact node id in lean/WeilConjectures: no statement
  match. Broader orbit searches found unrelated Galois, quotient, and cohomology results.
- `rg` in lean/Sheaf: the stronger-hypothesis existential ample-curve pencil theorem and
  its exact orbit helper definitions, so those definitions are reused. It does not state
  this theorem for arbitrary M and a supplied affine orbit-separated pair.
- `rg` of dag/nodes found the landed definition owner `def-sfb-pencil-orbit-bundle-norm`;
  it is added to stmt_deps. `blueprint_refs.py search 'orbit tensor'`: zero blueprint-node
  matches. The newest blueprint unit _section.md was read; this is a lower geometric
  input and does not alter that unit's six-functor statement.
- `rg` of the new names in Mathlib, WeilConjectures, Sheaf, and upstream names found no
  conflicting declarations. The existing nonvanishing and projective constructions were
  read rather than redefined.

The source text was read locally: constructions.tex, lemma-projective-space (01NE),
definition-projective-space and its following paragraph (01NF); morphisms.tex,
lemma-finite-proper (01WN). No statement fault or STATEMENT-DISPUTED flag was found.
The sole postponed proof is the item theorem. All helper data are actual constructions;
PencilTensorPermutation is a real inductive predicate, not a postponed axiom.

Validation: `scompile.py Q145 lem-sfb-proper-orbit-pair-finite-norm` compiled the actual
library module and its sandbox form in 3.8 and 3.9 seconds, respectively, with no errors or
non-sorry warnings. Auto-implicit variables are disabled explicitly.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
