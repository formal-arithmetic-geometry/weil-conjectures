## Worker report

The delivery states `AlgebraicGeometry.universal_norm_generation_open` in
`Sheaf.AlgebraicGeometry.UniversalNormGenerationOpen`. Its only postponed proof is the
main theorem. The thirteen other declarations in that module are transparent predicates or
constructions with real data, all belonging to this node's universal norm family.
The new definition node binds three existing canonical constructions with `existing: true`;
no duplicate module is supplied. The repair adds explicit definition dependencies and TeX citations, with the
clarification recorded in `statement_change`; hypotheses and conclusions are unchanged.
The source and all proof steps remain unchanged.

The node and all fourteen original and five added statement-dependency nodes were read, together with their
recorded signatures and the construction docstrings. The example CompactObject module is
now withdrawn and contains no declarations; its node records the Mathlib declaration.
The delivery follows the currently published module-mode examples instead.

Hypothesis and clause correspondence:

- The base field is `{F : Type u} [Field F]`. `C : Scheme.{u}` and
  `[C.Over (Spec (.of F))]` specify the scheme and its structure map.
- Smoothness, projectivity, geometric integrality, integrality and finite type are
  `[Smooth ...]`, `[IsHProjective ...]`, `[GeometricallyIntegral ...]`, `[IsIntegral C]`,
  and the pair `[LocallyOfFiniteType ...] [QuasiCompact ...]`. The dimension-one
  hypothesis is `hdim : topologicalKrullDim C = 1`.
- `G : Type v`, `[Group G] [Fintype G]`, and
  `ρ : G →* Aut (Over.mk (C ↘ Spec (.of F)))` specify a finite group and an action by
  F-automorphisms. There is no faithfulness or characteristic assumption.
- `L : C.Modules` with `[L.IsInvertible]` is the invertible sheaf;
  `n : ℕ` and `hn : 1 ≤ n` give the positive tensor exponent.
- B is the existing `pencilOrbitBundle`, and M is its existing `tensorPow n`.
  The existing `pencilNormSection` forms the tensor of translates with the recorded
  pullback-power comparison. None of those definitions is copied.
- Global sections are represented by `M.H 0`, canonically identified with
  `Γ(M, ⊤)` by `H.zeroLinearEquiv`. For J the explicit `HOver f M 0` spelling
  also exposes its canonical F-module instance; it is the same degree-zero space.
  The first two conjuncts assert finite dimensionality of V and J.
- For every `[Field E] [Algebra F E]`, both `Function.Bijective (H.baseChange ... 0)`
  conjuncts concern the actual canonical scalar-extension maps, not an abstract
  isomorphism. The native pullback is canonically identified with tensor pullback,
  and `boundaryPullbackPowIso` identifies the powers. The displayed order E tensor V
  is the standard commuted form of V tensor E.
- `∀ I [Fintype I] (b : Module.Basis I F ...)` means any finite basis of V.
  P is the actual scheme `𝔸(I × ULift (Fin 2); Spec F)`, two independent copies of
  the section coordinates. The lifted two-element index satisfies the existing
  sheaf-free-module and projective-coordinate universe conventions.
- `universalNormPair` constructs both actual universal sections on C times P. It
  sums coordinate multiples of normalized pulled-back basis sections, applies the
  existing tensor norm for the base-changed action, and transports through the
  canonical orbit-bundle base-change isomorphism.
- The first clause of `UniversalNormGenerationFamily` quantifies over every basis
  c of J and supplies polynomials `p : R → MvPolynomial I F` homogeneous of degree
  `Nat.card G`. For each of the two coordinate sets the section equals the finite
  linear combination of pulled-back c with those polynomial coefficients.
  `universalNormPolynomial` evaluates exclusively the chosen coordinate set.
- The existential `Z : ... .IdealSheafData` is an actual closed subscheme of the
  total space. For every trivializing affine W and frame e, if the two restricted
  universal sections have coefficients a,d, its ideal is exactly
  `Ideal.span {a,d}`. This specifies the common zero scheme, including its scheme
  structure, rather than only its support.
- `IsClosed (pullback.snd ... '' (Z.support : Set _))` states closedness of its
  projected support. `U : P.Opens` and the following set equality identify U with
  the complement of that exact image.
- For every E-valued parameter `z`, `hz` says that it is an F-point with values in
  E. `universalNormFiberMap` is the canonical fibre-product map into the total
  space. The specialization equalities use `universalNormSpecialize`, the
  normalized composition comparison, and `boundaryPullbackPowIso` to identify
  the restricted universal pair with the already published `normPencilSections`.
- `Set.range z ⊆ U ↔ Epi ((SheafOfModules.freeHomEquiv _).symm ...)` says exactly
  that factoring through the open is equivalent to generation of M_E. There is
  no closedness assumption on the image of z, so the same equivalence includes
  nonclosed images.
- `UniversalNormInvariantPair` records the two remaining clauses.
  `universalNormPermutation` constructs the specified g ↦ g*k identification
  using normalized pullback composition, finite tensor distribution, and actual
  associators and symmetries. Its implementation removes and reorders factors
  deterministically, and raises the resulting isomorphism to the nth power.
  The first conjunct says this particular comparison fixes each pulled-back norm.
  The second says that for every invertibility witness and every generating
  specialized pair the existing `ProjectiveSpace.homOfGeneratingSections` satisfies
  `(ρ k).hom ≫ h = h` as a scheme morphism to P¹_E.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from Mathlib's morphism module of that name.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Modules.IsInvertible`,
  `tensorPow`, and the tensor-power comparisons.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  monoidal tensor structure, inherited by the scheme-module category.
- `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`: `pencilOrbitBundle`,
  `pencilNormSection`, `pencilGroupElements`, `pencilTranslateTensor`,
  with the remaining seven orbit-norm declarations owned by
  `def-sfb-pencil-orbit-bundle-norm`. The repair uses neither `pencilSectionPair` nor
  `pencilCoordinateMorphism`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: fibre-product and
  module-base-change conventions, and `baseChange_morphism_projections`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: generation encoded as
  the `epi` condition of `GeneratingSections`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `ProjectiveSpace.homOfGeneratingSections`, applied directly with the norm-section
  family `fun j ↦ pencilNormSection ... (a j)` and explicit invertibility witness.
- `WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`:
  `HOver`, `H.baseChange`; `Cohomology.Defs`: `H.zeroLinearEquiv`.
- `Sheaf.AlgebraicGeometry.SeparatingPairOpen`: the existing real-data
  helpers `normPencilTranslateBaseChangeIso`, `normPencilCoordinateSection`, and
  `normPencilSections`, now owned by the new definition node
  `def-sfb-norm-pencil-base-change-sections`, with an `existing: true` binding.
  None of the container’s theorems is used in this statement.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `boundaryPullbackComparison`, `boundaryPullbackTensorIso`,
  `boundaryPullbackPowIso`, and `boundaryTensorPowIso`.
- `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`: `IsFreeGenerator`.

The modules of every recorded proof dependency are imported separately. The main docstring
carries the eleven proof steps and the names of the non-elementary inputs. No extra
postponed helper theorem is introduced.

Sources opened: coherent.tex `lemma-flat-base-change-cohomology` (02KH),
`proposition-proper-pushforward-coherent` (02O5); morphisms.tex
`definition-proper` (01W1); constructions.tex `lemma-projective-space` (01NE)
and its base-change paragraph; fields.tex `lemma-common-extension-field` (0H7K).
The node itself is the source for its explicit finite multilinear expansion and
right-translation construction.

Searches actually made:

1. msearch leanfinder: "Pairs of sections whose finite group tensor norms generate
   an invertible sheaf on a proper curve form an open affine parameter locus".
   Eight hits about affine/basic opens and localization, none the statement.
2. msearch loogle: `MvPolynomial.IsHomogeneous, SheafOfModules.GeneratingSections,
   pencilNormSection`. Zero hits; the service reported unknown identifier
   `pencilNormSection`, so this was not treated as evidence that the project lacks it.
3. msearch grep: `universalNorm|pencilNormSection|IsHomogeneous` in AlgebraicGeometry.
   Seven Mathlib hits, about homogeneous ideals and elliptic-curve polynomials;
   none the universal norm theorem.
4. msearch leansearch: "The generating pairs of finite group tensor norm sections of a
   line bundle on a proper curve form a Zariski open subset of the affine section parameter
   space". Eight hits about affine/basic opens and generating sections, none the statement.
5. rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID, norm-generation
   words, `pencilNormSection`, and `normPencilSections`. Located and reused the
   AmpleCurveTwoSectionPencil and SeparatingPairOpen helpers. No existing declaration
   gives the complete universal polynomial family and exact open equivalence.

Edge cases checked mathematically before writing: the trivial group gives a degree-one
norm; arbitrary nonfaithful actions remain permitted; characteristic dividing the group
order requires no division. If V=0, its empty basis gives P=A⁰, both sections are zero,
Z is the whole curve and the generating open is empty. An empty basis of J is also
allowed in the polynomial clause. The theorem does not assert a rational point or
nonemptiness of U. Finite base fields and transcendental E/F are allowed. The curve
itself is nonempty because it is integral and one dimensional. Nonclosed parameter
images are unrestricted. The group index lives in an independent universe v; scheme,
coefficient, extension-field and parameter-index universes follow the existing project
size convention u, with no additional equality between independent site universes.

No STATEMENT-DISPUTED finding. The ownership and citation clarification is recorded
under Statement corrected below; it changes no mathematical assertion.

Import ownership and cycle handling: the new definition node owns only the three
existing plain base-change helper definitions. It has no statement or proof dependency
on either this item or `lem-sfb-separating-pair-open`. The DAG direction is
`separating-pair theorem → universal-generation theorem → base-change definitions`.
The original `Sheaf.AlgebraicGeometry.SeparatingPairOpen` container is imported to reuse
these definitions, exactly as the latest return requests. It currently does not import
`UniversalNormGenerationOpen`. A future reverse proof import into that container must
be omitted under stages/2-statements.md §3(7)'s import-cycle exception. This is the
`existing: true` ownership option explicitly authorized by F1 of the first return,
like `def-sfb-pencil-orbit-bundle-norm`. No declaration is copied or renamed and no
physical import cycle is present.

## Second reading by Q41

The dispatcher prohibits starting another agent and assigns independent review to the
maintainer. This is the worker's separate final self-check. I re-read all three existing
helper signatures, bodies and docstrings in current main beside the rejected copies.
They construct the same objects: recursive translated-tensor base change, the coordinate
sum transported through the pullback-power comparison, and the norm transported through
the inverse orbit comparison. Only qualified spelling of tensorPullback differs; the
mathematics and real-data formulas coincide. Reusing the original definitions therefore
preserves all specialization clauses and the main theorem signature.

The main module still has thirteen transparent constructions/predicates and one theorem
with `sorry`; no new helper theorem is postponed. The generation predicate, closed zero
scheme, polynomial homogeneity in every basis, nonclosed field points, g ↦ g*k comparison,
and direct projective map retain the previously checked clauses. All four F2 definition
dependencies and their citations remain. The main signature is unchanged. No definition
owned only by the other pencil theorem is used.

## Repair of returned head 1dda2b915bb2

The maintainer identified three duplicate declarations in the added module. This repair
deletes `NormPencilBaseChangeSections.lean`, changes the main module's public import to
`Sheaf.AlgebraicGeometry.SeparatingPairOpen`, and changes the new definition node to an
`existing: true` binding of all three original declarations in that module, without a
`lean.file`. No renaming, wrappers or second constructions are introduced.

Current main now contains the original source that was unavailable during the previous
repair. Its full signatures, bodies and docstrings were read, and its import list was
checked for a reverse import. The sandbox node was compared with current main: the item
differs only in lean, the five authorized statement dependencies, the corresponding
TeX clarification, and statement_change. The added definition node is still new on main.
The wrappers perform the authorized rebase when preparing this delivery.

Earlier F1 remains repaired by independent definition-node ownership and a TeX citation.
Earlier F2 remains repaired by direct `ProjectiveSpace.homOfGeneratingSections`
applications to `fun j ↦ pencilNormSection ... (a j)` and the four direct dependencies:
`def-pc-flat-cohomology-comparison`, `def-sc-tensor-pullback-power-comparison`,
`def-sfb-tensor-power-pullback-comparisons`, and `def-sc-local-free-generator`.

## New nodes

`def-sfb-norm-pencil-base-change-sections` supplies an independent DAG owner for
`normPencilTranslateBaseChangeIso`, `normPencilCoordinateSection`, and `normPencilSections`,
all bound with `existing: true` to `Sheaf.AlgebraicGeometry.SeparatingPairOpen`.
No new Lean module is delivered for this node. The recursive comparison's variables
`f`, `α`, `β`, `w`, `L`, and list argument express the commuting-square tensor comparison.
The coordinate helper's `π`, `p`, `b`, `z`, `j` give the coordinate-weighted section sum
through `boundaryPullbackPowIso`; the norm helper uses the base-changed action,
`pencilNormSection`, and inverse `boundaryTensorPowIso` of the recursive comparison.
This is exactly the node's definition. There is no invertibility, positivity, basis,
faithfulness or generation hypothesis, and arbitrary parameter morphisms are allowed.
The empty coordinate set and n=0 are defined. Source: Stacks Modules 01CA/01CD and
this item's explicit coordinate specialization, proof steps 3–5; de Jong §3.4(c).

The retained actual searches are LeanSearch for the finite translated-tensor base-change
and universal-coordinate norm construction (eight tensor/base-change hits, none exact),
LeanFinder for base-changed orbit norm coordinates (eight nearby coordinate/tensor hits,
none exact), and Mathlib grep for the three names (zero hits). DAG and blueprint searches
found no independent definition owner. The original source was unavailable at the last
repair, but current-main rg now finds all three exact definitions in SeparatingPairOpen.
The new node records both historical results and this current successful match, whose
full bodies were checked. Consequently the declarations are reused, not duplicated.

## Statement corrected

The old statement remains verbatim in `statement_change.old_statement`. The only TeX
addition identifies the intended canonical coordinate sections with their definition
owner and names the four independent comparison/frame definitions required by F2.
The source remains the original Stacks 02KH/02O5 and explicit universal tensor expansion.
No hypothesis or conclusion changes. `old_stmt_deps` records the original dependency list;
proof and proof_deps remain unchanged. This repair changes no mathematical statement.

The complete citer search was `grep -rl '"lem-sfb-universal-norm-generation-open"'
dag/nodes`, followed by inspecting dependency lists. The sole citer is
`lem-sfb-separating-pair-open` (holds: true): it still uses exactly the same universal
polynomial family, open-generation equivalence and invariance assertions. It is not edited.
