## Worker report

Delivery: `lem-sfb-space-picard-stack-smooth`, group N8, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.SpacePicardStackSmooth`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.picard_stack_smooth`.

The statement in the node is unchanged. Its source was read in the current local Stacks
source: quot.tex, section-picard-stack and proposition-pic (0D04), and moduli.tex,
section-picard-stack, lemma-pic-qs-lfp (0DMB), lemma-pic-curves-smooth (0DPJ), including
that section's standing proper, flat, finitely presented algebraic-space hypotheses.
The node is a supporting prerequisite, not a blueprint unit's own statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `S : Scheme.{u}` is the scheme base. `X : AlgebraicSpace S` is an actual fppf sheaf
  algebraic space, not a scheme. `f : X ⟶ schemeSpace (Over.mk (𝟙 S))` is its map to
  the base scheme, regarded in the category of spaces over S. This introduces no new
  condition: the representable sheaf of the terminal S-scheme is terminal.
- `hproper : MapIsProper f` is precisely separatedness, finite type, and universal
  closedness after arbitrary algebraic-space base change. `hflat : MapIsFlat f` uses
  the existing etale source/target chart tests. `hfp : ProperQuotFinitePresentation f`
  is local finite presentation, quasi-compactness, and quasi-compact relative diagonal.
  Thus quasi-separatedness is retained. No other geometry is assumed.
- `PicardModuli f` has a `base : ProperQuotTest B`, namely a scheme over S together
  with its map to B, and `module : (properQuotFibre f base).Modules`. For the main
  theorem B is S itself, so these are all S-schemes with their unique map to S.
  `properQuotFibre` is the actual sheaf fibre product X ×_S base, with its existing
  algebraic-space proof. It is not an arbitrarily chosen model.
- The object's `line` field is the existing `IsLineModule`: local isomorphism to the
  unit structure module on the SMALL etale site. In particular no quasi-coherent,
  finitely presented, flat-over-base or proper-support proof is required as object
  data; those consequences are left to the algebraicity proof.
- `PicardModuli.Hom A C` retains the actual base map u and an isomorphism from
  `moduleTensorPullback (properQuotFibreMap f u)` of C's module to A's module.
  This is exactly the stated arrow u_X^* M ≅ M'. The existing normalized tensor
  pullback is O ⊗_{u_X^-1 O} u_X^-1(-), not an arbitrary functor or iso.
- `identity` uses the existing multiplication-normalized tensor identity;
  `composition` uses the existing pure-tensor-normalized composition comparison,
  then the pulled-back second isomorphism and the first isomorphism. The equality
  of the fibre maps is the existing `CoherentModuli.fibreMap_laws`, which concerns
  only scheme-test fibre maps, not coherent modules. `category_laws` is the named
  postponed proof obligation for precisely these operations, with its full tensor
  proof in its docstring. The instance and forgetful functor contain real data.
- `PicardModuli.category f` is the resulting actual total category over Sch/S.
  `IsAlgebraicModuliStack (PicardModuli.category f)` is the first conjunct and has
  NO dimension hypothesis: it includes fibred groupoids, etale stack descent,
  algebraic-space diagonal, and a smooth surjective scheme atlas.
- The second conjunct quantifies over EVERY `Ω : Type u`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, every geometric map `a : Spec Ω ⟶ S`, and every scheme object
  U of the fibre's small etale site. The condition `IsAffine U.obj.left.left` selects
  affine etale charts, and `topologicalKrullDim U.obj.left.left ≤ 1` bounds them.
  This says exactly that their supremum is at most one. It also retains the empty
  fibre: the dimension of an empty chart is bottom and there are no nonempty charts.
  The geometric map in Over explicitly has domain `Over.mk a`; it is not an extra
  chosen lift or a restriction on a. All test objects use the project's size convention.
- Only under this dimension antecedent does the conclusion supply `V : Over S` and
  `a : BasedFunctor (discreteModuli (yoneda.obj V)) (PicardModuli.category f)`.
  `IsSmoothModuliAtlas ... V a` is the specified smooth surjective atlas, and
  `Smooth V.hom` says that its structural map to S is smooth. These are exactly
  the witness fields of the existing `IsSmoothModuliStack` definition.
- `IsSurjectiveModuliMap a` retains the expressly requested field-extension clause:
  every field-valued object lifts after a field homomorphism K → K', with the actual
  2-isomorphism comparing the composite to restriction of that object. Field maps
  are unital, hence injective. This is the existing predicate, not a new formulation
  with geometric points only, or a sectionwise surjectivity assumption.
- There is no hypothesis on f_*O, sections, reducedness, connectedness, nonempty
  fibres or Noetherian bases. The natural-language proof includes all seven steps
  of the node, especially the noncartesian stage thickenings in approximation.

Dependency declarations read and used (namespace AlgebraicGeometry.AlgebraicSpace
unless otherwise stated):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `Modules`,
  `IsLineModule`, including their full definitions and the local-triviality predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`:
  `flat_proper_fp_locality`, with its separate flat/proper/finite-presentation tests.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with the sheaf pullback and full universal property.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingInverse`,
  `cotangentRingMap`; its recorded enlarged-site declarations are in
  `EnlargedEtaleRingedSite`, whose `schemeSpace` is reused here. Module pullbacks use
  the existing canonical small ringed-topos construction, not chart restriction for
  arbitrary base maps.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`, `IsSmoothModuliStack`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, bottom-inclusive dimension.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`, `properQuotFibre`,
  `properQuotFibreMap`, `ProperQuotFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`: `moduleTensorComposition`,
  read with its unique local pure-tensor normalization (owner node
  `def-sfb-space-module-tensor-composition`).
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `moduleTensorPullbackId`, its named
  uniquely normalized ordinary comparison; no derived category is used in our signature.
- `Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`: `CoherentModuli.fibreMap_laws`,
  reused for the base-change maps, and `coherent_stack_general` as proof input.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `CategoryTheory.IsSurjectiveModuliMap` and its chartwise equivalence theorem.

The seven added statement dependencies are ALREADY LANDED owners of these existing
interfaces: `def-sfb-space-morphism-properties`, `def-sfb-space-proper-quot-functor`,
`def-trf-space-etale-module-functors`, `def-sfb-space-module-tensor-composition`,
`def-sfb-space-derived-pullback`, `lem-sfb-space-coherent-stack-general`, and
`def-sfb-surjective-moduli-map`. They introduce no new notion or
statement correction. Existing statement dependencies remain present and unchanged.

All recorded proof-dependency modules are imported, publicly where their declarations
also supply construction data, privately otherwise. Unstated proof-only dependencies
at inspection time have no module to import: lem-sfb-space-invertible-open-coherent,
lem-sfb-space-invertible-limit-descent, lem-sfb-space-thickening-base-change,
lem-sfb-space-closed-immersion-quasi-coherent-modules,
lem-sfb-noetherian-space-fibre-cohomology-bound, and
lem-sfb-space-square-zero-picard-obstruction. No statement depends on an unstated
interface. Mathlib proof leaves use Noetherian and FinitePresentation imports.

Edge cases checked before finalizing: empty S; empty X or empty geometric fibres;
zero-dimensional fibres; higher-dimensional fibres (only algebraicity is asserted);
nonreduced and disconnected fibres; arbitrary characteristic including characteristic
zero; non-Noetherian bases; arbitrary line-module automorphisms. The structures keep
these cases, with no subsingleton or set-of-isomorphism-classes replacement. Every
universe and variable is explicit, with autoImplicit and relaxedAutoImplicit disabled.

Searches made, using the prescribed msearch.py wrapper and direct read-only searches:

- leanfinder: "The Picard stack of line bundles on a proper flat finitely presented
  algebraic space is algebraic and smooth if geometric fibres have dimension at most
  one". Result: 8 hits, scheme Smooth/IsSmoothOfRelativeDimension properties only;
  no Picard stack or relative line-module total category.
- loogle: `"Picard", "Smooth"`. Result: OK, 0 hits.
- grep (Mathlib): `PicardStack|picardStack|Picard.*Moduli|LineModuli`.
  Result: OK, 0 hits.
- rg in both lean/WeilConjectures and lean/Sheaf:
  `PicardModuli|picardModuli|picard_stack|PicardStack`. No existing declaration.
  A broader Picard/smooth search found scheme Picard-functor results, curve Picard
  torsion, and the downstream CurveSmoothPolarizationCover; none is this statement.
- grep -rn of the item's id in lean/WeilConjectures: no result.
- rg of `IsLineModule` in lean/Sheaf found the shared definition and its consumers;
  reused it. Searches of module operations and SpaceCoherentStackGeneral located
  the existing fibre maps and normalized tensor identity/composition, all reused.
- rg of the prospective Picard declaration names in dag/lean_names_upstream.json:
  no result. The DAG contains Picard-stack results and this node's own definition
  of P_f; no separate recorded relative Picard total-category declaration exists.
  `tools/blueprint_refs.py search 'Picard stack'`: 0 blueprint node matches.
- `scompile.py --source Sheaf.AlgebraicGeometry.SpacePicardStackSmooth`:
  source unavailable, confirming that this prospective module had not landed.

Verification: scompile.py compiled the single sandbox file and its named library module
cleanly, 3.8 s and 4.4 s respectively, with no unexpected warnings. The initial errors
(private import of a reused law and an underspecified Over-domain) were repaired by
publicly importing its owning module and explicitly writing the domain and triangle.
The remaining `sorry`s are exactly PicardModuli.category_laws (the category introduced
by this node) and picard_stack_smooth. Their docstrings give sources and complete
natural-language proofs. Definitions contain real data and no sorry. The ownership defect from the returned
delivery is repaired below. No statement correction or disputed statement is required.


## Repair of returned head 073f5ba5e243

H2 (the sole returned point): removed `lem-sfb-stack-chartwise-smooth-etale-calculus`
from `stmt_deps`; retained it in `proof_deps`. The statement now cites
`def-sfb-surjective-moduli-map` as the owner of the plain definition
`CategoryTheory.IsSurjectiveModuliMap`.

The return requested a new definition node, but the required preliminary search found
that Q87 had already landed exactly this definition node on current main. Its
`reviewed` and `reviewed_lean` records are PASS on 2026-10-24, and its `existing: true`
record points to `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`. Reusing
that landed owner satisfies the requested ownership correction and the one-definition
rule. No duplicate node, copied definition, or replacement declaration is introduced.
The existing node and its full Lean definition were read: the binders quantify over
the base scheme, independently sized source and target categories, the based functor,
every field K, its S-structure, and every object map; witnesses supply L, a field map
K → L, a source object map, and the precise ModuliTwoIso after restriction. This is
exactly the field-extension surjectivity clause used by the Picard theorem.

Read Stacks stacks-properties.tex Tag 04XI (lemma-characterize-surjective), including
the field-extension lift to the two-fibre product; also read Tag 04ZT
(lemma-composition-surjective). The existing owner cites 04XI and definition 04ZS,
which directly define and characterize this predicate. No new mathematical claim
is added in this repair. The empty-source/empty-target cases and identity extension
are included in the same universal-existential condition.

`lem-sfb-space-coherent-stack-general` remains in `stmt_deps`: as the reviewer
confirmed, its theorem `CoherentModuli.fibreMap_laws` supplies actual equalities used
by the eqToIso transports in the Picard identity/composition definitions.

Compared the retained delivered node with current main: before repair the only
differing fields were `lean` and `stmt_deps`, and main still had no Lean record or
Picard module. The repaired node was reconstructed from current main, carrying over
the retained Lean record and the corrected added dependencies. The delivery wrapper
builds the repair commit on freshly fetched current main. The Lean module remains
byte-identical to the retained delivered version; SHA-256: `55e20025379c912af0964086919ff1547bcd4c402875e3d3b186bff56c5cf7c7`.
No statement, proof, proof dependency, or universe changed.

Repair searches (prescribed msearch.py, group N8 and this item):

- leansearch: "A morphism of stacks is surjective if every object over a field lifts
  after an extension of fields"; 8 hits about concrete-category surjectivity, scheme
  surjectivity and surjectivity on stalks; no Mathlib moduli-map predicate.
- loogle: `"IsSurjectiveModuliMap"`; OK, 0 hits.
- grep of Mathlib: `IsSurjectiveModuliMap|SurjectiveModuli|surjective.*[Ss]tack`;
  OK, 0 hits.
- rg of the exact name in lean/WeilConjectures and lean/Sheaf finds its existing
  definition at StackChartwiseSmoothEtaleCalculus.lean:69 and theorem consumers.
- rg -l of the name in dag/nodes finds the exact definition owner
  `def-sfb-surjective-moduli-map`, as well as theorem consumers. Its full node and
  existing binding were read; no additional owner is needed.
- tools/blueprint_refs.py search 'surjective' finds existing general blueprint
  surjectivity references; the exact owner was identified by the preceding DAG search.

The compiler and delivery dry run are rerun for this repaired packet. The maintainer's
independent review remains the second reading; no worker review is claimed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
