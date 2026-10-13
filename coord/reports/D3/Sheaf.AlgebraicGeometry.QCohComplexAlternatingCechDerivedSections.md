## What changed

Replaced the sole hole of `AlgebraicGeometry.qcoh_complex_alternating_cech_derived_sections`
with a compiling reduction to two analytic quasi-isomorphism statements in new modules:
`Sheaf.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso` and
`Sheaf.AlgebraicGeometry.KInjectiveAlternatingCechAugmentationQuasiIso`.
The existing theorem's signature, universes, public imports and docstring are unchanged.
No existing definition or statement was changed; no forced adaptations are needed.

The categorical argument is proved in the item's module. Its private `sectionsDerivedUnit`
is the actual right-derived unit transported through `quotientCompQhIso`, and
`sectionsDerivedUnit_iso` proves its component on a K-injective equals the inverse of
`rightDerivedFunctorObjQIso`. The proof constructs a natural transformation using the
existing functorial K-injective resolution and inverses of explicit natural transformations.
It proves `a.app K ≫ β.app K = b.app K`, then the defining comparison equation through
EVERY K-injective resolution. It proves invertibility on the quasi-coherent complex,
uniqueness of every supplied comparison by cancellation along one resolution, and the
requested naturality square from that uniqueness and naturality of β.

The parent DAG proof and dependency list now follow those actual Lean steps.
All three modules compiled together with `lcompile.py --all`, without warnings.
The remaining analytic interfaces were checked against Stacks Tags
[08C1](https://stacks.math.columbia.edu/tag/08C1),
[08C2](https://stacks.math.columbia.edu/tag/08C2),
[01XB](https://stacks.math.columbia.edu/tag/01XB),
[01EP](https://stacks.math.columbia.edu/tag/01EP), and
[08BS](https://stacks.math.columbia.edu/tag/08BS).

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.qcoh_complex_alternating_cech_derived_sections`
(node `lem-sc-qcoh-complex-alternating-cech-derived-sections`). No sorry remains in the item.

Added exactly two named theorem holes, each in its own module:

- `AlgebraicGeometry.qcoh_alternatingCech_resolution_quasiIso`
  (`lem-sc-qcoh-alternating-cech-resolution-quasi-iso`): the actual Čech total map
  of a quasi-coherent complex's K-injective resolution is a quasi-isomorphism.
- `AlgebraicGeometry.kInjective_alternatingCech_augmentation_quasiIso`
  (`lem-sc-kinjective-alternating-cech-augmentation-quasi-iso`): the actual finite-cover
  augmentation on a K-injective complex is a quasi-isomorphism.

This is a decomposition: one original hole closed and two lower holes added, not a
sorry-free proof or a net decrease in holes. Neither child restates the parent:
they assert quasi-isomorphisms of distinct explicit cochain maps, and neither asserts
existence of a derived comparison, invertibility of an arbitrary supplied comparison,
or its naturality. The Lean combination of these facts is complete.
Every new hole has source, a full proof in words, and a matching node.
The private unit helpers contain no holes. No data was selected from a new existence theorem.

Edge cases: for r=0 the cover condition forces X empty; both totals and all section
modules vanish. For a zero complex the resolution-map claim is consistent with
acyclicity of its resolution. Repetitions in the affine hypothesis are harmless;
actual alternating terms use strictly increasing tuples. For r=1 the cover member
is top, and the augmentation is the section-complex identification. The augmentation
child deliberately assumes neither affine intersections nor quasi-coherence, and it
allows K-injective complexes without injective terms; its homotopy-transport step is
written explicitly in the node and docstring. No coefficient-degree bound was added.

## No longer needed

Removed all ten old proof-only direct imports from the item:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.Paper.QCohAcyclicDerivedSectionsComparison`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.SpectralSequencePageInduction`
- `Sheaf.CategoryTheory.FiniteFiltrationInduction`
- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
- `Sheaf.AlgebraicGeometry.AlternatingCechComputes`

These are not all globally pruned modules. The affine and restriction
lemmas remain planned dependencies of the resolution-map child; the second reading replaces
its spectral-sequence/page/filtration steps by the existing upstream finite-column theorem; injective Čech
acyclicity and alternating comparison remain planned dependencies of the augmentation
child. Ringed-space derived-image and resolution declarations remain available through
the unchanged public imports of `AlternatingCechTotalComplex`, and are actually used.
The nodes for all these retained ingredients remain in the children's or parent's DAG
closure. No unit statement or realized unit step was bypassed.

The duplicate node `lem-sc-kinjective-quasi-iso-comparison` is no longer needed in this
reduction: the augmentation child's homotopy-equivalence transport uses the equivalent
Mathlib comparison recorded by `lem-weil-pbc-kinjective-hom-derived`. Both original
nodes pointed to `CochainComplex.IsKInjective.Qh_map_bijective`; no second application is
required. The second reading also removes `thm-sp-spectral-object-yields`, `lem-sp-page-induction`
and `lem-sp-finite-filtration-induction` from this reduction, using
`lem-sc-integer-finite-column-total-comparison` instead. These are dependency-route
prunings; no whole-library module-pruning count is claimed.
Removed an unnecessary Coherent public import from the new augmentation module before
its final compilation; that statement does not use quasi-coherence.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The planned affine, spectral and Čech
lemmas are ingredients rather than plug-in lemmas for the two explicit total-complex
quasi-isomorphisms; their signatures do not directly finish those steps. The two new
nodes isolate precisely those analytic interfaces. The existing categorical definitions
are adequate: the natural transformation construction proves the universal resolution
equation and naturality without a separate new resolution-independence hole.

The local literature checkout contains lists rather than the cited Stacks text, so the
linked primary-source pages were read directly. LeanSearch returned Internal Server
Error; its searches are recorded as unavailable without a mathematical verdict. Actual
LeanFinder, Loogle and pinned-Mathlib source grep searches were also performed and logged
in `searches.jsonl`. No exact existing statement was found. Blueprint searches for
`Cech K-injective` and `alternating Cech derived` returned no matching blueprint node.
The unit `sk-thm-picard-duality` has no realized binding of this node to a distinct unit
step, and its route was left unchanged.

## New nodes

`lem-sc-qcoh-alternating-cech-resolution-quasi-iso`, in
`dag/nodes/sec-picard-framework/`, states the affine-intersection/finite-column comparison
from original Steps 2--3. Its proof records restriction, unbounded affine sections,
finite products, and the existing upstream finite-column total comparison. Its module is
`lean/Sheaf/AlgebraicGeometry/QCohAlternatingCechResolutionQuasiIso.lean`.

`lem-sc-kinjective-alternating-cech-augmentation-quasi-iso`, in the same chapter, states
the augmentation quasi-isomorphism from original Steps 4--5. Its proof records exact
injective alternating rows, the finite staircase argument, the signed total homotopy,
and transport to K-injectives without injective terms. Its module is
`lean/Sheaf/AlgebraicGeometry/KInjectiveAlternatingCechAugmentationQuasiIso.lean`.

Both inherit chapter and unit from the parent, and their blueprint ancestry is the
proper-flat support comparison in `lem-sc-finite-duality`. No change record is required:
all existing interfaces and public visibility are unchanged.

## Second reading by D3

1. **Interfaces: PASS.** Diffed the item's whole module against the repository. The existing
   theorem signature, universes, docstring and four public imports are byte-for-byte unchanged.
   The only added declarations are private helpers with explicit data and proofs. Both other
   delivered modules are new. The parent node changes only proof, proof_deps and proof_origin.
   No change record or forced adaptation is required.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three files with
   lcompile.py --all, without warnings or errors. Compiled a scratch copy with #print axioms
   for both private helpers, the parent and both children. The helpers use only propext,
   Classical.choice and Quot.sound; the three public theorems additionally use sorryAx, as
   expected from the two named child holes and existing open dependencies. There are exactly
   two direct sorry proofs, both whole proofs of the named public child theorems; no hollow
   data, arbitrary existence witness, axiom or forbidden declaration. Read the cancellation
   and naturality argument in full: the constructed unit is the actual derived unit, its
   K-injective component is the canonical inverse, and the resolution equation is established
   for every K-injective resolution. One original hole closed, two added: net -1, not a
   sorry-free proof.
3. **Split statements: PASS.** Checked each signature against its node and its natural-language
   proof. They assert different explicit cochain quasi-isomorphisms, each strictly part of
   the parent's argument. Checked empty covers, empty intersections, singleton covers, zero
   complexes, repeated indices and unbounded coefficient degrees. In the augmentation child,
   transport from injective terms to arbitrary K-injectives uses a homotopy equivalence and
   the signed total homotopy, not unjustified exactness of sections. Independently read
   [08C1](https://stacks.math.columbia.edu/tag/08C1),
   [08C2](https://stacks.math.columbia.edu/tag/08C2),
   [01XB](https://stacks.math.columbia.edu/tag/01XB) and
   [01EP](https://stacks.math.columbia.edu/tag/01EP). Independent LeanFinder query on homotopy
   equivalences and finite column comparison, Loogle query HomologicalComplex₂.total,
   QuasiIso, and msearch grep on augmentation/quasi-isomorphism returned no exact child
   theorem. Also searched lean/Sheaf, lean/WeilConjectures and pinned Mathlib sources with
   rg. The principal-open sections theorem imports this parent, so cannot shorten this
   proof without a cycle. The singleton augmentation only handles one cover member.
4. **Shortest route and pruning: PASS after repair.** Found the already-proved upstream
   HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns and its existing node
   lem-sc-integer-finite-column-total-comparison. Replaced the resolution child's planned
   spectral comparison, page induction and finite graded-filtration argument with this
   direct theorem; its remaining affine-section interface is substantial and cannot be
   closed by that theorem alone. Updated its docstring and node, without changing any
   signature or Lean proof. The parent's two proof imports and all new public imports are
   appropriate to their use. Its old dependencies now omitted are
   lem-pc-affine-qcoh-derived-equivalence, lem-sc-qcoh-acyclic-derived-sections-comparison,
   lem-sc-derived-k-injective-restrict-open, thm-sp-spectral-object-yields,
   lem-sp-page-induction, lem-sp-finite-filtration-induction,
   lem-weil-pbc-module-injective-open-cover-cech-acyclic, lem-pc-alternating-cech-computes,
   lem-weil-pbc-kinjective-hom-derived and lem-sc-kinjective-quasi-iso-comparison.
   Retained ingredients are explicitly assigned to the child nodes above. The unit
   sk-thm-picard-duality and its realized fields are unchanged; no bound unit step is bypassed.
5. **DAG agreement: PASS.** Read all three nodes; checked statement records against Lean,
   dependency lists against the union of uses in the proof steps, sources, creation records,
   blueprint ancestry and chapter/unit. The parent follows the actual natural-transformation
   proof; the two child nodes describe their unfinished analytic arguments. The finite-column
   shortcut uses an existing node with a complete upstream proof; no duplicate node is added.

Second reading changed the resolution child's proof docstring and DAG plan to reuse the
existing finite-column theorem, corrected the report's pruning account, and recorded these
independent checks. The compiled categorical proof needed no repair.
