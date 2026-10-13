## What changed

The original signature of AlgebraicGeometry.principalCech_resolution_quasiIso is unchanged.
Its proof applies the basic-open section comparison to the product defining each intersection,
obtains a finite-column model, invokes the already proved
HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns with bounds 0 and r-1,
and transports the result along an arrow isomorphism using quasiIso_iff_of_arrow_mk_iso.

Added PrincipalOpenSectionsResolutionQuasiIso and PrincipalCechFiniteColumnModel, one public
statement per module, and their two DAG nodes. All three additional imports in the item are proof-only imports.
The original public import PrincipalOpenCechTotal is unchanged. No definition or existing
statement changed, no adaptations are necessary, and no objects are defined by choosing
arbitrary witnesses from an unproved existence theorem. The model witnesses are used only
inside the theorem proof to apply the finite-column comparison.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.principalCech_resolution_quasiIso
(lem-sc-principal-cech-resolution-quasi-iso). No sorry remains in the item.

Added two named holes, each the entire proof of its theorem:

- AlgebraicGeometry.principalOpenSections_resolution_quasiIso
  (lem-sc-principal-open-sections-resolution-quasi-iso).
- AlgebraicGeometry.principalCech_finiteColumn_model
  (lem-sc-principal-cech-finite-column-model).

This is a decomposition: one hole closed, two added, net -1 before subsequent pruning.
The first obligation is only the affine section comparison, with no Cech total conclusion.
The second is the algebraic bicomplex construction and arrow identification, with no
geometric assumptions and no total quasi-isomorphism conclusion. The finite-filtration
quasi-isomorphism argument itself uses an existing proved theorem, not a new hole.

All three modules compile through lcompile.py without warnings. The support interval is
empty for r=0, and the existing finite-column theorem expressly handles that case; r=1
has only the singleton column. The proposed statements also include g=0 (empty open),
empty intersections, zero complexes and the zero ring. There is no vertical boundedness
assumption and no quasi-coherence assumption on resolution terms.

## No longer needed

Removed the item's direct proof import
Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections and its direct proof-dependency
edge lem-sc-qcoh-complex-alternating-cech-derived-sections. Its statement is retained as a
planned tool of the new basic-open section lemma, through the one-element affine cover;
there is no claim that the module has left the whole target closure.

The new item proof does not directly need AffineQCohDerivedEquivalence,
QCohAcyclicDerivedSectionsComparison, RingedSiteKInjectiveResolutions,
KInjectiveRestrictOpen, BoundedFilteredComplexSpectralSequence, SpectralSequencePageInduction,
FiniteFiltrationInduction, ModuleInjectiveOpenCoverCechAcyclic or AlternatingCechComputes,
the proof modules behind the old dependency. They were not separately imported by the
item and are not separately added. Their nodes are not globally retired: some remain
needed by the section-comparison obligation or other target routes. The explicit finite
filtration induction in the item's plan is discharged by the already proved integer
finite-column comparison, rather than by the general filtered-object spectral machinery.

The second reading replaced the model module's public BicomplexColumns import with
Mathlib.Algebra.Homology.TotalComplex and Mathlib.Algebra.Homology.Embedding.CochainComplex,
which supply its actual statement interface. BicomplexColumns is now a proof-only import
of the item, where its comparison theorem is used. No other imports were removed. The Serre-duality unit has
no realized nodes in the unit record; no unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The old proof step cited an intersectionwise assertion found only in the proof text of
lem-sc-qcoh-complex-alternating-cech-derived-sections. Its Lean statement instead concerns
alternatingCechTotalFunctor for a cover of an entire scheme, with a derived comparison;
it does not directly state QuasiIso of affineOpenSections.mapHomologicalComplex.map i.
The new section node makes that specific missing interface explicit. The original
mathematical statement is not disputed.

The finite-filtration step was marked elementary but its formal proof already exists
in BicomplexColumns. The remaining algebraic gap is identifying the hand-written finite
coordinate total with that library's total construction, not proving another spectral
comparison theorem. Standard total signs were checked in Mathlib ComplexShapeSigns:
epsilon1=1 and epsilon2=p.negOnePow, matching the original displayed differential.

The local Stacks TeX files are absent. Read the official online statements and proofs at
https://stacks.math.columbia.edu/tag/08C2 and https://stacks.math.columbia.edu/tag/08D2.
LeanSearch returned Internal Server Error; this is recorded as unavailable, not absence.
LeanFinder, Loogle and Mathlib rg searches ran and did not expose either required interface.
The existing proved finite-column theorem and its DAG node were found by local rg.

blueprint_refs.py ancestor prints None for this item because its created.item is a Lean
module name rather than a DAG id. The new nodes' blueprint ancestry was traced through
the item's stored parent and its parent's stored blueprint record to lem-sc-finite-duality.
The unit, chapter, source and current target signatures are unchanged.

## New nodes

lem-sc-principal-open-sections-resolution-quasi-iso is stated in
lean/Sheaf/AlgebraicGeometry/PrincipalOpenSectionsResolutionQuasiIso.lean. It is the
one-element affine-cover specialization of the unbounded acyclic section comparison;
its docstring and node describe restriction, affine vanishing, comparison with arbitrary
K-injective resolutions, and restriction of scalars. It is strictly the first step.

lem-sc-principal-cech-finite-column-model is stated in
lean/Sheaf/AlgebraicGeometry/PrincipalCechFiniteColumnModel.lean. It isolates regrouping by
subset cardinality, the strict support bounds, the column product comparison, the total
signs, and the arrow isomorphism. It works for any coefficient map and does not assert
the item's total quasi-isomorphism. Both new nodes carry the actual logged three-kind
searches, full proofs in words and Lean signatures. No change records are needed.


## Second reading by W3

1. Compared the item with the repository using diff. The only existing declaration is
   AlgebraicGeometry.principalCech_resolution_quasiIso: its signature, visibility and
   docstring are byte-for-byte unchanged; only its proof and proof-only imports change.
   The two other modules are new. There are no changed definitions or change records.
   Verdict: unchanged mathematical interface of the existing item.
2. Compiled all three modules with lcompile.py, and compiled scratch copies ending in
   #print axioms for each of the three theorem names. Each reports only propext,
   Classical.choice, Quot.sound and sorryAx. The item contains no sorry; the two new
   public theorems each have exactly one whole-proof sorry. No forbidden declaration,
   implementation escape or definition choosing model witnesses was added. The existential
   model is eliminated only inside a proposition proof. Verdict: valid reduction with
   two explicitly open obligations, not an axiom-free proof of the target.
3. Read Stacks 08C2, 08D2, 08BS and 08D1 online. The section lemma specializes the
   one-member cover comparison after restriction to D(g); the affine-open basis verifies
   all three vanishing conditions. Comparing K-injective resolutions by homotopy
   equivalences handles J without injective or quasi-coherent terms. For the model lemma,
   group coordinates by card(S)-1 and use the commuting bicomplex with horizontal
   restriction and vertical coefficient differentials; the total signs are exactly
   horizontal plus (-1)^p vertical, as in 08D1. The finite diagonal coproduct is a finite
   product. Checked r=0 (empty support and zero totals), r=1 (one column), g=0, empty
   intersections, zero ring and zero complexes; no boundedness or covering hypothesis is
   needed. Neither lemma restates the item: one is the local section step; the other is
   an algebraic model for arbitrary maps and makes no total quasi-isomorphism assertion.
   Repeated LeanFinder search with “An unbounded complex of quasicoherent sheaves on an
   affine scheme computes derived global sections by ordinary termwise sections” and
   Loogle with “HomologicalComplex₂.total.map, QuasiIso”; searched both library roots
   with sections/quasi-isomorphism and Cech/double-complex/column patterns. Reviewed
   QCohAcyclicDerivedSectionsComparison, AffineQCohDerivedEquivalence and
   CechResolutionDoubleComplex/Total. These supply different derived or bounded
   interfaces, not either missing comparison for the concrete principalCechFunctor.
   Both new theorem docstrings and nodes state their full mathematical reductions.
   Verdict: true, strictly smaller obligations; neither closes in a few-minute application.
4. Read the finite-column comparison proof: its filtration induction includes the empty
   interval. Applying it and transporting along the supplied arrow isomorphism is the
   existing shortest available total comparison. All remaining imports supply statement
   symbols or an actually used theorem. The old node has exactly one proof dependency,
   lem-sc-qcoh-complex-alternating-cech-derived-sections, listed under No longer needed
   as a direct edge; it remains part of the section obligation's planned route. Read
   dag/units/sk-thm-picard-duality.json: realized.statement and its sole realized step
   are empty. No unit-level realization was removed. Verdict: pruning and unit route agree.
5. Compared the item node's proof steps against hsections, model elimination, finite-column
   comparison and quasiIso_iff_of_arrow_mk_iso. Its proof_deps is exactly their node union.
   The two new nodes have matching verbatim Lean signatures, sources, complete proof
   steps, dependency unions, searches, ancestry, chapter/unit and created/lean records.
   Existing-node changes are confined to proof, proof_deps and proof_origin.
   Verdict: nodes match the actual proof and its open obligations.

Second reading changed the import boundary described above, expanded the section docstring
and node to verify 08C2 on every member of the affine-open basis, and corrected the model
node's mistaken label for Tag 08D1 (which is the Koszul comparison whose proof states the
alternating double complex and signs). It did not change any theorem signature, close an
additional hole or add a hole. Counts remain one original hole closed and two split off.
