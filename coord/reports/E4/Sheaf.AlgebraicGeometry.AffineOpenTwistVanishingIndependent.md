## What changed

Replaced the one sorry in `Sheaf.AlgebraicGeometry.AffineOpenTwistVanishingIndependent`
with a compiling reduction. Added proof-only imports of the fixed-degree affine Serre
lemma, ordinary higher-image restriction, module-cohomology source comparison, affine
higher-image sections, uniform qcqs degree bounds, tensor quasi-coherence, and Mathlib tilde.

The proof constructs a coefficient-independent degree bound for the restricted morphism.
It takes a finite subcover of the local coefficient-independent degree bounds on the affine
base and their finite maximum, then selects one threshold per degree below that bound, omits the degree-zero condition,
and takes their finite sum. Higher degrees vanish by that bound; lower positive
degrees vanish by the new lemma. Affine sections and quasi-coherence detect zero via the
tilde counit, and ordinary open restriction transports this to the required conclusion.
The statement and all public imports of the existing module are unchanged. Both modules
compile without warnings through lcompile.py.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_twist_on_affine_open`
(node `lem-pc-q3-affine-open-twist-vanishing-independent`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_isZero_restricted_twist_moduleCohomology_degree`
(node `lem-pc-e4-affine-restricted-twist-fixed-degree`), in the new module
`Sheaf.AlgebraicGeometry.AffineRestrictedTwistVanishing`.

This is a decomposition, not a sorry-free proof of geometric Serre vanishing: one hole
closed and one strictly smaller hole added. The remaining assertion fixes a single
positive degree, concerns module cohomology rather than higher images, and has no
uniform-in-degree threshold. The actual combination across degrees, affine zero detection,
and transport are proved. No arbitrary data are defined from an unproved existence theorem:
all choices in this delivery occur within proposition proofs. Empty source/base and degree
bound zero are included; Fin 0 gives an empty threshold sum.

## No longer needed

No original public import was removed. Removed the trial proof import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, which compilation
showed unnecessary.

The original proof dependency `lem-weil-pbc-coherent-serre-vanishing` and its module
`Sheaf.AlgebraicGeometry.CoherentSerreVanishing` are not needed directly: the new fixed-degree
node replaces that whole all-degree Serre interface. Its mathematical ingredients remain
in the new node's plan. Likewise `lem-pc-restrict-derived-direct-image-open` and
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` are unnecessary here; the ordinary
higher-image restriction node `lem-pc-higher-direct-image-open-restriction` suffices.
The DAG copies record exactly this replacement. No claim is made that these modules are
unreachable from other targets or items. The global theorem `lem-pc-finite-support-hi` /
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` is also pruned from this proof: it
has a cyclic Lean import path through the parent proper-coherence item. Its needed bound
is constructed from `lem-pc-local-uniform-higher-direct-image-bound` instead. This finite
cover only combines degree bounds inside the one fixed affine base; it is not the global
twist-threshold cover step of RelativeSerreVanishing.

The fourth removed original proof dependency is `lem-pc-proper-base-change`: no explicit
call to its recorded declaration remains in this module; Mathlib supplies the restricted
morphism instances through the unchanged public Proper import. Its geometric content
remains in the fixed-degree node, which explicitly cites it. No public import is pruned.

## Where the brief, the DAG or earlier work was wrong

The recorded CoherentSerreVanishing proof dependency cannot be imported: import_direction.py
reports that it already reaches this item and would close an import cycle. The source
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre` is similarly cyclic. This was anticipated
by the item's proof_origin note. The first dry run also caught a cycle through the
projective global degree-bound module; it was removed and the bound constructed from
the acyclic local coefficient-independent theorem. Existing acyclic comparison and degree-bound modules are
usable, so there is no tool blockage. Tag 0B5T (4) asserts a threshold for each fixed positive
degree; the finite-degree combination missing from that citation is now real Lean.

The unit `sk-thm-picard-coherence` has empty realized lists and this node is below the unit.
The route remains the affine-local Serre/projective argument and Cech-derived machinery;
no unit or chapter route is replaced.

## New nodes

`lem-pc-e4-affine-restricted-twist-fixed-degree`, module
`Sheaf.AlgebraicGeometry.AffineRestrictedTwistVanishing`: fixed-degree cohomology vanishing
on the inverse image of the specified affine open. Source: Stacks Tags 0B5T (4) and 02O1.
Its statement, proof steps, searches, source, blueprint ancestry and Lean signature are
recorded in its new DAG file; its theorem docstring supplies the complete proof plan.
Searches found no Mathlib match; LeanSearch returned Internal Server Error. Existing
all-degree interfaces were found but cannot be imported acyclically. No change record is
needed: no existing signature, definition, or public import changed.

## Second reading by E4

1. **Unchanged interface: PASS.** Read both delivered modules and diffed the existing
   module against the repository. The only existing declaration has the same signature
   byte for byte, including Noetherian base, proper morphism, coherent/quasi-coherent F,
   invertible L, specified affine V, ample restriction and injective-resolution assumption.
   All five existing public imports remain identical. There is no definition change or
   forced adaptation; only a private proved helper, proof imports and the proof are added.

2. **Proof and axioms: PASS as a decomposition.** Both modules compiled through
   `lcompile.py --all` without warnings. A scratch copy with `#print axioms` for both
   public theorems returned exactly propext, Classical.choice, Quot.sound and sorryAx.
   The item contains no sorry; the sole delivered sorry is the listed fixed-degree theorem.
   No axiom, unsafe, opaque, implemented_by, extern or hollow definition occurs.
   The choices of neighborhoods, finite bounds and thresholds are inside a proposition
   proof and do not define public data from arbitrary unproved existence witnesses.

3. **New statement: PASS, proof plan repaired.** Read Stacks
   [0B5T (4)](https://stacks.math.columbia.edu/tag/0B5T) and its residue-class proof, and
   [02O1](https://stacks.math.columbia.edu/tag/02O1). Base-changing the proper morphism to
   the affine Noetherian V gives exactly its hypotheses; coherence restricts, and hL gives
   the required ample invertible restriction. The conclusion fixes q>0 and concerns
   cohomology, so it leaves the finite degree combination and higher-image transport to
   the actual Lean reduction. Checked empty V, empty inverse image, zero F, degree one,
   residue zero and d=1; none requires an extra hypothesis. Degree zero is deliberately
   excluded (O on projective space has nonzero H^0). Threshold d*T works also for T=0.
   Independent LeanFinder, Loogle and Mathlib grep searches with cohomology/projective
   phrasing found no matching theorem. Read CoherentSerreVanishing, source Serre and
   ClosedImmersionSerreVanishing: the first two cannot supply an acyclic import here.
   The planned projective-space node records a field-only Lean theorem, inadequate for
   the general Noetherian base. Replaced that planned input by the existing ring-general
   closed-immersion Serre theorem, applied to each coherent residue coefficient; its
   docstring's projection-formula explanation remains valid. The ample immersion and
   residue transport are substantial unfinished work, not a few-minute lemma closure.

4. **Top-down proof and pruning: PASS.** Checked the coefficient-independent local
   bound's qcqs hypotheses on g, compactness of affine V, domination by Finset.sup,
   gluing zero over the finite cover, and domination of every threshold by the finite
   sum. The q>=d branch uses the degree bound and q<d uses the fixed-degree lemma;
   q=0 imposes no threshold, and d=0 leaves an empty sum and only the first branch.
   Read the source comparison, affine higher-image sections and open-restriction
   declarations: their directions match the additive equivalences and `of_iso` calls.
   The tilde counit is invertible by quasi-coherence, so zero sections imply zero object.
   Each new proof import supplies a used declaration or instance (ProjectionFormula
   supplies invertible tensor-power and tensor quasi-coherence instances). No shorter
   applicable acyclic library theorem was found. Completed No longer needed with the
   fourth removed original dependency, proper-base-change. The unit's realized statement
   and step lists are empty; the proof still uses the unit's projective/Serre and
   Cech-derived route, without changing a unit or chapter statement.

5. **DAG agreement: PASS after repair.** Diffed the existing node: only proof,
   proof_deps and proof_origin change. Each actual proof dependency appears in a step,
   and proof_deps is their union. Checked the new node's signature verbatim, source,
   self-contained hypotheses, statement dependencies, ancestry, chapter/unit, searches,
   status and created/Lean records. Its steps now name the ring-general closed-immersion
   theorem rather than the field-only projective-space attachment. It uses that theorem
   from the neighboring proper-base-change unit as the projective tool needed for the
   same residue argument; no alternate unit route is introduced.

Changes by the second reader: added the new module's blueprint tag, completed the
pruning report, repaired the fixed-degree node's Noetherian-ring proof plan, and wrote
this reading. No Lean statement, definition or proof body was changed. One original
hole closed and one new hole added: net zero, a decomposition, not a sorry-free result.
