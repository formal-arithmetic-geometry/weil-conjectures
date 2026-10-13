## What changed

Replaced the sorry in AlgebraicGeometry.exists_tensorHomUncurry_descent_representative
with a compiled construction of the family. A local relation records chain presentations
of an input and their localized outputs using object equalities and HEq. The proof derives
uniqueness from the new representative-coherence theorem, chooses from ExistsUnique on
represented inputs, and assigns zero elsewhere. The normalization clause follows from an
explicit witness and uniqueness. The existing signature and docstring are unchanged.
Added the proof-only import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence.
The coherence module also imports its five remaining planned proof-dependency modules
privately, as required for a still-open theorem; its differential statement dependency
is the only public import.
No existing interface, target, definition or visibility changes.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_tensorHomUncurry_descent_representative
(lem-pc-tensor-hom-uncurry-descent-representative), from the new coherence theorem.
There are no sorries left in the item.
Added: AlgebraicGeometry.tensorHomUncurry_representative_coherence
(lem-pc-tensor-hom-uncurry-representative-coherence), one whole-proof sorry in its own module.
This is a decomposition: one hole closed, one strictly intermediate hole added, net zero.
The new theorem compares two specified chain presentations; it does not assert or construct
the function family. All relation construction, uniqueness, conditional extension and
normalization are proved in Lean in the item.

Both modules compile cleanly through lcompile.py --all. The zero and identity-presentation
cases of coherence have identical outputs; arbitrary unbounded complexes are retained.
The second complex is not assumed K-flat: its replacement and cancellation remain part of
the coherence proof. Empty representation fibers get zero. The conditional choice uses
ExistsUnique, and the unique output is proved using the named theorem; no arbitrary data
are obtained from an unproved existence result.

## No longer needed

None pruned. No imports were removed. The original direct proof dependencies
lem-pc-kflat-resolution (Sheaf.Algebra.Homology.KFlatResolution),
lem-pur-hom-kflat-into-kinjective (Sheaf.Algebra.Homology.KInjectiveHomComplex),
lem-weil-pbc-kinjective-hom-derived (Mathlib.Algebra.Homology.DerivedCategory.KInjective),
lem-pur-hom-complex-global-cochains (Sheaf.Algebra.Homology.HomComplexGlobalCochains)
and lem-pc-tensor-hom-uncurry-differential remain needed in the new coherence argument.
They are no longer direct dependencies of the extension proof, but are not claimed pruned.
The statement import CanonicalTensorHomUncurryDifferential remains necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The original node combines the geometric independence
argument with an elementary extension construction. The available dependencies do not
state the cross-presentation equality needed by that construction. This delivery makes
that gap a precise theorem and completes the extension step.
The cited literature/stacks-project files are absent on this machine; the three original
Stacks sources were read online at https://stacks.math.columbia.edu/tag/08DJ,
https://stacks.math.columbia.edu/tag/0A90 and https://stacks.math.columbia.edu/tag/0A96.
Blueprint search for uncurry returned no matches; evaluation matches did not assert this
cross-presentation equality. The unit realization lists are empty, and no unit-level
statement or route is changed. LeanSearch was unavailable (HTTP 500); LeanFinder returned
Tor and monoidal-localization lemmas, Loogle returned generic FactorsThrough extension,
and grep found only those extension tools, not sheaf evaluation coherence.

## New nodes

lem-pc-tensor-hom-uncurry-representative-coherence is stated in
lean/Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryRepresentativeCoherence.lean.
It isolates the original proof's sentence about common K-flat resolutions making values
of two descriptions of the same literal derived input agree. Its docstring and DAG proof
record resolution, homotopy evaluation, naturality and cancellation, with the original
proof dependencies and the Hom-complex/total-tensor comparison. Equality transport rather
than arbitrary isomorphism transport is sufficient for this item. No change record is
needed: only proofs and a new proof dependency change.

## Second reading by E1

1. PASS: diffed both delivered Lean modules against the repository. The item changes
   only its proof and adds a private proof import. The entire existing theorem signature,
   docstring, visibility and options are unchanged. The coherence module is new. No target
   or definition changes and no forced adaptations or change records are required.
2. PASS: compiled both modules in import order with lcompile.py --all. Compiled scratch
   copies with #print axioms for both declarations: precisely propext, Classical.choice,
   Quot.sound and sorryAx. The item has no local sorry; the sole added sorry is the named
   coherence theorem, with source, complete prose argument and node. Neither file has
   axiom, unsafe, opaque, implemented_by or extern, or a holed definition. The relation
   fixes the output uniquely before Classical.choose is used; the fallback is explicit zero.
3. PASS as a decomposition: checked the coherence signature against its prose and read
   Stacks Tags 08DJ, 0A90 and 0A96 independently. K-flat replacement of the second input,
   Hom into K-injectives, natural componentwise evaluation and localization give the stated
   comparison; no boundedness or K-flatness of L or L' is required. Identical presentations
   with identical maps give HEq.rfl; zero maps evaluate to zero, and empty representation
   fibers cause no constraint on the explicit fallback. The lemma is the two-presentation
   uniqueness step, rather than the function-family existence conclusion of the item.
   Independent LeanFinder search for homotopy invariance of evaluation found
   DerivedCategory.Q_map_eq_of_homotopy and generic localization results, which need the
   missing evaluation homotopy. Loogle HomotopyCategory and grep for uncurrying/homotopy
   and evaluation/naturality found no direct replacement. Also searched repository and
   upstream HomTensor, internal-Hom and module files; the available Hom-total-tensor
   isomorphism and global-cochain comparison are intermediate tools already in the node.
   Closing this coherence theorem requires the substantial comparison/homotopy argument;
   it is not a few-minute application. One upper hole closed and one lower hole added,
   net zero; this delivery is not a complete axiom-free proof of the item.
4. PASS: checked the extension construction top-down. It uses exactly the coherence
   hypothesis to prove single-valuedness and performs extension and normalization itself.
   The sole public import supplies the statement's models; the private import supplies
   coherence. The new open theorem keeps private imports for its planned dependencies.
   No old proof dependency is pruned: all five are retained in the coherence plan and
   listed above. The unit sk-thm-picard-duality has realized.statement = [] and
   realized.steps = [[]]; this below-unit split changes no unit statement or route.
5. PASS after repairs: the existing node changes only proof, proof_deps and proof_origin,
   matching the actual uniqueness/extension proof. The new node has its source, searches,
   creation, blueprint, chapter, unit and Lean record; its dependency list is the union of
   its proof-step uses. Corrected its lean.statement to the exact multiline Lean signature.
   Added private imports for KFlatResolution, KInjectiveHomComplex, derived-category
   KInjective, HomComplexGlobalCochains and HomTensorTotal, so the open theorem's module
   contains its stated proof plan. No mathematical proof or existing signature was changed.
