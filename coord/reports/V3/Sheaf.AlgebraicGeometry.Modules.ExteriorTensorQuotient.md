## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient in favor of its
proved official twin, as assigned in coord/retire-items.tsv and the 2026-10-20
retirement hand-off. The item file is listed in deleted.txt and absent from the
sandbox. Its node new-exterior-tensor-quotient now points to the official
exteriorTensor_quotient_exists, with its exact exteriorPower/wedge signature;
the node's proof record describes that already proved official construction.

The two constructions use different restrictions. New module
ExteriorSheafTensorQuotientComparison transports the official quotient via the
existing exteriorSheafPowerIso isomorphisms, retaining the objects and section
formula needed by the consumers. The proof constructs the conjugate map, obtains
epimorphy by composition, and evaluates its cancellation equation on wedges.
A private proved helper computes the inverse tensor comparison on wedge sections.

DeterminantWedgeMorphismGlue and DeterminantWedgeQuotientFactor replace one private
import and one proof call each with exteriorSheafTensor_quotient_exists.
Their public statements are verbatim unchanged. Their two DAG proof records
now cite the compatibility theorem. No upstream source, target, or definition
is edited. Change record: coord/changes/V3-retire-exterior-tensor-quotient.md.

## Proved and sorry left

The assigned item has zero textual holes at the current base. Closed 0 of 0
sorries; added 0; split off 0. No sorry remains in any delivered module.
This is a retirement and fully proved API transport, not a hole-closure claim.

New public theorem AlgebraicGeometry.Scheme.Modules.exteriorSheafTensor_quotient_exists
(node lem-sc-exterior-sheaf-tensor-quotient-comparison) is fully proved from the
official quotient theorem and the already proved comparison. The private
comparison_inv_tensor_wedge is also fully proved. Both consumer proofs are
retained. lcompile.py --all compiled the new theorem (3.3 s) and the two consumers
(1.9 s each) cleanly, with no warnings. Delivery preflight additionally checks
the axioms of every delivered declaration. The three unchanged immediate
downstream consumers also compile against the sandbox outputs:
DeterminantLiftWedgeKernel (1.9 s), DeterminantWedgeMorphismLocalAt (8.6 s),
and DeterminantWedgeMorphismLocal (2.1 s), all without warnings.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient and both direct
imports of it. The handwritten duplicate exterior presheaf map, its naturality
proof, sheafification formula and epi-cancellation proof disappear with the twin.
The official construction and its extensionality dependency remain intact.
The original node is preserved and redirected, not deleted. The consumers now
reach it through the proved comparison transport. No mathematical unit step,
other module, or source-library declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but the current file is
already completely proved. The current queue and retire-items.tsv identify the
actual assigned repair: retirement of its duplicate, including both consumers.
No compiling no-op is delivered. The earlier P7 extensionality retirement supplies
the comparison needed here; rebuilding that comparison is unnecessary.

The API difference is substantive: official exteriorPower/wedge and older
exteriorSheaf/exteriorSheafSection are canonically isomorphic. The delivery uses
the existing constructed isomorphism, rather than weakening any statement or
assuming the two objects equal. The proof applies to degree zero, empty opens,
the empty scheme and zero rings. Both edited consumers were unclaimed. All
source-library declarations, public consumer signatures and the unit route stay
unchanged.

## New nodes

lem-sc-exterior-sheaf-tensor-quotient-comparison records the proved transport of the
official exterior tensor quotient to the older exteriorSheaf construction. It
uses new-exterior-tensor-quotient and lem-sc-exterior-sheaf-power-comparison;
the consumers now cite this node. The source remains the determinant paragraph
of the Riemann--Roch blueprint, and the proof records the canonical conjugation
argument required by retirement. LeanSearch, LeanFinder, Loogle, msearch grep and
direct source searches found the generic tensor/isomorphism APIs and the official
quotient, with no existing quotient comparison. No new sorry is introduced.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
