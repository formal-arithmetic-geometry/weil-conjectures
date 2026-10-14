## What changed

Closed `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian` by
assembling a pointwise finite-pushforward detector with a Noetherian module finite-selection
statement. Added the detector and selection modules and their DAG nodes. The existing
normal-constant wrapper and its two proof-only split modules remain in the delivery.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`.

The following named obligations remain sorry:

- `AlgebraicGeometry.Etale.exists_noetherian_stalk_detector`
  (`new-lem-weil-pbc-noetherian-stalk-detector`);
- `AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_module_stalk_injective_general`
  (`new-lem-weil-pbc-noetherian-module-finite-selection`);
- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit`
  (`lem-weil-pbc-normal-constant-generic-unit`);
- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_open_unit`
  (`lem-weil-pbc-normal-constant-generic-open-unit`).

## No longer needed

Removed the direct `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection` import and the
finite-carrier comparison and selection route. The proof now uses the Noetherian module
selection intermediate directly. The discarded non-finite-coefficient branch split is not
delivered because the general detector and selection statements cover the original
Noetherian-ring hypothesis.

## Where the brief, the DAG or earlier work was wrong

The earlier route split on whether the coefficient ring had a finite underlying type, which
introduced a branch with the same conclusion as the target and could not be a strict
reduction. The corrected route states two genuine parts of the planned proof: pointwise
finite-stage detection and finite selection of stalk-injective maps over a Noetherian ring.

## New nodes

- `new-lem-weil-pbc-noetherian-stalk-detector`: pointwise finite pushforward detector.
- `new-lem-weil-pbc-noetherian-module-finite-selection`: finite selection of module stalk
  detectors over a Noetherian coefficient ring.

## Second reading by Q3

1. **Statements and signatures.** I compared every delivered existing module and declaration
   with `sheaf-dag`. The target theorem signature is byte-for-byte unchanged. The generic-point
   and open-unit modules are unchanged; the two detector and finite-selection declarations are
   new split statements with their own nodes.
2. **Proof checks.** All five delivered Lean modules compile locally. The target theorem is
   closed without `sorry`; the only remaining `sorry`s are the two named split theorems, each
   documented and represented by a DAG node. No axiom, `unsafe`, `opaque`, `extern`, or hollow
   definition was introduced. The restored normal-constant modules retain their previously
   checked proofs.
3. **New statements.** I checked the detector statement against Stacks Tag 09Z6 (3), including
   the pointwise geometric-stalk condition and finite-module value. I corrected the finite
   selection proof description to use the Noetherian-object finite-selection argument from that
   lemma, rather than the earlier unsupported generic-kernel propagation claim. Both new nodes
   record the corresponding source and proof route.
4. **Pruning.** The old finite-carrier selection import is removed because the target proof now
   uses the Noetherian detector and selection interfaces. No existing proof dependency or module
   was removed from the normal-constant route, and the unit `sk-thm-p1` route is preserved.
5. **DAG agreement.** The target node's `proof`, `proof_deps`, and `proof_origin` now match the
   two split declarations used by the Lean proof. Existing node metadata was restored unchanged;
   only the target node's stage-3-owned proof fields and the two new node files differ.

I restored the previously proved generic-point and open-unit module bodies after finding that
the worker's version replaced them with `sorry`. I also restored their existing DAG metadata and
updated the finite-selection node and module documentation to describe the Stacks Noetherian
finite-selection route accurately.
