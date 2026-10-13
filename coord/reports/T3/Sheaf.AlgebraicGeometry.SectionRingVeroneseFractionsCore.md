## What changed

Exposed the canonical fraction map as the named noncomputable additive homomorphism
`sectionRingVeroneseFractionCanonicalMap`, defined as the inverse of the explicit
Veronese fraction equivalence. The core theorem now states bijectivity of this
canonical map directly. Its proof is the bijectivity theorem for the underlying
additive equivalence.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is proved
with no `sorry`. No new holes were added.

## No longer needed

No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly rejected the former bare `Nonempty` conclusion.
The earlier repair stated bijectivity through the inverse equivalence but did not
name the canonical map itself. This delivery exposes that map and states the
required bijectivity directly.

## Earlier second reading (a previous round; superseded)

The canonical map definition and theorem compile with the prescribed launcher. The
statement change is recorded in
`coord/changes/sectionRing_veronese_fraction_core.md`; the existing upstream
statement-change record is retained under `previous` in the DAG node.


## Second reading by T3

1. Compared the delivered module with the repository version. The original theorem
   signature is replaced only by the declared repair, and the new canonical map is
   documented in the change record; no unrelated declarations changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no errors, no `sorry`, and no
   forbidden declarations. The proof is exactly the bijectivity theorem for the
   inverse additive equivalence. Verdict: pass.
3. Checked the repaired statement and canonical map against the source description
   and the existing equivalence. The map has the stated domain and codomain and the
   theorem asserts bijectivity, with no weakened conclusion or added hypotheses.
   Verdict: pass.
4. The proof follows the existing Veronese fraction equivalence node and introduces
   no unnecessary imports or split-off holes. Verdict: pass.
5. The node statement, proof, dependency, and origin describe the delivered canonical
   map and its use of `sectionRingVeroneseFractionEquiv`; the unit route is unchanged.
   Verdict: pass.

Changed: added the canonical additive homomorphism definition, corrected the change
record signature, and added this second-reading record.
