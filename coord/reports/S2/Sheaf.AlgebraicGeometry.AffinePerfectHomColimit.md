## What changed

Retired Sheaf.AlgebraicGeometry.AffinePerfectHomColimit in favor of
WeilConjectures.AlgebraicGeometry.AffinePerfectHomColimit, as assigned by the
retirement queue. Listed the Sheaf file in deleted.txt. Redirected the lean record
of lem-pc-affine-perfect-hom-colimit to the upstream theorem and adjusted its proof
text to name the upstream localization wrappers. Public signatures agree byte for
byte. The three additional Sheaf declarations are proved private helpers, with
no external consumers. Change record: coord/changes/retire-affine-perfect-hom-colimit.md.

## Proved and sorry left

Zero holes initially and zero holes remaining in this retirement packet.
CochainComplex.affine_perfect_hom_colimit already has a complete proof upstream;
no holes closed, no holes added, no split-off statements. No theorem or definition
is weakened. Remote verification compiled an import of the upstream theorem in 1.4 seconds.
#print axioms returned exactly propext, Classical.choice, and Quot.sound.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.AffinePerfectHomColimit, including its private
helpers scalarExtension_isKProjective, Q_map_surjective, and Q_map_eq_iff_homotopy.
No current Lean source imports this module. The upstream twin preserves the
statement and its chain-map/homotopy descent dependencies. No mathematical DAG
node is pruned, and no upstream dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes, but the live queue assigns
this item as retire with zero holes. The retirement inventory lists
Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine as its consumer; that file is
already absent, and the existing upstream consumer already imports the upstream
twin. The node's old lean record still pointed at the redundant Sheaf declaration.
The DIFFERENT classification concerns only three private proof helpers, not the
public theorem's signature. No consumer or source-library adaptation is needed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
