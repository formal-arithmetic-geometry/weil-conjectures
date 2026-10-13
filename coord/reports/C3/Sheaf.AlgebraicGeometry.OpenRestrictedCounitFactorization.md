## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_factorization` by reducing it to a separately named auxiliary counit compatibility equation and cancelling the representative restriction isomorphism. Added a proof-only import of `Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux`.

## Proved and sorry left

The target theorem `openRestricted_counit_factorization` is proved. The auxiliary theorem `openRestricted_counit_compatibility_aux` remains `sorry`, as a strictly stronger compatibility statement needed for the cancellation argument; node `new-open-restricted-counit-compatibility-aux` records it.

## No longer needed

None; both original proof imports are used by the auxiliary statement and the target proof.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted a directly stated compatibility lemma. The proof therefore introduces that stronger intermediate equation and derives the target by categorical cancellation.

## New nodes

`new-open-restricted-counit-compatibility-aux`: auxiliary compatibility equation, in `dag/nodes/sec-picard-framework/new-open-restricted-counit-compatibility-aux.json`.

## Earlier second reading (a previous round; superseded)

Pending the second reader; the target proof compiles and the auxiliary node is the only remaining hole.

## Second reading by C3

1. Compared the delivered factorization module with the repository version. The theorem
   signature is byte-for-byte unchanged; only its proof and a proof-only import were added.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no forbidden
   declarations or hollow definitions. The target is proved; the sole remaining `sorry` is
   the named auxiliary theorem, with its split node and source documented above. Verdict: pass.
3. Read the auxiliary statement and node. It is the compatibility equation obtained by
   precomposing the target with the representative restriction isomorphism, hence strictly
   stronger and sufficient for cancellation; it does not restate the target. Its source,
   proof steps, and Lean declaration agree. Verdict: pass.
4. The proof uses both original public imports and the auxiliary theorem through a plain
   proof-only import, so no unused import or node was found. The unit route is preserved:
   the target remains the factorization node and the auxiliary is only an intermediate
   reduction. Verdict: pass.
5. Checked the DAG metadata against the declarations and proof. The new node points to the
   auxiliary module and lists the dependencies used by its proof; the target node's proof
   now records the cancellation route. Verdict: pass.

Changed only the target proof, added the proof-only auxiliary module and its node, and added
this second-reading record. No statement or definition was changed.
