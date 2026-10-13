## What changed
Added the proof-only import of `SelfTorProjectionHomologyTermwise` and proved
`AlgebraicGeometry.nonempty_selfTor_projection_homology` by composing the termwise
representative isomorphism with the homology isomorphism induced by the supplied
complex isomorphism. Added the strictly simpler intermediate theorem
`AlgebraicGeometry.nonempty_selfTor_projection_homology_termwise` as a named pending
step with its DAG node.

## Proved and sorry left
The target `nonempty_selfTor_projection_homology` is proved. The new intermediate
`nonempty_selfTor_projection_homology_termwise` remains `sorry` and is recorded by
node `lem-pc-self-tor-projection-homology-termwise`.

## No longer needed
None; all existing imports remain part of the declared projection-formula route.

## Where the brief, the DAG or earlier work was wrong
The original node combined the termwise projection computation and arbitrary
representative transport in one hole. Splitting the termwise computation into a
strictly simpler theorem makes the transport proof explicit and checkable.

## New nodes
`lem-pc-self-tor-projection-homology-termwise` in
`dag/nodes/sec-picard-framework/lem-pc-self-tor-projection-homology-termwise.json`.

## Earlier second reading (a previous round; superseded)
Pending the independent second reading; the target proof compiles and the new node is
strictly simpler than the target because it omits arbitrary representative transport.

## Second reading by R4

1. Compared the delivered target module with the repository version. The existing
   theorem signature is byte-for-byte unchanged; the only interface addition is the
   declared proof-only import of the new termwise module. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`; both compile without
   errors. The target proof contains no new `sorry`, while the named intermediate
   theorem is the sole split-off hole. A scratch `#print axioms` reports only the
   permitted axioms together with `sorryAx` from that open theorem. Verdict: pass.
3. Checked the split-off statement against the target: it removes the arbitrary
   representative `Q` and isomorphism `e`, so it is strictly simpler and needed for
   the transport proof. Its docstring, node, source, and declaration agree, and no
   duplicate declaration was found in `lean/`. Verdict: pass.
4. The proof uses the termwise theorem, `HomologicalComplex.homologyMapIso`, and
   functorial `mapIso`; the existing projection-formula imports remain the route's
   declared dependencies. Removed an unused local complex binding. Verdict: pass.
5. The target node's statement and proof dependencies are unchanged, and the new
   node records the termwise substep. The unit route is preserved because the
   target still composes the termwise projection result with representative
   transport. Verdict: pass.

Changed only the target proof by removing an unused local binding; no imports or
statements were otherwise changed. The split-off termwise theorem remains open as
documented above.
