## What changed

Proved `AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_inv_leg` in
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeLeg`. A proved private
`mapped_iso_inv_leg` handles inversion, functoriality, and associativity in arbitrary
categories. The main proof applies it to the explicit inverse-image composition
comparisons and the mapped coefficient colimit injection. All existing signatures,
docstrings, imports, and the node's proof route are unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_inv_leg`
(node `lem-sbc-restricted-affine-single-cone-leg`). No `sorry` remains in the module.
No new holes, nodes, or dependency theorems were added. The private helper is proved.
The single-file compilation completed without warnings in 44.7 seconds.

## No longer needed

None. The three definition nodes in the existing proof plan are all used through
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps` and its public imports.
No additional proof imports are needed.

## Where the brief, the DAG or earlier work was wrong

The previous broad simplification candidate exceeded the compiler's 60-second limit.
Naming the comparison factors and applying a general proved categorical identity
avoids expensive repeated unfolding during kernel checking.

The published cache lacks `RestrictedAffineSingleMaps.olean`. For local checking,
an unchanged copy of that existing dependency was compiled with the supported
`lcompile.py --all` command into this sandbox's `.lbuild`. Its source copy was then
removed; it is not part of the delivery. The required single-file compile uses the
sandbox artifacts. No shared compiled cache or library source was changed.

## Second reading by P4

1. PASS: Compared the sole delivered module with the repository using `diff -u`.
   The existing theorem signature, docstring, module header, and public import are
   byte-for-byte unchanged. The only additions are the proved private helper and
   the replacement of the theorem's `sorry` by a proof. No definition or target
   statement changed; no change record is required.
2. PASS: Independently compiled the module with `lcompile.py`: no errors or warnings,
   41.2 seconds. A scratch copy with `#print axioms` for both
   `restrictedAffineSingleConeIso_inv_leg` and `mapped_iso_inv_leg` compiled in
   37.5 seconds. Both use exactly `propext`, `Classical.choice`, and `Quot.sound`;
   neither uses `sorryAx`. No `sorry`, forbidden declaration, or data construction
   from an unproved existence theorem occurs in the delivered module. Scratch copy
   removed before delivery.
3. PASS: There are no split-off statements, new public declarations, or added holes.
   Read the private helper: reversing the composite isomorphism gives
   `s.hom` followed by the image of `a.inv`, `b.hom`, and `P.map e.inv`;
   functoriality and associativity combine this with the image of `f`.
   This works for arbitrary categories, identity isomorphisms, and zero maps; it
   requires no nonemptiness or directedness. For empty I the main theorem has no
   index to instantiate, and singleton I requires no extra assumption.
4. PASS: Read `RestrictedAffineSingleMaps`, `RestrictedAffineCoefficientConstruction`,
   and `rawAffineRestrictedCoefficient`. The main proof supplies precisely the
   three comparison isomorphisms and the coefficient colimit injection to the
   elementary helper. The projection identity is proved by pullback simplification;
   proof irrelevance identifies its equality witness with the one in the definitions.
   Searched the library and upstream for the comparison theorem, and Mathlib for
   inverse-composite and mapped-isomorphism lemmas (including an independent
   `msearch.py ... grep` query). The helper already uses the applicable Mathlib
   identities; no shorter complete existing theorem was found. The sole public
   import supplies objects in the signature and is necessary. All three old
   `proof_deps` are used, so `No longer needed: None` is complete. The unit
   `sk-lem-failure-field` and its existing `realized` record are unchanged: no
   unit step or chapter route is bypassed.
5. PASS: Read node `lem-sbc-restricted-affine-single-cone-leg` and its three definition
   dependencies. The node's expansion-and-functoriality proof, `proof_deps`, and
   `proof_origin` accurately describe the implemented proof. No node update is
   necessary and no new node is required for this elementary proved private helper.

Second reading changed only this report. The Lean proof was correct as delivered
and needed no repair. One existing hole closed, zero holes added: a proof, not a
decomposition. No modules or dependency nodes pruned.
