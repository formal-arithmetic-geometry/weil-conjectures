## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleGeometricStalk_sheafification`, keeping its
statement and public imports unchanged. Added one proved private helper,
`lift_geometricPoint_cover`: base change a covering family to the fixed `Spec Ω`,
choose a nonempty member, and use the existing source theorem
`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale` to obtain its section.

The pointed refinement condition constructs a site point using Mathlib
`Point.ofIsCofiltered`. Its fiber is a colimit of the specified neighbourhood
diagram. The proof identifies the actual `colim.map` with the fiber map conjugated
by the two colimit isomorphisms; Mathlib makes the fiber of the sheafification unit
an isomorphism. Functoriality and `toSheafify_naturality` prove the second conjunct.
The node records this route. No statement, definition, or consumer was changed.

The single-file compile is clean (4.4 seconds). The axiom probe reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the target and the source section
theorem. The cofilteredness dependency also passes the same axiom check.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtaleGeometricStalk_sheafification`
(node `lem-cbc-proetale-sheafification-geometric-stalk`).
The new private helper is proved. Zero holes remain in the item; zero holes were
added and zero statements are split off. The temporary isomorphism split was
removed from the sandbox; it is not part of this delivery.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.RingTheory.IndPrincipalZariski`
- `Sheaf.RingTheory.WeaklyEtaleField`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.FieldTheory.IsSepClosed`
- `Mathlib.CategoryTheory.Sites.LocallyBijective`
- `Mathlib.CategoryTheory.Sites.Localization`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`

Replaced them with proof imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`,
`Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered`, and
`Mathlib.CategoryTheory.Sites.Point.Skyscraper`.

The following old proof dependencies are no longer used as separate statements:
`def-pc-fibre-product`, `def-weil-affine-spectrum`, `def-weil-geometric-point`,
`def-weil-pbc-category-colimit`, `def-weil-pbc-ind-etale-algebra`,
`def-weil-size-convention`, `lem-galois-fpqc-covering-base-change`,
`lem-weil-pbc-separable-extension-embeds-separably-closed`,
`lem-weil-pbc-site-sheafification-iso-locally-bijective`,
`lem-weil-pbc-weak-etale-field`,
`lem-weil-pbc-weakly-etale-composition-base-change`, and
`lem-weil-pbc-weakly-etale-source-locality`.
Their functions are handled by existing source or Mathlib results. Removed the
four obsolete top-level tool approvals for weakly etale composition/base change,
source locality, weakly etale field algebras, and separably closed embeddings.
This is pruning for this proof; other target paths may still use these nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the target or the unit route was found. The existing
source theorem for a nonempty weakly etale scheme over an algebraically closed
field avoids repeating the residue-field construction. Once the geometric
cover-lifting condition is proved, Mathlib supplies both the site point and the
sheafification comparison, so separate representative-surjectivity and
representative-injectivity lemmas are unnecessary. The fixed field and all
universes are preserved, including the initially small neighbourhood category.

## Second reading by F3

1. **Signatures and statements — pass.** Compared the delivered module and node with
   the repository versions. The theorem signature, all existing declarations, and the
   target statement are unchanged; the node proof and proof dependencies match the
   delivered proof.
2. **Proof and axioms — pass.** Compiled the module with `lcompile.py`; the target and
   its source helper have no `sorry`, forbidden declarations, or extra axioms. The axiom
   probe reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Split statements — pass.** No split-off theorem or new node was added. The private
   lifting helper is fully proved, and the existing node statement is true and unchanged.
   The duplicate search found no existing declaration that the proof should reuse.
4. **Pruning and route — pass.** The proof follows the unit route through the pointed
   neighbourhood category, uses the shortest available Mathlib point and sheafification
   results, and removes the obsolete imports and proof dependencies listed above.
5. **DAG agreement — pass.** The node's four proof steps, `proof_deps`, `proof_origin`,
   and `tool_uses` agree with the Lean proof; the unit's realized route is unchanged.

Changed the stale theorem proof docstring to describe the actual helper, point-fibre,
sheafification, and naturality argument. No mathematical or interface change was needed.
