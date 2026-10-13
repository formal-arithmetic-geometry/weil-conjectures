## What changed

Completed the saved matrix reduction of
`AlgebraicGeometry.affineBasisDualIso_naturality` in
`Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality`, with its existing
signature unchanged. The theorem now has a complete Lean proof from the
free-sheaf transpose calculation and the sheafified algebraic dual-basis
matrix component.

`Sheaf.AlgebraicGeometry.FreeSheafDualTranspose` retains the proved
`AlgebraicGeometry.freeSheafDualTranspose_component` from the saved attempt.
`Sheaf.AlgebraicGeometry.AffineBasisDualMatrix` states the strictly smaller
remaining component theorem: it compares scalar entries of two sheafified
algebraic maps, without internal sheaf Hom.

Refactored the data to shared coordinate isomorphisms in the underlying
sheaf category. `affineBasisSheafIso` abbreviates that construction.
`affineDualTransportIso` constructs the same composite with explicit fields
and proved inverse identities; `affineBasisDualIso` uses that transport.
Its forward-map formula is proved through the generic transport equation.
Generic categorical cancellation assembles the formulas without rewriting
concrete colimit maps. No data come from a theorem left sorry. Added a proof
import of FreeSheafDualTranspose and a public import of AffineBasisDualMatrix,
whose coordinate definitions are used by the public data constructions.

Validation: all three delivered modules compiled in import order without
warnings (about 6, 33, and 30 seconds). The original direct consumer
`Sheaf.AlgebraicGeometry.AffineFiniteFreeDualComplexComparison` compiled
unchanged against the new module in 14 seconds. No forced adaptation is needed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.affineBasisDualIso_naturality`
(node `lem-sc-affine-finite-free-dual-naturality`). Its proof is a decomposition,
not a net reduction in holes: one original hole closed and one lower hole added.

Proved `AlgebraicGeometry.freeSheafDualTranspose_component`
(node `lem-sc-free-sheaf-dual-transpose`). All private categorical assembly,
extensionality, functor-map, and forward-map helpers are proved.

The only sorry in the delivered files is
`AlgebraicGeometry.affineBasisDualMatrix_component`
(node `lem-sc-affine-basis-dual-matrix`). Its module and node give the source,
full component proof plan, and empty-index/zero-ring checks. There is no sorry
in the original item's module or in any definition.

## No longer needed

Removed redundant direct public imports of `Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.LinearAlgebra.Dual.Basis`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: the required public
`AffineBasisDualMatrix` import already exports all three. No original DAG node
or module leaves the import closure. Both new component modules
are necessary: the free internal-dual transpose calculation and the sheafified
algebraic dual-basis calculation supply different sides of the matrix argument.
The shared coordinate definitions also use the original associated-sheaf
constructions. The unit record sk-thm-picard-duality has no realized statement
or step bypassed by this reduction. No principal-open gluing lemmas beyond
the recorded matrix-component argument are imported into the main proof.

## Where the brief, the DAG or earlier work was wrong

The saved attempt left the original theorem sorry, so its partial component
work alone was not a delivery. The mathematical reduction was sound; concrete
projection conversion and rewrites triggered kernel or file timeouts.
Shared data, explicit transport fields, proved projection formulas, and a
fully abstract categorical assembly repair that failure. No statements were
found false, and no existing signature was weakened.

## New nodes

`lem-sc-free-sheaf-dual-transpose` records the proved transpose component of
the canonical internal dual of finite free sheaves.

`lem-sc-affine-basis-dual-matrix` records the remaining scalar component
identity for sheafified algebraic module duals, strictly below the naturality
square. Both nodes were retained from the saved attempt and checked against
their Lean signatures. The existing naturality node now follows the actual
matrix and categorical cancellation proof.

Definition change records:
`coord/changes/affineBasisSheafIso.md` and
`coord/changes/affineBasisDualIso.md`. No existing downstream module is adapted.


## Second reading by X2

1. Compared the item module with the repository by diff. The naturality theorem
   signature is byte-for-byte unchanged. The two definition refactors and the
   def-to-abbrev change are declared in their change records. Unfolding the shared
   coordinates gives the original basis constructions; the explicit transport
   fields give the same composite and inverse. No hypothesis, conclusion, or
   target meaning is weakened. Local source search confirms that the only
   external textual user is AffineFiniteFreeDualComplexComparison; its original
   source is compiled unchanged against this delivery. Verdict: pass.
2. Compiled all three delivered modules separately with lcompile.py, with no
   errors or warnings. Scanned the delivered Lean files for forbidden constructs
   and holes. The only sorry is affineBasisDualMatrix_component; no definition
   contains a hole or obtains arbitrary data from an unproved existence theorem.
   A scratch import printed axioms for all five public constructions and all
   three public theorems. The constructions and freeSheafDualTranspose_component
   use only propext, Classical.choice, Quot.sound. The matrix component and the
   main naturality theorem additionally use sorryAx, exactly as reported.
   Verdict: pass as a decomposition, not a completed axiom-free naturality proof.
3. Read the matrix component statement, docstring, and node. Both sides have
   the coefficient bM.repr (f (bN j)) i; dualBasis_repr supplies the algebraic
   equality, and the defining colimit and restriction comparisons carry the
   generators and projections. Empty indices give no components, rank-one maps
   give the same scalar, zero maps give zero, and the zero ring gives zero on
   both sides. No internal Hom appears, so this is a strictly smaller step,
   not a restatement of naturality. Independent leanfinder search for
   sheafification of transpose coordinates, loogle search for Basis.dualBasis,
   and grep for dualBasis_repr/toMatrix_transpose found the algebraic identities
   and free-sheaf generator lemmas, but no existing sheafified component theorem.
   The colimit comparison work is substantive and is retained as the single
   named hole. Verdict: true and needed, with complete proof plan and node.
4. Read the proof from its final categorical cancellation back to finite matrix
   extensionality and the two component identities. The free internal-dual
   component is actually proved, so the reduction removes that part of the
   original obligation. No shorter already-proved comparison was found. The
   proof-only transpose import is plain import; the coordinate module must be
   public because public definitions use its constructions. Removed three
   redundant direct public imports supplied by that module. Both old proof
   dependencies (the tilde construction and internal Hom) remain needed through
   the definitions/component nodes; neither is claimed pruned. The unit
   sk-thm-picard-duality has empty realized entries, and no unit statement or
   step is bypassed. Verdict: pass.
5. Compared the node proof steps and dependency unions with the Lean reduction,
   and the new node signatures with their actual theorems. Both new nodes have
   source, proof plan, search records, provenance, blueprint route, chapter,
   unit, creation metadata, and Lean records. The main node names exactly the
   two component steps used by its proof. Verdict: pass.

Second-reading changes: removed the three redundant direct imports above and
added this review. No theorem proof, existing signature, definition body, or
remaining hole was changed. One original hole is closed by adding one smaller
hole; net holes closed is zero. The additional free-dual component is proved.
