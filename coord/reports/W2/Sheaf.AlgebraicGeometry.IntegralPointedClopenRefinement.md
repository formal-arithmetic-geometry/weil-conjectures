## What changed

Proved `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_clopen_refinement` with its
signature unchanged. Added the proved finite-model theorem in
`Sheaf.AlgebraicGeometry.IntegralPointedEtaleFiniteModel`. It chooses an affine base
neighbourhood, descends a single standard étale pair to a finite subalgebra, and constructs
the finite model, its morphism to V, and its marked point. The main proof applies the
source library's finite pointed-piece theorem, pulls the piece back to X, constructs its
open complement, and verifies both point equations by pullback extensionality.

Removed five proof imports and replaced them by the finite-model module. Existing public
imports and signatures are unchanged. Updated the item's DAG proof route. Recorded the
already proved source-library coefficient-descent and finite pointed-piece declarations
as nodes; these are tools, not new proof obligations. No definitions or existing
interfaces changed; no forced adaptations.

Both delivered modules compile without warnings. `#print axioms` for both the target and
the finite-model theorem lists only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_clopen_refinement`
(node `lem-sbc-integral-pointed-clopen-refinement`).

Also proved `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_etale_finite_model`
(node `lem-sbc-integral-pointed-etale-finite-model`). No holes added, no split-off sorries,
and no sorry remains in any delivered module. This is a proof, not a decomposition.

## No longer needed

The following five proof imports and corresponding planned dependency nodes are no longer
needed by this proof (other targets may still use them):

- `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`;
  `lem-weil-pbc-etale-algebra-filtered-colimit-descent`.
- `Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite`;
  `lem-weil-pbc-integral-algebra-directed-colimit-finite`.
- `Sheaf.Paper.EtaleFiniteDataDescent`;
  `lem-weil-pbc-etale-finite-data-descent`.
- `Sheaf.RingTheory.FiniteOverHenselianLocalProduct`;
  `lem-weil-pbc-finite-over-henselian-local-product`.
- `Sheaf.RingTheory.HenselianEtaleRetraction`;
  `lem-weil-pbc-henselian-etale-retraction`.

The finite coefficient-descent theorem handles the necessary integral approximation
without building strict henselisation or a general inverse-limit descent diagram here.
The finite pointed-piece theorem already supplies the pointed refinement at a finite
stage. The unit record `sk-lem-universal-datum` has no realized node for this item or its
steps; no fixed unit statement or step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The planned five general lemmas do not directly expose the
geometric finite model or the necessary point compatibility; the source library already
proves coefficient descent and the finite pointed-piece result with that compatibility.
The integral disjoint-cover theorem alone is insufficient because it gives an unpointed
map. The replacement preserves the finite approximation and selected-factor argument
from the blueprint's conservativity proof.

Small cases: an empty source admits no t; no surjectivity assumption on f is used;
empty geometric fibres cannot occur with the supplied t; an arbitrary, possibly infinite
integral algebra is handled by finitely many coefficients; V need not be affine or
quasi-compact since one standard étale chart suffices. The section of the selected finite
piece preserves the actual Omega-valued point, not just its underlying topological point.
No arbitrary object is defined using an unproved existence theorem.

Searches ran with msearch: LeanFinder for integral pointed clopen refinement (eight
unrelated étale declarations); Loogle for SplitNbhd (unknown identifier); grep for finite
étale descent (six unrelated Mathlib results); the finite-model, finite pointed-piece,
and standard-pair coefficient searches recorded in the new nodes. LeanSearch returned
HTTP 500 and is recorded as unavailable. The exact source signatures and proofs were
read in PieceSection.lean and StandardEtale.lean. Blueprint searches for pointed étale
finite models, standard étale, and split neighbourhoods returned zero matches.

## New nodes

`lem-sbc-integral-pointed-etale-finite-model`: the proved geometric finite approximation,
strictly a part of the target argument. Its Lean module contains the complete construction
and both marked-point equations.

`lem-sbc-finite-pointed-piece-refinement`: records the existing, proved declaration
`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_pieceFunctor_obj_hom` in
`WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection`. No source module changed.

`lem-sbc-standard-etale-finite-subalgebra`: records the existing, proved declaration
`StandardEtalePair.exists_subalgebra_finite_algEquiv_tensor_ring` in
`WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`. No source module changed.

No change record is needed: all existing statements, definitions, and visibility remain
identical; the helper is a new theorem, and its import in the target is proof-only.

## Second reading by W2

1. PASS. Diffed both delivered modules against the repository: the finite-model module
   is new; the existing target's declaration signature is byte for byte unchanged.
   Its public imports, docstring, namespace, universes and visibility are unchanged.
   Only five proof imports, the proof body and its local elaboration option differ.
   No existing definition or statement changes, and no change record is required.
2. PASS. Recompiled both modules in import order with lcompile.py, without errors or
   warnings. Temporarily appended #print axioms to the target file, compiled it against
   the sandbox helper, then restored it. Both the target and finite-model theorem use
   exactly propext, Classical.choice and Quot.sound. Scanned both delivered files for
   sorry, axiom, unsafe, opaque, implemented_by, extern and skipKernelTC: none occur.
   All chosen data come from proved results; no unproved existence supplies an object.
3. PASS. No split-off sorry exists. The finite-model theorem is strictly the finite
   approximation part of the argument, without a clopen conclusion, and is fully proved.
   Read the upstream standard-etale coefficient-descent proof and finite pointed-piece
   theorem, including their point conditions. The helper handles a non-affine V by a
   single affine chart; integral B need not be finite; the marked point excludes empty
   fibres. The empty family in coefficient descent allows the bottom subalgebra, finite
   as an A-module. No surjectivity of f is required. New grep queries using
   standardEtalePair/subalgebra-tensor/pieceFunctor and a LeanFinder query about pointed
   finite approximation found no duplicate geometric theorem. LeanFinder also found
   Algebra.Etale.exists_subalgebra_fg; read its Mathlib source. It can replace algebraic
   descent, but still needs affine charts, tensor geometry and both point equations, so
   it does not furnish a shorter direct proof of the item or duplicate the helper.
4. PASS. The proof first constructs the finite model, applies the already proved finite
   pointed-piece theorem, then pulls the selected piece back and takes its complement.
   Read every pullback and point equality: hptμ identifies the actual Ω-valued map with
   r, so preservation is stronger than merely preserving its underlying point.
   No open project theorem is used. The removed five imports are exactly all old
   proof_deps, and all five nodes appear in No longer needed. The helper's sole public
   import supplies the neighbourhood operations and basePt in its statement; its proof
   uses the coefficient descent available there. Existing public imports in the target
   remain required by the unchanged interface contract. The unit record's realized
   statement and steps are empty; this route bypasses no realized unit node.
5. PASS after metadata repair. Diffed the old node: only proof, proof_deps and
   proof_origin change. The target's dependencies are exactly finite approximation and
   finite pointed-piece refinement; the helper records local standard-etale structure
   and coefficient descent. Checked the new nodes' statements, source, searches,
   creation metadata, blueprint ancestry, chapter, unit and Lean records. The two
   upstream declarations are recorded as existing proved tools, not added obligations.

Changed only two new-node proof descriptions: the finite-model proof_origin now names
its actual tensor/point construction rather than the finite pointed-piece theorem (used
only by the target); the coefficient-descent node now explains the derivative-localized
pair and mulDerivative equivalence used by the upstream proof. No Lean code changed
in the second reading. The delivery closes one original hole of one, proves its new
helper too, adds zero holes and splits off zero open statements.
