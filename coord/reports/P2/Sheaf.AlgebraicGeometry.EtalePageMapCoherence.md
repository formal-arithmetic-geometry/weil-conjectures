## What changed

Proved `AlgebraicGeometry.Etale.etale_page_map_coherence` in
`Sheaf.AlgebraicGeometry.EtalePageMapCoherence`, preserving its full signature,
visibility, docstring, imports and file options. Added the proved private helper
`apply_eq_index`: equality induction for applying a dependent family of maps to
an argument family indexed by an equality. This keeps kernel reduction of scheme
pullbacks out of the equality-induction proof itself.

The local `identity_law` transports the scheme arrow with its complex comparison,
then uses `hid`; the identity-complex comparison is the identity. The local
`composition_law` transports the composite arrow together with its comparison,
then applies `hcomp`. The first two conclusions follow by substituting `hidentity`
and `hcomposition`. For the cocone conclusion, apply `composition_law` using
`(c.w f).symm`; precompose `L.w f.op` with `(eG i).inv`, substitute `hG`, reassociate
and cancel the inverse-hom pair. Apply congruence under `M` to this equality.
This implements all three existing node proof steps, with no changed route or
proof dependencies and no changes to a unit statement or step.

Searches: LeanFinder for dependent transport of scheme-arrow maps returned generic
scheme congruence results, with no match for this theorem. Loogle did not recognize
`NatIso.mapHomologicalComplex` in its index. The required grep search and direct
library searches found the homological-complex identity/composition APIs and
`Cocone.w`, used here; no existing proof of this page-map coherence theorem was
found. The single-file compile succeeds.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.etale_page_map_coherence`
(node `lem-weil-pbc-etale-page-map-coherence`). All three conjuncts are proved.
No holes added, no intermediate statements split off, and no `sorry` remains in
any delivered declaration. The private helper `apply_eq_index` is proved by
equality induction and reflexivity.

## No longer needed

None. The sole public import `Sheaf.Paper.EtaleTermwiseHypercohomology` is needed
by the unchanged statement. No proof imports were added or removed. The node's
`proof_deps` is already empty; its existing three elementary proof steps describe
the proof delivered, so no DAG update or module pruning is necessary.

## Where the brief, the DAG or earlier work was wrong

The previous attempt correctly identified dependent transports, but they do not
prevent a complete proof. Generalize the arrow and its equality before supplying
the complex map; equality induction then transports both together. Generic
`apply_eq_index` also avoids expensive kernel reduction under these transports.
The supplied DAG plan is valid and has been implemented without new assumptions.
No statement, definition, target, public interface, or other module was changed.

## Second reading by P2

1. Compared the delivered module with the repository version. The theorem signature,
   visibility, docstring, imports, and options are unchanged; only a private helper and
   the proof body were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the delivered
   declarations contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`.
3. Checked the proof route and the node statement. Equality induction transports the
   dependent map families before applying `hid` and `hcomp`; the cocone step uses `hG`
   and `Cocone.w`. The three conclusions are exactly the node's explicit equalities.
4. Searched the repository and the recorded Mathlib searches for an existing theorem or
   duplicate split statement. None was found; no new statement or node was introduced.
5. Checked pruning and unit preservation. The existing public import remains needed for
   the theorem statement, the node's proof dependencies remain empty, and all three
   elementary proof steps in the DAG are realized by the delivered proof.

Verdict: the proof is valid, the target statement is unchanged, and the delivery is
ready for preflight.

Changed during second reading: added this review record only.
