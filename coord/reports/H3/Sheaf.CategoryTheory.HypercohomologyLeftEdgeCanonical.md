## What changed

Closed `CategoryTheory.Functor.cochainHypercohomologyLeftEdge_canonical` without changing
its signature, visibility or public import. The proof constructs the cochain map from
`K.cycles n` placed in degree n to K. It proves the induced cycle map is the prescribed
canonical lift by cancelling the cycle inclusion, and proves that the induced homology
map is the quotient `K.homologyπ n`. Naturality and single-degree normalization then give
the requested equality by associating composites and cancelling the mapped single
homology isomorphism. No object is chosen from an unproved existence statement.

Added `Sheaf.CategoryTheory.HypercohomologyLeftEdgeNaturality`, with a complete Lean proof
of `CategoryTheory.Functor.cochainHypercohomologyLeftEdge_naturality`: transport through
extension, map-extension and quotient homology comparisons; use derived-unit, spectral
left-edge and target-comparison naturality; transport back. This theorem needs no
Grothendieck assumption on C. Added `Sheaf.CategoryTheory.HypercohomologyLeftEdgeSingle`,
containing only the remaining single-degree normalization statement. Both imports in
the original module are proof-only. Updated the original node's proof and dependencies.

## Proved and sorry left

Original hole closed:
`CategoryTheory.Functor.cochainHypercohomologyLeftEdge_canonical`
(`lem-pc-hypercohomology-edge-cocycle-canonical`). Its combining proof is complete.

New theorem proved:
`CategoryTheory.Functor.cochainHypercohomologyLeftEdge_naturality`
(`lem-pc-hypercohomology-left-edge-naturality`).

One new hole remains, as the entire proof of a public named theorem:
`CategoryTheory.Functor.cochainHypercohomologyLeftEdge_single`
(`lem-pc-hypercohomology-left-edge-single`). It handles only a single-degree complex,
with no arbitrary differential, cycle object or homology quotient to transport.
This is a decomposition, with one original hole closed and one smaller hole added;
net hole reduction is zero. No sorry remains in the original module or the naturality
module. All three modules compile locally without warnings.

Edge cases checked: n=0 uses the same single-complex map with no incoming differential;
A=0 makes the normalization equation an equality of zero maps; identity cochain maps
make naturality an identity; a zero cycle object makes the original equation zero.
Neither new statement assumes acyclicity of the terms or of A. The normalization is
consistent with the shifted degree-zero derived-unit comparison for an arbitrary A.

## No longer needed

Removed the proof-only imports `Sheaf.CategoryTheory.CartanEilenbergExists` and
`Sheaf.Paper.CartanEilenbergLeftExactCohomology` from the original module. Its proof
no longer needs nodes `lem-sp-cartan-eilenberg-exists` or
`lem-sp-cart-eilenberg-left-exact-cohomology`. The new modules do not import them either.
This is pruning this proof route, without claiming that other targets no longer reach
these modules. The original public import `HypercohomologyLeftEdge` remains required.
The unused candidate `Mathlib.Algebra.Homology.SingleHomology` import was removed from
the naturality module; the normalization module needs it for its signature.

The item does not realize a unit statement or step: `dag/units/sk-thm-picard-rr.json`
has empty realized lists. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original dependencies give resolution existence and a comparison on complexes with
injective cycles/boundaries; neither states the compatibility of that model with the
explicit truncation edge. The original plan is not refuted, but for the canonical lift
its resolution calculation can be replaced below the unit level by naturality and
single-degree normalization. Naturality is fully proved here. The normalization remains
the specific remaining comparison task, with its proof in words in its module and node.
The existing declaration docstring records the old resolution plan; the updated node
and this report record the actual proof route.

The local `literature/stacks-project/derived.tex` is absent. Consulted the official
[Stacks Tag 015J](https://stacks.math.columbia.edu/tag/015J); the new proof descriptions
are explicitly agent-written expansions of the canonical truncation and derived-unit
comparisons, not verbatim statements from that source.

## New nodes

`lem-pc-hypercohomology-left-edge-naturality`, in
`dag/nodes/sec-picard-framework/lem-pc-hypercohomology-left-edge-naturality.json`, records
the proved functoriality theorem in `Sheaf.CategoryTheory.HypercohomologyLeftEdgeNaturality`.

`lem-pc-hypercohomology-left-edge-single`, in
`dag/nodes/sec-picard-framework/lem-pc-hypercohomology-left-edge-single.json`, records the
single-degree normalization in `Sheaf.CategoryTheory.HypercohomologyLeftEdgeSingle`.
It is strictly the normalization part of the argument; the original arbitrary-complex
case additionally requires the proved naturality and cycle/quotient transport.

No change record or forced adaptation is needed: existing statements and definitions,
public imports and visibility are unchanged.

## Second reading by H3

1. Compared the existing module and original node against the repository with `diff`.
   Verdict: the existing theorem signature is byte for byte unchanged, including both
   Grothendieck hypotheses, derived-category assumptions, degree range, and the let-bound
   canonical lift. No definition or public import changed. Only the proof and proof-only
   imports changed. There are no forced adaptations or statement change records.
2. Independently compiled all three modules through `lcompile.py --all`: clean.
   Examined every proof and scanned for forbidden declarations and attributes: none.
   Scratch-copy `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for
   naturality, and those plus `sorryAx` for canonical and single normalization. Exactly
   one local hole remains, the named normalization theorem; no data definition was added.
   In particular the proof constructs `f` with `mkHomFromSingle`, not existential choice.
3. Read both new statements, their docstrings and nodes. Verdict: naturality has a complete
   proof; normalization is a strictly smaller single-degree case, not a renamed arbitrary
   complex equation. At n=0 all displayed lifts still typecheck; zero A gives zero maps;
   identity f makes the naturality square tautological. The single complex has no incoming
   or outgoing differential, and H^n(RG(A placed in n)) is R^0G(A), so higher derived
   functors of A need not vanish. Repeated LeanFinder search for derived-unit degree-zero
   single-object compatibility, Loogle search for rightDerivedZeroIsoSelf, and `rg` of
   leftEdge/single comparisons in Sheaf and upstream. Found the proved
   `rightDerivedPlusSingleUnitHomology_comp_comparison`, which supplies the degree-zero
   unit calculation described in the normalization proof, but not its truncation, shift,
   and natural-index extension transport. No existing full normalization or cochain-edge
   naturality theorem was found. Closing normalization requires these further coherence
   calculations, rather than one immediate application of that comparison.
4. Read the reduction from its top: the map from the single complex on K.cycles n induces
   c on cycles (by monicity) and K.homologyπ n on homology. Naturality plus normalization
   then gives exactly the original quotient equation. Both new imports are needed and
   proof-only; SingleHomology is public only in the normalization module, where its
   isomorphism occurs in the statement. All two removed old proof dependencies are named
   under No longer needed. The unit sk-thm-picard-rr has empty realized statement and step
   lists; this below-unit route bypasses no realized unit step. Verdict: pass.
5. Read the three node records against the Lean. Original proof/proof_deps/proof_origin
   accurately describe the new route; the original node's other fields are unchanged.
   New nodes have the required creation, source, blueprint ancestry, searches and Lean
   fields, and proof_deps equals the union of uses. Verdict: pass after correcting both
   new lean.statement fields to preserve the source signature's exact whitespace.

Second reading changed only the verbatim signature formatting in the two new node
records and this report. The Lean proofs were retained. This delivery is a decomposition:
original holes closed 1, new holes added 1, net 0, plus a proved naturality theorem and
pruning of the two former proof-dependency imports. The original declaration docstring
still describes its historical resolution plan; the actual route is in its updated node.
