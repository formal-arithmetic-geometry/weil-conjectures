## What changed

Replaced the first worker's choice of an unspecified transport isomorphism by an
explicit invertible natural transformation built from the selected adjunction unit,
the pinned single tensor comparison, and the canonical underived composition
comparison. The transport is its inverse. Mathlib's exact-functor localization and
left-derived uniqueness, together with the upstream derived-equivalence instance,
prove invertibility. Added only the proof import
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`; the other ingredients
are already publicly available through the existing import. The existing theorem's
signature and the public import are unchanged. Updated the existing DAG node's proof,
proof dependencies and proof origin to match this construction.

## Proved and sorry left

Closed `AlgebraicGeometry.exists_isomorphic_single_tensor_counit_transport` (one of
one holes in the original item). No holes added; no local sorry remains. The two
proposed split-off statements `exists_isomorphic_single_tensor_transport_iso` and
`isomorphic_single_tensor_transport_inv_formula`, and their proposed modules/nodes,
were removed from the sandbox before delivery. This is one local hole closed, not a
decomposition. A scratch-copy `#print axioms` reports exactly `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx`, so the theorem is proved
including its actual proof dependency closure.

## No longer needed

None of the repository's imports or old proof dependencies is pruned: all three
old dependencies remain used. The discarded first-worker-only transport existence
and formula modules/nodes were never part of the repository baseline and are not
counted as pruned modules. No new modules or nodes are delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's existence statement gave only an isomorphism with property True.
It did not determine that isomorphism, so choosing its witness and asserting the
canonical inverse-component formula was unjustified. For identity maps over a
field of characteristic different from two, a nonzero single-complex functor has
both identity and negative-identity natural automorphisms: existence alone cannot
select the required one. The proposed short docstrings also omitted the source
and complete proofs, and the original item's DAG did not describe the proposed
reduction. The existing canonical-construction plan was correct and is now carried
out directly without either additional assertion.

The previous attempt was blocked by delivery-tool package-source discovery for the
required Mathlib PointwiseLeftDerived import. On this retry, the unchanged proof
passed deliver3.py compilation, axiom auditing and source validation. No tool or
library file was changed, and nothing was pushed.

## Second reading by F4

1. Compared the delivered module against the repository with diff and extracted
   its complete theorem signature: byte-for-byte identical. No hypotheses,
   conclusion, definition, universe, declaration visibility or public import changed.
   All new imports are proof-only. Verdict: pass.
2. Read the entire proof. Local compilation through lcompile.py succeeds without
   warnings; the delivered source has no sorry, axiom, unsafe, opaque,
   implemented_by or extern declaration, and no new definition. The canonical
   transformation is constructed from its actual maps, not from an arbitrary
   existence witness. The scratch-copy axiom audit lists only propext,
   Classical.choice and Quot.sound, with no sorryAx. Verdict: pass.
3. Rejected and removed both proposed split-off statements. Independently searched
   with msearch.py (leanfinder, loogle and grep), and searched lean/ with rg using
   exactness, localization, invertibility and equivalence queries. Found Mathlib's
   isIso_of_isLeftDerivedFunctor_of_inverts and the upstream
   isEquivalence_mapDerivedCategory instance, closing the argument with no new
   statements. Zero modules and empty schemes cause no exception: the proof uses
   equivalences, whiskering and localization uniformly. Verdict: pass after repair.
4. The proof now constructs the displayed inverse from the top downward using the
   shortest available exact-equivalence route, rather than delegating the target
   to new holes. Checked public import reachability and removed the redundant
   proposed proof import of the upstream exact-functor module. All old proof_deps
   are used. Read dag/units/sk-thm-picard-f-representable.json: its realized statement
   and step lists are empty and this item realizes no fixed unit step; the unit
   route and record are untouched. Verdict: pass.
5. Updated the existing node's proof to the exact-equivalence computation, the
   specified derived adjunction, the explicit single comparison, and inversion.
   proof_deps equals the union of step uses and retains the three old nodes.
   proof_origin records the source and second-reading repair. There are no new
   nodes or change records. Verdict: pass.

Second reading changed the complete proof, removed two unsupported new theorem
modules and nodes, minimized proof imports, and corrected the report and existing
node metadata. The existing target statement and public interface are unchanged.
