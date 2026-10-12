## What changed

Proved `AlgebraicGeometry.finite_exactHom_single_counit_transport` from the existing
proved affine single-pushforward comparison and two strictly smaller generic
comparison identities. The public signature, universes, hypotheses, conclusion,
visibility, and public imports are unchanged.

The private assembly constructs the algebra-module isomorphism using the fully faithful
single functor. Exact scalar restriction reflects derived isomorphisms through its
cohomology comparison. Naturality of the exact single comparison and the derived
counit identity give the required equation. A proved private transport helper handles
the equality of the two underived pushforward functors by equality elimination.

Added proof imports of `SingleRightDerivedExactComposition`,
`ExactDerivedAdjunctionSingleCounit`, and Mathlib's derived-category full-faithfulness
module. Both new statement modules have one public theorem, with a source and a proof
in words. No definitions or other existing modules were changed.

The theorem now disables lazy weak-head reduction locally, preserving the original
heartbeat budget. Together with generic equality transport this repairs the previous
wall-clock timeout; the required three-file compilation passed cleanly (main file:
40.4 seconds before enclosing the generic context in its local section). No compiler scripts or time limits were changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finite_exactHom_single_counit_transport`, node
`lem-sc-finite-exact-hom-single-counit-transport`. Its module has no remaining `sorry`.
All three private helper theorems are proved without local holes.

Added two holes, constituting a decomposition rather than a dependency-free proof:

- `CategoryTheory.Functor.single_rightDerived_exact_composition`, node
  `lem-sc-single-right-derived-exact-composition`.
- `CategoryTheory.Adjunction.exact_derivedAdjunction_single_counit`, node
  `lem-sc-exact-derived-adjunction-single-counit`.

The first identifies canonical comparison maps under exact postcomposition; the second
computes the exact derived adjunction counit on one single complex. Neither asks for
schemes, quasi-coherence, an arbitrary derived isomorphism, or an existential module
isomorphism. Both identities hold for zero modules and zero functors: the proof plans
use canonical invertible comparisons and the unique maps outside degree zero, with no
cancellation of a noninvertible map. The original affine comparison declaration in the
current library is already proved.

## No longer needed

Removed the redundant direct proof import `Sheaf.AlgebraicGeometry.DerivedCategory`;
its definitions are still supplied by unchanged public statement imports. This does
not prune its module from the targets' import closure. Every original proof dependency
remains needed directly or through the two new comparison lemmas. In particular,
`lem-sc-derived-adjunction-from-underived` leaves the item’s direct `proof_deps` but
is retained as a dependency of `lem-sc-exact-derived-adjunction-single-counit`; its
module is still a public statement import. No entire node or module is claimed to
be pruned from the closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG route did not state the two explicit canonical comparison identities
needed to combine its steps. The new statements expose precisely those parts of the
argument and preserve the unit route. The unit's `realized` statement and step lists
are empty; no realized unit statement or step was bypassed.

The earlier attempt's generic assembly was sound, but its scheme specialization had
not passed compilation. Rewriting the composite pushforward inside its derived functor
creates an invalid dependent rewrite motive, because the additive instance depends
on the functor. Direct conversion and simplification of the same expressions also
exceeded the time limit. Equality elimination in the private generic transport helper
handles the dependent additive instance before specialization. Local eager weak-head
reduction resolves the signature's costly ring-sheaf unification.

The prior attempt recorded LeanFinder, Loogle, source grep, and the unavailable
LeanSearch service in the new nodes. This repair also ran Loogle for the exact single
comparison and LeanFinder for the derived single counit, and inspected the current
Mathlib and WeilConjectures implementations. They provide the generic infrastructure,
not either combined comparison identity. The cited Stacks tags motivate the affine
specialization; the general categorical proof plans are explicitly agent-written.

## New nodes

`lem-sc-single-right-derived-exact-composition` records the canonical exact-postcomposition
single identity, in `Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition`.

`lem-sc-exact-derived-adjunction-single-counit` records the exact-derived-adjunction
single counit identity, in `Sheaf.AlgebraicGeometry.ExactDerivedAdjunctionSingleCounit`.

`coord/changes/finite-exact-hom-private-proof-context.md` records the scoped generic
proof context. The conservative interface check requests this record for new universe,
variable and open commands, although the existing signature and public imports are
unchanged. No forced adaptations are needed.

## Second reading by K2

1. **Interfaces: pass.** Read the full source diff against the repository. Extracted
   the existing theorem signature up to `:= by` and checked byte-for-byte equality.
   Universes and original public imports are unchanged; the generic variables and
   opens are scoped in `ProofAssembly`. All added helpers are private proved theorems.
   No definition, target, or other existing Lean module is modified. The conservative
   context change is declared in the supplied change record.
2. **Proof and kernel checks: pass.** Compiled all three delivered modules in import
   order with `lcompile.py`, without errors or warnings (main module 41.2 seconds).
   Inspected the full assembly: scalar restriction reflects isomorphisms through the
   forgetful functor; exact homology comparison lifts this reflection to the derived
   category; the affine comparison and invertible canonical comparisons make `cg`
   invertible. `preimageIso` constructs `j` from full faithfulness, and naturality,
   the two split identities, and inverse cancellations prove the required equation.
   Equality elimination handles the dependent additive instance correctly. There
   are exactly two delivered sorries, both the named reported split theorems, and
   none in a definition or private helper. No prohibited declarations or options
   occur. Scratch `#print axioms` checks are recorded below.
3. **Split statements: pass as a decomposition.** Both equalities follow from the
   defining factorization of the canonical comparison maps, not from affine
   geometry or the existential isomorphism to be constructed. Checked their map
   directions against `rightDerivedFunctorCompMapDerivedCategoryIso`,
   `singleFunctorCompRightDerivedFunctorIso`, `mapDerivedCategorySingleFunctor`, and
   the localized adjunction counit factorization. The zero object, zero functors
   where an adjunction exists, and identity functors give the same equalities; no
   invertibility of an arbitrary unit or nonzero hypothesis is assumed. Sources,
   complete word proofs, and matching nodes are present. Independently searched
   Loogle for `derived_counit`, LeanFinder for localization/exact-postcomposition
   unit compatibility, and source grep for composite single comparisons. These
   give the factorization infrastructure, not either stated combined identity.
   A short attempt to finish the composition identity encountered dependent
   homotopy-category elaboration; no partial proof or extra hole was retained.
4. **Route and pruning: pass.** The main proof opens the original hole and combines
   the already proved affine comparison with full faithfulness and two smaller
   identities. Neither split theorem restates the item. New proof-only imports use
   plain `import`; new public imports are used by their theorem signatures. The
   removed direct import is redundant. All old proof dependencies remain used
   directly or indirectly; explicitly recorded the derived-adjunction node’s move
   to an indirect dependency. The unit `sk-thm-picard-duality` has empty realized
   statement and step lists, unchanged. No module leaves the target closure.
5. **DAG: pass.** Compared all node fields with the originals. The existing node
   changes only `proof`, `proof_deps`, and `proof_origin`; the two new nodes have
   matching verbatim Lean signatures, creation/source/search/blueprint metadata,
   and the same chapter and unit. Each `proof_deps` equals the union of its steps’
   `uses`. The written plans match the two canonical-map identities and assembly.

Second reading changes: clarified the indirect old dependency in `No longer needed`
and added this independent review and axiom evidence. The compiling Lean proofs and
statements were retained unchanged. One original hole is closed and two strictly
smaller holes are added: this is a decomposition, with net holes closed minus added
of -1 in the affected closure, not a dependency-free proof.

Axiom evidence: `finite_exactHom_single_counit_transport`, private `assembly` and
`assembly_transport`, and both split theorems report only `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx`. The private
`derivedNatIso_refl` reports only the three permitted axioms. All scratch copies
compiled successfully and were removed from the delivery source tree.
