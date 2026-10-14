## What changed

The existing declaration
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`
keeps its original signature and all its original public imports. Its proof obtains a
positive annihilator of the unit from `(hΛ 1).exists_nsmul_eq_zero`, applies the
unbounded proper-base-change theorem over `ULift (ZMod n)`, transfers that isomorphism
to Λ componentwise, and assembles the natural isomorphism.

Two private proof imports replace `Sheaf.AlgebraicGeometry.DerivedCategories`:
`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN` and
`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful`. The first module realizes
existing node `lem-kun-0f0c`; the second realizes new node
`lem-kun-proper-base-change-forgetful`. There are no definitions or forced adaptations
in this delivery. No existing declaration's signature, visibility, or docstring changes.

## Proved and sorry left

Hole closed, by name:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`.
Its Lean proof has no local sorry but depends on the following two named holes added
by this delivery:

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_modN`, in
  `ProperUnboundedBaseChangeModN`, existing node `lem-kun-0f0c`.
- `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_modN`, in
  `ProperUnboundedBaseChangeForgetful`, new node `lem-kun-proper-base-change-forgetful`.

This is a decomposition, not a completed proper-base-change proof: one original hole
closed, two lower holes added (raw net -1; the ledger determines the import-closure net).
The first lower statement is the finite cyclic-coefficient case. The second is solely
coefficient transfer, conditional on invertibility of that cyclic exchange, without
properness. Both are strictly parts of the original argument, and neither merely
renames the original theorem. Each remaining hole is a public named theorem with an
exact `:= by sorry` proof, source, full proof in words, and matching node.

All three files compile in import order with lcompile.py and no compiler warnings.
Scratch-copy `#print axioms` checks for all three declarations return exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; no other axiom occurs.
No axiom, unsafe, opaque, implemented_by, extern, hollow definition, or data selected
from an unproved mere existence theorem is introduced.

## No longer needed

Removed from the existing target module: private import
`Sheaf.AlgebraicGeometry.DerivedCategories`. Its declaration is not used by the
proof. This is import pruning; this report does not claim the module is globally
unreachable, since other library modules use it.

The old direct proof dependencies were `def-weil-pbc-derived-categories`,
`lem-kun-0f0c`, and `lem-kun-unbounded-abelian-exchange-comparison`.
`lem-kun-0f0c` is retained directly. The other two are no longer direct dependencies
of the target: their use is inside the coefficient-transfer node, and both remain
transitive dependencies. No mathematical branch of the route is discarded.

The rejected sandbox-only `ProperUnboundedBaseChangeAbelian` module and
`lem-kun-proper-base-change-integer-unbounded` node are not delivered. Their universal
integer-coefficient assertion was not justified by the cited torsion theorem. The
forgetful module no longer imports that module, Proper, Torsion, Derived.Coefficients,
or ModuleCat.AB. The cyclic module does not import Torsion, Derived.Coefficients, or
ModuleCat.AB. Its remaining imports supply symbols and instances in its signature.
No existing public import is removed or privatized.

## Where the brief, the DAG or earlier work was wrong

The first worker's split treated unbounded proper base change on **all** integer-module
complexes as an available theorem, but its source, Stacks 0F0C, is explicitly for
Z/nZ coefficients with n positive. Its proposed proof applied a torsion
cohomological-dimension bound to arbitrary integer-module sheaves, and applied
bounded-below proper base change without a torsion hypothesis. Neither inference is
justified. The original target's proof in words and original DAG already had the
correct cyclic-coefficient reduction. The second reader restored that route instead
of delivering the unsupported integer assertion.

The first report also failed to name the removed DerivedCategories import, and called
the target proved without accounting for two new holes. This report corrects both.
The new finite cyclic theorem reuses the existing `lem-kun-0f0c` node, rather than
creating a duplicate of an already stated mathematical node. The original unit route
is retained, with coefficient comparison explicit below that unit.

The local literature checkout does not contain the cited Stacks .tex sources. The
second reader verified the authoritative pages directly: 0F0C (Lemma 59.92.3),
095U (torsion cohomological-dimension bound), 07K7 (unbounded acyclic-complex
computation), 079P (termwise injective K-injective representatives), and 0D6J(3)
(canonical comparison with abelian derived direct image). The full canonical mate
coherence is the additional assertion of the existing comparison node, not an
assertion attributed to 0D6J alone.

## New nodes

`lem-kun-proper-base-change-forgetful`: choose the explicit coefficient map
Z/nZ → Λ from n·1=0 and restrict a representing complex. The two canonical
coefficient-forgetting exchange equations identify the same underlying abelian
exchange; invertibility transfers through the endpoint comparisons and reflects
back through conservative forgetting. Searches were rerun with msearch.py using
coefficient restriction and cyclic-coefficient terminology: LeanFinder returned only
algebraic etale restriction results; Loogle returned no coefficient IsIso theorem;
source grep returned no unbounded etale coefficient comparison. LeanSearch was
unavailable and is recorded as such. Existing module/abelian exchange comparison
modules concern bounded-below derived categories and cannot be silently used here.

Existing node `lem-kun-0f0c` receives only a `lean` attachment to the cyclic-coefficient
module; its mathematical statement and proof plan are unchanged. No change record is
needed: no previously published statement or definition changes.

## Second reading by P2

1. Compared the delivered target with the repository version by diff. The existing
   declaration's signature is byte-for-byte identical; all four public imports,
   visibility, universes, variables, and existing docstring are identical. Only two
   private proof imports replace one private import and the proof body changes. The
   lower declarations are new. No other existing Lean module is edited. Verdict: pass.

2. Compiled all three final modules with lcompile.py in import order. There are exactly
   the two named theorem holes listed above, each with a docstring proof and node;
   the original declaration has a complete composition proof. Scratch `#print axioms`
   checks yield only the allowed three axioms and sorryAx. No definitions are added,
   and the positive annihilator is eliminated within a proof, not used to define
   arbitrary data. Verdict: pass as a decomposition, not a completed proof.

3. Rejected the proposed universal integer-coefficient split. Replaced it by the actual
   positive-n Z/nZ statement of Stacks 0F0C and reused its existing node. The transfer
   statement supplies no geometric base-change theorem itself: it assumes cyclic
   exchange invertibility. Checked n=1 (zero coefficient category), n=0 in the
   transfer statement (ZMod 0=ℤ), the zero ring, arbitrarily large torsion rings,
   identity squares, and unbounded complexes. The cyclic theorem excludes n=0;
   the target obtains n>0 even for the zero ring. Restriction preserves the underlying
   complex and hence compares the same canonical mate, not only isomorphic endpoints.
   Reran Mathlib searches and read library comparison signatures; the available ones
   are bounded below. Verdict: repaired, then pass.

4. Read the target from the top down, the old proof dependencies and their statements,
   and `dag/units/sk-prop-sf-kunneth-ordinary.json`. The cyclic proper-base-change step
   and the coefficient-forgetting step of the old route are both retained. The unit's
   realized fields and route are not changed. Removed the unused DerivedCategories
   import and unnecessary imports in the new modules; proof-only imports remain
   private. The No longer needed section enumerates every old direct dependency
   absent from the new direct list and explains its retained transitive use.
   Verdict: pass; no whole module claimed globally pruned.

5. Checked the nodes against the final Lean signatures. Target proof_deps names precisely
   the cyclic theorem and transfer theorem used in its body. Its steps record the
   positive-annihilator choice and componentwise assembly. The finite theorem attaches
   to existing node lem-kun-0f0c without changing its statement or plan. The new transfer
   node has self-contained statement, exact Lean signature, complete proof steps with
   proof_deps their union, sources, origin, recorded searches, creation metadata,
   blueprint link, matching chapter/unit, and Lean record. Verdict: pass.

Second-reading changes: replaced the unsupported integer theorem by the positive-n
cyclic case; revised the coefficient-transfer signature and proof in words; changed
the target proof to explicitly choose a positive annihilator; reused the existing
finite-case node; synchronized all DAG fields and the hole accounting; pruned
unnecessary imports. No remaining lower statement can be closed from the currently
available bounded-below comparison interfaces in a short proof.
