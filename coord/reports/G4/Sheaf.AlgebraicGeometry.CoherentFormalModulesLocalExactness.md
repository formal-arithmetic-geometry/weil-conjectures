## What changed

Reduced `AlgebraicGeometry.coherentFormalModules_local_exactness`, keeping its full
signature and public imports unchanged. The theorem now has a complete Lean proof
from two strictly narrower geometric statements and the existing
`coherentFormalModule_isIso_of_isIso_restrict` and `coherentFormalModule_abelian`.
No existing declaration or definition changes its signature or meaning.

Added `CoherentFormalModulesRestrictionObjects.lean`: the remaining object-closure
statement, followed by the real `coherentFormalModulesRestriction` construction.
The functor is ObjectProperty.lift of the inclusion followed by termwise module
restriction. Its underlying data are explicitly constructed; only the object
membership proof uses the new theorem. Additivity is proved by instance inference.
There is no selection of arbitrary functor data from an existence theorem.

Added `CoherentFormalModulesRestrictionLimits.lean`: preservation of finite limits
and finite colimits by that specific restriction functor. Its proof plan follows
restriction of the stabilized kernel construction and termwise cokernels.

The combination in the item is real Lean: construct Noetherian instances on opens,
supply the functor, derive preservation of short exact sequences, prove local
detection of zero objects from invertibility of the zero endomorphism, detect
exactness through left homology, and detect mono/epi by auxiliary complexes with
zero first/second arrow. A proved private helper transports homology across the
unique zero-morphism structure: the existing abelianity theorem returns an
existential abelian structure whose preadditive data need not be definitionally
the ambient ones. No private helper has a sorry.

All three delivered modules compile together with lcompile.py --all, with no
warnings. The item compiles in about five seconds after its new imports are built.
One intermediate compile timed out; subsequent complete compiles passed without
any limit adjustment or splitting for performance. The original and new node
proof records match this route. The unit sk-thm-p1 realization is unchanged; this
item and the two isolated steps are below the unit level.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.coherentFormalModules_local_exactness`
(node `lem-weil-pbc-coherent-formal-modules-local-exactness`). No sorry remains in
the item's module. This is a decomposition, not a completed sorry-free geometric
proof: one upper hole closed, two lower holes added, net -1 before any later work.

Every sorry added by the delivery (each in its own new module, exactly by sorry):

- `AlgebraicGeometry.coherentFormalModules_restriction_objects`, node
  `lem-weil-pbc-coherent-formal-modules-restriction-objects`.
- `AlgebraicGeometry.coherentFormalModules_restriction_limits`, node
  `lem-weil-pbc-coherent-formal-modules-restriction-limits`.

The first is only the object conditions under termwise restriction. The second is
only finite-limit/finite-colimit preservation; neither asserts locality or the
cover equivalences. The parent proof establishes those cover equivalences.
Existing imported sorries are unchanged. The current isomorphism-local theorem has
a complete proof; its geometric dependencies may still contain sorries.
The added definition uses no sorry data. Homology is used only through its
universal property and IsZero, invariant under its canonical isomorphisms.

Edge cases of the new statements were checked mathematically: U empty, U=X, the
zero system, I=0, and the unit ideal. Termwise restriction preserves all three
object conditions in these cases, including every positive-level quotient
condition. The zero target category for U empty preserves finite limits and
colimits; restriction to X is the identity up to the canonical identifications.
An empty covering can cover only the empty scheme; the proved zero-object
reflection step handles it through the existing arbitrary-cover isomorphism
locality theorem, without any nonempty-cover hypothesis.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: already public through abelianity.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel`: now a dependency of the
  restriction-limits step, not used directly in the parent combination.
- `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`: now a dependency of
  the restriction-objects step.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`: now a
  dependency of the restriction-objects step.

The old direct proof dependency
`lem-weil-pbc-module-restriction-open-immersion-colimits` is also no longer used
directly by the parent: both new nodes retain it. Its declarations are provided
by Mathlib module restriction and its adjunction, already available through the
formal-module imports.

The corresponding nodes remain needed indirectly; these are removals of direct
imports, not claims of whole-closure pruning. The new geometric modules keep their
planned proof imports for the next workers.

The parent no longer needs the planned epi-kernel-lift argument or node
`lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`; left homology and local zero-object
detection replace it. This is the only logical dependency pruned from the overall
argument. It is a Mathlib leaf, so no standalone project module is thereby
claimed to leave the targets' import closure. No unit realization is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned declarations do
not directly state closure of formal-system object conditions under restriction,
nor preservation of the stabilized kernel fork by that functor. The two new
statements isolate precisely those geometric steps, with the source and complete
proof plans in docstrings and nodes. The old isomorphism-locality statement is
levelwise, not already phrased for the formal restriction functor: evaluating the
explicit lift supplies exactly its hypotheses.

The local Stacks source file is absent in this clone. The cited source was read
at https://stacks.math.columbia.edu/tag/087X (Lemma 30.23.2), including the
stabilized-kernel description and final restriction/locality sentence. No new
unsourced geometric argument was introduced.

## New nodes

`lem-weil-pbc-coherent-formal-modules-restriction-objects` records the object
conditions and the explicit functor they permit. Its statement is in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesRestrictionObjects.lean`.
It inherits the parent's chapter and unit and cites step 1 and Stacks 087X (2).
LeanFinder, Loogle and grep found no formal-system closure theorem; Mathlib ObjectProperty.lift
supplies the functor construction once closure is known.

`lem-weil-pbc-coherent-formal-modules-restriction-limits` records finite-limit and
finite-colimit preservation by the actual restriction functor. Its statement is
in `lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesRestrictionLimits.lean`.
It inherits the parent's chapter and unit and isolates step 2, using the existing
stabilized-kernel and termwise-cokernel nodes. LeanFinder, Loogle and grep found generic
preservation criteria and ordinary module restriction, but no formal-module
preservation theorem. No change record or forced adaptation is necessary.

LeanSearch was additionally attempted for both new nodes, but the service returned
Internal Server Error. Both nodes record this unavailability without a verdict;
the other search methods were available and are recorded with their results.

## Second reading by G4

1. PASS. Diffed the existing module against the read-only repository. Its sole
existing theorem signature is byte-for-byte identical, including universes and
all quantifiers; its public imports are unchanged. No existing definition was
edited. The existing node changes only proof, proof_deps and proof_origin. The
other two modules and nodes are new, with no forced adaptations or change records.

2. PASS as a decomposition. Independently compiled all three modules in import
order with lcompile.py: no errors or warnings. There are exactly two named public
sorry theorems, the two listed above, and no prohibited declarations or sorry
inside data. A scratch copy printed axioms for the parent theorem, both new
statements, the explicit restriction definition and both private helpers: only
propext, Classical.choice, Quot.sound and permitted dependency sorryAx occur.
The homology transport helper itself has no sorryAx. The restriction definition
constructs its object system and maps with ObjectProperty.lift; the open theorem
supplies only membership evidence. Abelianity and homology are used via universal
properties; no arbitrary existence witness supplies the restriction data.

3. PASS. Read the three object conditions and the stabilized-kernel statement,
and independently read Stacks 087X (https://stacks.math.columbia.edu/tag/087X).
Object closure preserves precisely coherence, annihilation and the transition
quotient equation. Limit preservation is the geometric kernel/cokernel step,
without asserting local reflection. Both are strictly proper parts of the
original argument, have source/proof docstrings and matching nodes, and are true
for the empty and total open, the zero system, zero ideal and unit ideal. In
particular, for the unit ideal the annihilation condition forces every level to
be zero; for the zero ideal all transition maps are isomorphisms. An empty cover
can only cover an empty scheme and the zero-endomorphism argument handles it.
Independent searches used LeanFinder's query "adic coherent sheaf inverse system
pullback open immersion object property quotient transition", Loogle's query
"CategoryTheory.Functor.Additive, CategoryTheory.Limits.PreservesFiniteLimits",
and source rg with formal/adic and restrict/pullback alternatives. Results give
ordinary module restriction and generic exact-functor criteria, not either new
geometric assertion. No split-off statement can be closed in a few minutes by
these results: restriction of ideal products/quotients and stabilized kernels
still needs formal geometric work. The parent proves actual cover reflection
through homology and auxiliary zero-arrow complexes, rather than just renaming
its original hole.

4. PASS. Checked the shortest-route alternatives and proof-only import visibility.
The Mathlib exact-functor criteria found by Loogle require the same geometric
preservation information; they do not remove either remaining hole. The parent
uses Mathlib homology directly and the existing isomorphism-local theorem.
All five old proof dependencies removed from the parent's direct list are now
accounted for: kernel, coherence locality, ideal products and ordinary restriction
remain indirect, while epi-kernel-lift is pruned. No project module is claimed
pruned from the target closure. Read dag/units/sk-thm-p1.json and its realized
fields: no realization is replaced or bypassed by this reduction below the unit.

5. PASS. Checked each node's proof_deps against the union of its proof-step uses,
the new Lean statements verbatim, source records, creation/item/group fields,
chapter/unit inheritance and the actual parent proof. The only existing-node
edits are the three allowed proof fields. Each new node records LeanFinder,
Loogle and grep, plus the explicitly unavailable LeanSearch attempt. The report
correctly counts one upper hole closed, two lower holes added, net minus one;
this delivery does not claim a complete proof of the geometric result.

Second-reading changes: completed the No longer needed account with the ordinary
restriction dependency and corrected the description of the already-proved
isomorphism-locality theorem. No Lean proof, signature, definition or node needed
repair. The axiom-check scratch copy is outside the delivered lean directory.
