## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonSquareProEtalePath_normalization`
in `Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization`.
The existing public import, theorem signature and docstring are unchanged.
Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, using its
proved exact-derivation composition, whiskering, identity and associativity laws.

Four fully proved private calculations implement the existing route: `exact_path`
normalizes the three ordinary path factors; `derive_transport` treats equality
transport; `square_exact` normalizes the total left derived square; and
`normalized_path` combines these calculations with naturality and cancellation.
The final theorem converts the explicit endpoint presentations and uses only
path-definition expansion and associativity to finish. Updated the item's node
proof and proof origin to match this proof.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.comparisonSquareProEtalePath_normalization`
(node `stage3-proetale-comparison-square-proetale-path-normalization`).
Actual item hole count: 1 before, 0 after. Added holes: none. Split-offs: none.
All four private helpers are proved; no `sorry` remains in the item module.
The complete module compiles through `lcompile.py`, without warnings, within the
single-file limit. The required delivery dry run checks all added declarations'
axioms as well as compilation. The first dry run passed both compilation and
its axiom probe; its remaining findings were the scope-command change record
and the second reader's pending section.

## No longer needed

None. No original import, node or module is pruned. Both imports are used.
The proof follows the existing one-path normalization plan and uses no theorem
asserting equality of the etale and pro-etale square paths.

## Where the brief, the DAG or earlier work was wrong

The earlier saved proof's generic calculations were correct, but its final
rewrite did not compile across the definitionally equal endpoint presentations.
Kept the fully proved combined calculation as a private helper and used explicit
conversion followed by path-definition expansion and associativity.

The published `ComparisonSquarePaths.olean` remains unavailable to the wrapper.
An exact, unchanged sandbox copy of the existing repository module was compiled
with `lcompile.py --all` before the item. It is included only to supply that
unchanged dependency during validation; it produces no repository change and adds
no declarations or holes beyond those already present in the library. No build
script, dependency interface, target, or other group's proof was changed.

The preflight conservatively flagged the helper section variables and local
reducibility attribute as interface commands. Their effects are local, and the
public interface is unchanged. The change record is
`coord/changes/E4-proetale-path-normalization-private-proof-scopes.md`; it lists
all 57 downstream modules. No consumer adaptation is needed.

## Second reading by E4

1. **Public interface — pass.** Read both delivered Lean files and diffed them
   against the shared repository. The dependency copy `ComparisonSquarePaths.lean`
   is byte-for-byte identical. The item's existing theorem signature and docstring
   are byte-for-byte identical; its existing public import is unchanged. All four
   added helpers are private. The added `MapDerivedCategoryMate` import is plain
   `import` and supplies proof lemmas. Section variables and the local reducibility
   attribute do not change downstream declarations or global attributes. The
   conservative preflight finding is documented by the existing change record.
   No definition, target, or other group's module is altered.

2. **Proof and trust — pass.** Independently compiled the item with `lcompile.py`:
   exit 0, no warnings, 8.0 seconds. Read `exact_path`, `derive_transport`,
   `square_exact`, `normalized_path`, and the final conversion in full. Whiskering,
   exact composition associativity, equality induction, naturality, and inverse
   cancellation prove the stated path without assuming square coherence.
   An appended `#print axioms` in a scratch copy reports exactly `propext`,
   `Classical.choice`, and `Quot.sound` for the public theorem. No `sorry` or
   forbidden trust escape occurs in the item. No new data definition or witness
   selection is introduced; `cs` is explicitly assembled from the supplied
   pullback. The unchanged dependency contains only explicit path constructions.

3. **Split statements — pass, none.** No hole is added and no statement is split
   off. The four private lemmas are fully proved calculations used by the final
   theorem. Their statements retain the actual path factors, and equality
   transport is justified by induction, including the reflexive case. Identity
   edges and zero inputs require no nondegeneracy hypothesis: all steps remain
   valid naturality, identity, and isomorphism equations.

4. **Route and pruning — pass.** Read the imported path definitions, upstream
   exact-derivation coherence lemmas, the blueprint transport argument, and
   `dag/units/sk-thm-properbasechange.json` including `realized`. The item carries
   out a subsidiary path normalization and bypasses none of the unit's statement
   or steps. Searched the local base-change and derived-category modules and
   made a fresh LeanFinder query about derivation of whiskered composites.
   Results supplied general derived-functor laws, with no shorter specialized
   normalization theorem. The proof already uses the upstream composition,
   whiskering, and associativity laws. Both imports are needed. The old
   `proof_deps` is empty, so `## No longer needed` correctly lists no pruning.

5. **DAG and report — pass.** Parsed and compared the node JSON: only `proof` and
   `proof_origin` differ. The three steps accurately describe the four private
   calculations and final conversion; no new mathematical dependency is hidden
   by the empty `proof_deps`. The existing statement and Lean declaration record
   are unchanged. No new nodes are required. The report records one original
   hole closed, zero added, and zero split-offs, by declaration name.

Second-reading changes: added this independent review and its compilation,
axiom, signature, duplicate-search, and route evidence. No proof repair was
needed and no Lean code or node was changed by the second reader.
