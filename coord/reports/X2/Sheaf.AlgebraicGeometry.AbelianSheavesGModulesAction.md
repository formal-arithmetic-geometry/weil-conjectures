## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_action`
with a compiling reduction to three strictly separate parts of the existing plan:
construct the canonical action functor, prove it full and faithful, and prove it
essentially surjective. The proof obtains the functor and its germ formula, applies
the other two statements to that same functor, constructs the Mathlib equivalence,
and retains the same stalk comparison and action formula. No existing signature,
definition, or docstring changed. A declaration-scoped unused-variable linter setting
preserves the existing quantified proof-binder names `hτ` and `hx` without warnings.

Added three modules under `Sheaf.AlgebraicGeometry`: `GaloisStalkActionFunctor`,
`GaloisStalkActionFullyFaithful`, and `GaloisStalkActionEssSurj`. Each contains exactly
one public theorem with a whole-proof sorry and a complete sourced proof in words.
Updated the original node's proof, proof dependencies and proof origin to match the
Lean reduction. The target's three new proof imports are ordinary non-public imports.

Read Stacks `etale-cohomology.tex`, the Galois-action section and the proof of the
field stalk equivalence, obtained in the sandbox scratchpad because the local
literature checkout contains only lists. Searches through the supplied search tool
found generic categorical and point APIs but no directly applicable theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable.

## Proved and sorry left

The item's sole original sorry is eliminated:
`AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules_action`, node
`lem-exc-abelian-sheaves-gmodules-action`. This is a reduction, not a sorry-free
transitive proof: its three new dependencies remain open.

Every sorry left in this delivery:

- `AlgebraicGeometry.Scheme.exists_galoisStalkActionFunctor`, node
  `lem-exc-galois-stalk-action-functor`, in `GaloisStalkActionFunctor.lean`.
- `AlgebraicGeometry.Scheme.galoisStalkActionFunctor_full_faithful`, node
  `lem-exc-galois-stalk-action-fully-faithful`, in `GaloisStalkActionFullyFaithful.lean`.
- `AlgebraicGeometry.Scheme.galoisStalkActionFunctor_essSurj`, node
  `lem-exc-galois-stalk-action-essentially-surjective`, in `GaloisStalkActionEssSurj.lean`.

The construction theorem asserts no equivalence property. The full-faithfulness
theorem asserts only bijectivity on hom-sets for a supplied canonical action functor.
The essential-surjectivity theorem asserts only realization of objects for that
supplied functor. None is the original theorem with a renamed or repackaged conclusion.

All four modules compiled locally in import order, and the original module compiled
without warnings after preserving its existing proof-binder names. Checked the
mathematical edge cases: empty sheaf coproducts and empty etale schemes; trivial
Galois groups; imperfect base fields; transcendental Omega; and orbit index sets
larger than the scheme universe. The fully faithful and essentially surjective
statements require the action formula, not merely an arbitrary action on stalk sets.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`.
- `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`.
- `Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.

These dependencies remain needed in the corresponding intermediate modules; they
have moved down the proof, so this delivery claims no global pruning. Similarly,
`lem-exc-etale-field-gsets` and `lem-galois-stalk-representable` remain necessary for
the essential-surjectivity argument, and the geometric-stalk definition remains
necessary throughout. The item's original six proof dependencies are no longer
direct dependencies of its proof; the new nodes retain the applicable ones below
it. Explicitly these are `def-weil-pbc-geometric-stalks`,
`lem-exc-etale-field-gsets`, `lem-exc-field-sections-stalk-invariants`,
`lem-galois-stalk-representable`,
`lem-weil-pbc-etale-fibre-discrete-separable-points`, and
`lem-weil-pbc-small-etale-representable-presheaf-sheaf`. Both existing public imports remain necessary for its statement and instances.
No node or module is claimed to have left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically usable and its route was retained. Its geometric
ingredients do not themselves state the action functor, the reconstruction of
sheaf morphisms, or realization of G-sets in the larger coefficient universe.
Those three pieces are now separately stated, with the omitted arguments written
out. The unit is still `sk-prop-h2`; no unit statement or realized proof step was
bypassed or modified.

An older theorem, `AlgebraicGeometry.etaleSheavesGsetsPoint`, was found during the
short-route search. Its hypotheses require an algebraic closure and its coefficient
universe is `max u (v + 1)`, whereas this item uses arbitrary algebraically closed
Omega and `max (u + 1) v`. It is therefore not a direct application. No change to
that theorem is included. The source's representable-by-one-scheme proof also
requires care about universes; the existing parent plan's coproduct of finite-orbit
representable sheaves supplies the stated larger-universe conclusion.

## New nodes

`lem-exc-galois-stalk-action-functor` states construction of a functor lifting the
stalk to discrete continuous Galois actions and the precise germ formula. Its
proof follows Stacks 03QW, including extension independence, open stabilizers,
functoriality, and the left-action order. Its module is
`lean/Sheaf/AlgebraicGeometry/GaloisStalkActionFunctor.lean`.

`lem-exc-galois-stalk-action-fully-faithful` states fullness and faithfulness for
any such functor and comparison satisfying the germ formula. Its proof transfers
the existing invariant-section theorem from the algebraic subfield of Omega,
then reconstructs all section maps componentwise. Its module is
`lean/Sheaf/AlgebraicGeometry/GaloisStalkActionFullyFaithful.lean`.

`lem-exc-galois-stalk-action-essentially-surjective` states realization of every
discrete continuous G-set for any such canonical functor. Its proof realizes finite
orbits by representable sheaves and takes their coproduct in the coefficient
universe, using the stalk/skyscraper adjunction. Its module is
`lean/Sheaf/AlgebraicGeometry/GaloisStalkActionEssSurj.lean`.

There are no change records because no existing statement, definition, or publicly
visible import was changed.


## Second reading by X2

1. **Visible interface: pass.** Compared the delivered original module with the
repository by `diff -u` and compared the complete theorem signature as literal
text: byte-for-byte equal. The original docstring is unchanged. Its only other
changes are ordinary proof imports and a declaration-scoped linter setting.
There are no changed definitions, target statements, or change records.

2. **Lean proof and axioms: pass as a reduction.** Independently compiled all four
modules through `lcompile.py --all`, in import order, with no errors or warnings.
Scanned all delivered Lean files for forbidden declarations and mechanisms: none.
Exactly three whole-proof `by sorry` occurrences remain, in the three reported
public named theorems; there are no definitions in these files. A temporary copy
of the original module with `#print axioms` for all four declarations compiled;
each printed only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The original theorem is therefore reduced, not transitively axiom-free. The
scratch axiom-check copy was removed before delivery.

3. **Split statements: pass.** Read every new signature and its source/docstring
proof, alongside Stacks' action formula, equivalence proof, and direct invariant
sections proof in the supplied source text. Construction asserts a lift and its
formula only; the two universal statements assert respectively full faithfulness
and essential surjectivity for that lift. No single split restates the original
equivalence. The germ formula determines the action because every Galois element
extends to Omega and every germ has a representative; it is not vacuous for
transcendental Omega. Extension independence uses finite separable residue fields.
Checked the empty sheaf/orbit coproduct, empty etale object, separably closed K,
imperfect K, and transcendental Omega cases. The finite-orbit and Type-w sheaf
coproduct argument covers orbit index sets too large for the site's scheme
universe. Each remaining sorry has a source, a complete proof in words, and a node.
Independent searches used leanfinder (etale sheaves versus absolute Galois actions),
loogle (`CategoryTheory.Functor.IsEquivalence`), grep, and `rg` in Sheaf and upstream
site modules. No direct replacement for a split was found. The older
`etaleSheavesGsetsPoint` requires an algebraic closure and has a different universe
expression and representable comparison; it does not directly apply. None of
these geometric splits can be closed by a short categorical API application.

4. **Route and pruning: pass.** The original Lean proof combines the three actual
parts via Mathlib's `Functor.asEquivalence`, retaining the same functor, comparison,
and germ formula. Read the old six dependencies and their relevant declarations
or Mathlib matches: all remain below the reduction, with the appropriate private
proof imports or the existing public statement imports. No global pruning is
claimed. Expanded the report to list every old direct node dependency explicitly.
Read `dag/units/sk-prop-h2.json`: its realized statement and step lists are empty;
this item is a lower-level ingredient and the delivery changes no unit record,
unit statement, or realized step, and bypasses no populated realized node.

5. **DAG agreement: pass after metadata clarification.** The original node changes
only `proof`, `proof_deps`, and `proof_origin`. These name exactly the three
statements used by the Lean reduction. Each new node has its matching Lean
signature, source, dependency union, searches, creation metadata, blueprint origin,
chapter, unit, and split status. The essential-surjectivity node's open-subgroup
quotient fact is an existing Mathlib match available through KrullTopology;
the representable stalk comparison is likewise an existing Mathlib match.
Clarified the new construction node's prose statement to give T's domain/codomain
and explicitly assert that j satisfies the displayed germ formula; its Lean
signature was already correct and remains unchanged.

Second-reading changes: clarified the new construction node's prose statement,
expanded the direct-dependency list in this report, and recorded this independent
review. No Lean proof or signature needed repair.
