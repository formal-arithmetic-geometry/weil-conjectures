## What changed

Proved `AlgebraicGeometry.Scheme.Modules.nonvanishing_section_trivializes` in
`Sheaf.Paper.NonvanishingSectionTrivializes`, without changing its signature or definitions.
Added two proved private helpers: `stalk_generator_bijective` and
`nonvanishing_eq_compl_support`. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`,
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`, and
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.
All existing public imports are retained: they provide the statement's module category,
invertibility class, section morphism, and nonvanishing definition.

The key reduction identifies the stalk-defined locus with the existing open complement of
`Hom.zeroLocus (homOfGlobalSection L s)`. The source library's proved
`isFreeGenerator_app_one_of_le` then supplies sectionwise bijectivity. Reflection of
isomorphisms from the underlying presheaf proves the overFunctor assertion; bijectivity
also gives the required unique quotient. Updated the item's proof, dependencies and origin.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.nonvanishing_section_trivializes`.
No sorry remains in the item, and none is added elsewhere. Both private helpers are proved.
This is a proof, not a decomposition. Single-file launcher compilation passes without warnings.

## No longer needed

No existing imports were removed; each occurs in the unchanged public statement's interface.
The proof no longer needs `lem-weil-pbc-nakayama-local-generators` or
`lem-weil-pbc-module-iso-on-stalks` (Mathlib leaves with no dedicated project module).
`def-weil-residue-field` is also unnecessary: the argument uses maximal-ideal membership
and units directly, without forming the residue field. These dependencies are removed from
the item's proof_deps. No claim is made that other targets cease to need them.
The replacement reuses the source library's free-generator argument below the unit level;
none of the fixed statement/step nodes in `sk-thm-reduction.realized` is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier candidate note correctly warned that a comparison between the stalk-defined
nonvanishing set and the zero-scheme complement was missing; this delivery proves it.
The two invertibility classes are connected by the already proved
`IsInvertible.sheafOfModules_isInvertible` theorem, so the candidate is usable.
The original seven-step proof is longer than necessary: local scalar coefficients and the
existing free-generator theorem remove the need for Nakayama and a stalkwise iso criterion.
The referenced Stacks source is absent at literature/stacks-project/modules.tex on this
machine; the actual source was read at /home/ubuntu/c1-stacks-review/modules.tex,
lemma-s-open. Its local-coefficient argument also appears in the source library docstrings.
Empty schemes and the zero section require no exclusions: U may be empty and bijectivity
on its subopens follows from the same source theorem. No statements were disputed or changed.

## Second reading by E2

1. Compared the delivered module and node with the repository using `diff -u`.
   The original theorem signature and docstring are byte for byte unchanged; no
   definitions, public imports, or existing declarations were altered. No change
   record is needed. Verdict: pass.
2. Independently compiled the module through `lcompile.py` with no errors or warnings.
   Scanned the delivered Lean for sorry and forbidden declarations: none occur.
   Compiled a scratch copy with `#print axioms` for both private helpers and
   `AlgebraicGeometry.Scheme.Modules.nonvanishing_section_trivializes`; all three
   depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no new data definition or arbitrary witness from an unproved theorem.
   Verdict: pass.
3. No statements were split off and no new holes or nodes were added. Read both
   proved private helpers: germ representatives and shrinking establish the stalk
   bijection; the free stalk basis identifies maximal-ideal membership with scalar
   membership. The empty scheme, zero section, and empty subopen cases require no
   extra hypothesis. Searched with `msearch.py grep` for stalk/generator and
   nonvanishing/support combinations and inspected the source free-generator lemmas;
   no replacement for the comparison helper was found. Verdict: pass.
4. Read `basicOpen_coeff_eq`, `isFreeGenerator_app_one_of_le`, the invertibility
   comparison, and Stacks `lemma-s-open` in the available local source. The proof
   uses the proved source-library free-generator route, without adding a lower hole.
   Every proof-only import supplies a used declaration: `FlatPullbackStalk` supplies
   `germ_smul`, `ClearDenominators` supplies the coefficient/open and free-generator
   lemmas, and `ProjectionFormula` supplies the invertibility comparison. The existing
   public imports supply the unchanged statement's interface. Checked the original
   proof_deps: all three removed dependencies are explicitly listed under No longer
   needed. Checked `dag/units/sk-thm-reduction.json`: this item is below its fixed
   realized statement/step nodes, and none is bypassed. Verdict: pass.
5. Read the delivered node and the records for its dependencies. Its four proof
   steps describe the Lean argument; proof_deps is exactly the union of their uses,
   and proof_origin identifies the local-coefficient route and source declarations.
   The node's statement and Lean signature record are unchanged. Verdict: pass.

Changes made by the second reader: appended this independent review and recorded the
additional search. No Lean or DAG repair was necessary. Closed one original hole,
added zero holes, and split off zero statements; this remains a proof rather than a
 decomposition. The scratch axiom check is outside the delivered lean/ tree.
