## What changed

Proved `AlgebraicGeometry.IsCurve.clopen_last_four` in
`Sheaf.AlgebraicGeometry.Curve.ClopenConstantAssertionsLast`, without changing its
signature, visibility, or existing docstring. Added proof-only imports of
`Sheaf.Paper.FiniteCoproductCohomologyAssembly`,
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

Repaired the maintainer's duplicate-statement return: removed the private
`comparison_surjective_of_iso` and `comparison_bijective_of_iso` statements.
Their library counterparts in `ReducedConstantLowerShriekAssertions` are private
and cannot be reused by import. Generalized the local transport argument in place
to `comparison_conjugate`, an equality identifying the complete comparison map
with a conjugate through the two cohomology equivalences. The C6, C7, and C8
branches now rewrite by this identity and apply the existing generic
`Equiv.bijective`, `Equiv.surjective`, and function-composition lemmas. This
establishes a stronger identity rather than repeating either transfer statement;
no module owned by another group is changed.

The private helpers are all fully proved. They identify the disjoint covering opens
and their pullbacks as coproducts, identify restricted underlying constant module
sheaves, transfer cohomology maps through coefficient isomorphisms, and prove that
surjectivity/bijectivity can be checked componentwise. The four final branches use
the C5, C6, C7, and C8 projections of the supplied component assertions. Properness
of each clopen inclusion, constructible pullback, and stalkwise torsion transport
supply their conditional hypotheses. Updated the existing node's proof, proof_deps,
and proof_origin to describe the compiled route. No interface adaptations.

The coproduct and product arguments also cover empty schemes, an empty index type,
and empty components. The morphism comparison helpers impose no properness,
field-extension, or open-immersion assumptions; those assumptions are used only
when invoking the relevant component assertion. No arbitrary data is chosen from
an unproved existence theorem: the constructions of all private definitions use
explicit isomorphisms, and the preimages chosen in proofs use proved surjectivity.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.IsCurve.clopen_last_four`
(node `lem-pbc-k2-clopen-constant-assertions-last`).
No `sorry` remains in the item, and no holes or new modules were added.
This is a proof from existing coproduct assembly, pullback functoriality, and
constructible/stalk/constant-sheaf results, not a decomposition into new holes.
The local single-file compile passed without warnings, with `autoImplicit=false`.

## No longer needed

No original import was removed: the public import of curve assertion definitions
is needed for the unchanged statement.

Removed the following planned direct proof dependencies from this node:

- `lem-weil-pbc-etale-sheaf-clopen-product`, module
  `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`: the already proved cohomology
  assembly theorem supplies everything needed here. Its own proof still uses the
  sheaf equivalence, so this is removal of a direct edge, not a claim that this
  module leaves the targets' entire import closure.
- `lem-weil-pbc-finite-pushforward-cohomology`, module
  `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`: no finite-pushforward
  edge comparison is used in this proof. The coproduct restriction theorem is
  sufficient; other users of this module are unaffected.

The exploratory import
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` was removed: the only
lemma needed from it was torsion invariance under a coefficient isomorphism,
which is proved directly with stalk linear equivalences. No smooth-base-change
result is needed. Exploratory direct imports of
`Mathlib.Algebra.Category.ModuleCat.Colimits` and
`Mathlib.CategoryTheory.Sites.PreservesSheafification` were also removed after
verifying that the retained imports already expose the required declarations.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery repeated two private coefficient-transport theorems from
`Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions`. The repair
removes both duplicate statements and uses one stronger map-conjugation identity
with generic equivalence transport. The previous second reading predates this
repair and has been removed so the next reader can review the repaired version.

The DAG's finite-product plan is correct, but it need not separately invoke
finite-pushforward cohomology or the sheaf-category product equivalence. The
existing finite coproduct assembly theorem already provides the canonical
restriction map, and existing composition naturality provides the necessary
commuting square. Mathlib supplies the scheme-coproduct recognition theorem and
pullback-image formulas, including the empty case.

The blueprint source path recorded by the node is not present in this local
read-only checkout. The implementation follows the finite-disjoint-union argument
provided in the existing node and declaration docstring, with every step checked
against the actual Lean signatures and compiled. The unit record `sk-thm-p1`
was read; no realized unit statement or step is bypassed or altered.

## Second reading by V1

1. **Unchanged interface — PASS.** Read the entire delivered module and diffed it
   against the read-only repository version. A byte comparison confirms that the
   existing theorem's complete docstring and signature through `:= by` are
   identical. The sole public import is unchanged; the four added imports are
   proof-only. All added declarations are private. No statement, definition used
   by another module, visibility, or other group's file is changed.
2. **Kernel-checked proof — PASS.** Independently compiled the delivered file with
   `lcompile.py`: exit 0, no warnings, 44.6 seconds. Replaced the stale scratch
   axiom-check copy with the repaired module and compiled it with
   `#print axioms AlgebraicGeometry.IsCurve.clopen_last_four`: exit 0, 39.3 seconds,
   exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   Scanned the delivered Lean sources for `sorry` and prohibited declarations:
   none. The explicit coefficient isomorphisms and cohomology equivalences are
   genuine constructions; the coproduct witnesses are proofs of universal
   properties, and component preimages are chosen only from proved surjectivity.
3. **Split statements and small cases — PASS.** There are no split-off statements,
   new public statements, new nodes, or new holes. Read each private helper:
   conjugation follows from coefficient naturality; the two coproduct witnesses
   use disjoint covering images; the component comparison arguments use assembly
   and the pullback commuting square. With an empty index, coverage forces the
   scheme empty, and the empty product is a singleton; with one component these
   arguments reduce to the component assertion. Empty components cause no
   exception. The conditional C5/C6/C7 hypotheses are supplied exactly where
   their corresponding component assertions require them; C8 uses the pulled-back
   open immersion.
4. **Shortest route and pruning — PASS.** Read the assembly and functoriality
   modules, the assertion predicates, the existing clopen cohomology material,
   and `dag/units/sk-thm-p1.json`. Searched the library using alternate phrases
   for clopen/component cohomology and coefficient-isomorphism transport, and ran
   the launcher's `msearch.py` grep search. No available result eliminates the
   needed component comparison argument. The old private transfer statements
   are absent: all three branches use the stronger conjugation identity and
   generic equivalence/composition results. A torsion-isomorphism lemma exists
   in `SmoothBaseChange.Derived`; the short stalk argument avoids importing that
   unrelated development. The retained proof imports supply assembly,
   composition naturality, constructible pullback/isomorphism invariance, and
   closed-immersion recognition. `No longer needed` lists both old dependency
   edges absent from the new proof. These are direct edges only; no whole module
   is claimed pruned from the target closure. No realized unit statement or step
   is changed or bypassed.
5. **DAG agreement — PASS.** Diffed the delivered node against the repository:
   only `proof`, `proof_deps`, and `proof_origin` change. Read the Lean records of
   all six listed dependencies and checked their declarations against the proof.
   The set of `proof_deps` equals the union of the proof steps' `uses`. The steps
   accurately describe coproduct recognition, constant-coefficient restriction,
   composition compatibility, and each of C5–C8. No new-node fields are required.

Second reading changed only this report and the scratch axiom-check copy, which
previously tested the superseded proof. No delivered Lean or DAG repair was needed.
The independent verdict applies to the repaired `comparison_conjugate` version.
