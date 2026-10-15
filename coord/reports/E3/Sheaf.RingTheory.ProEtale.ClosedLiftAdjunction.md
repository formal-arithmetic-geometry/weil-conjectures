## What changed

Proved `Algebra.ClosedLift.exists_natural_homEquiv` in
`Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction`, with its signature and public imports
unchanged. All added declarations are private, fully proved helpers in the item module.

For a finitely presented indexing algebra, categorical finite presentability factors a
map into the closed lift through one stage. Compatibility with the retained map makes
that factorization an indexing morphism, so the cocone equation proves uniqueness.
A polynomial quotient presentation constructs the unique lift for an etale source.
For an ind-etale source, these unique lifts form a cocone and descend along its chosen
colimit presentation; colimit hom-extensionality proves the required equations and
uniqueness. Choices of lifts are therefore uniquely determined, rather than arbitrary
witnesses of an unproved existence statement.

Constructed the quotient Hom equivalence explicitly using `Ideal.Quotient.lift`, and
composed it with the bijection given by postcomposition with `toAlgHom`. The formula on
representatives is definitional. Proved covariance from `ι_map` and `ι_toAlgHom`, then
identity and composition preservation from lift uniqueness. Proved ind-etaleness of
reduction directly by the source-library theorem
`RingHom.IndEtale.isStableUnderBaseChange`, with the quotient pushout provided by
`CommRingCat.isPushout_quotient`. Added its proof-only import
`WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions`.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-exc-closed-lift-adjunction` to match this argument, citing the existing Mathlib leaf
`lem-weil-pbc-tensor-quotient-base-change` for quotient base change. The unit record has
no realized statement or step requiring either pruned auxiliary dependency, and the
unit's route is preserved.

Validation: the complete item compiles cleanly through `lcompile.py` in approximately
three seconds. The import-direction check accepts the added source-library import.
The proof handles arbitrary ideals, including zero and the unit ideal, and allows zero
rings; it assumes neither nilpotence nor properness of the ideal. It also handles
etale presentations with zero generators and arbitrary filtered presentation categories.

## Proved and sorry left

Holes closed: 1, `Algebra.ClosedLift.exists_natural_homEquiv`
(node `lem-exc-closed-lift-adjunction`).

Holes added: 0. Split-offs: 0. No `sorry` remains anywhere in the delivered Lean module.
Every private helper, including both equivalence constructions, is fully proved.

The proof uses existing imported declarations that remain obligations of other items:
`Algebra.ClosedLift.isFiltered_index` (`lem-exc-closed-lift-filtered`),
`Algebra.ClosedLift.ι_toAlgHom` and `Algebra.ClosedLift.ι_map`
(`def-exc-ind-etale-closed-lift`). The existing definition `map` also uses the existing
proof `Algebra.ClosedLift.postcomp_compatible` of that same node. These are not new
holes or split-offs. The existing stability theorem used for quotient base change is
already proved. This delivery proves the assigned theorem from those existing APIs;
it does not claim that its entire imported axiom closure is already sorry-free.

## No longer needed

Removed these proof-only imports:

- `Sheaf.RingTheory.IndEtaleStability` (second reading: the source library already
  proves the needed ind-etale base-change clause directly).
- `Mathlib.Algebra.Category.Ring.FinitePresentation`.
- `Mathlib.RingTheory.FinitePresentation`.
- `Mathlib.CategoryTheory.Limits.HasLimits`.
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`.
- `WeilConjectures.RingTheory.ProEtale.ClosedLift`.

The declarations from the finite-presentation and colimit APIs used by the proof are
already publicly available through the retained statement imports. No separate
underlying-ring colimit or connected-over-category argument is used.

Pruned proof dependency `lem-weil-pbc-filtered-colimit-algebras-elementwise`: finite
presentability in `CommAlgCat A` directly supplies the stage factorization. The
finite-presentation factorization principle itself remains needed and is retained.

Pruned proof dependency `lem-exc-closed-lift-reduction`: the theorem asserts the
natural Hom equivalence and functor laws, and these do not require that the counit
be an isomorphism. Its source module remains needed for the actual closed-lift
construction and filteredness; no entire source module is claimed unreachable.
The stability node remains a mathematical proof dependency for its base-change clause;
its bundled Sheaf module is no longer imported directly. No additional Sheaf obligation
module is imported, withdrawn, or duplicated. No claim is made that other targets no
longer reach that module.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's final counit-isomorphism step proved more than the Lean
statement requires. The adjunction follows from the natural Hom equivalence itself,
so this delivery removes that dependency without changing the statement.

The original uniqueness step passed to underlying rings and then invoked a
ring-level finite-presentation factorization. The source library already proves
`CommAlgCat.finitePresentation_le_isFinitelyPresentable`, and Mathlib's
`IsFinitelyPresentable.exists_hom_of_isColimit` applies directly to the algebra
colimit. This is the same factorization argument with the unnecessary comparison
removed. No statement, definition, target, or other group's module was changed.

## Second reading by E3

1. **Unchanged interface: PASS.** Read the repository and sandbox modules in full and
   compared them with `diff -u`. The complete signature of the only pre-existing
   declaration, `Algebra.ClosedLift.exists_natural_homEquiv`, is byte-for-byte identical;
   so are all three public imports and the existing docstrings. The new helpers are
   private. No existing definition, other module, target, or statement changed, and no
   change record is required. Compared both JSON records: only `proof`, `proof_deps`,
   and `proof_origin` changed.

2. **Proof and axioms: PASS.** Independently compiled the delivered module with
   `lcompile.py`, then compiled a scratch copy with `#print axioms` for the public
   theorem and all ten private declarations. There are no compiler errors or warnings,
   no `sorry` in the delivered file, no forbidden declaration or kernel-bypassing
   option, and no line longer than 100 characters. The quotient equivalence and
   quotient ind-etaleness helper use only `propext`, `Classical.choice`, `Quot.sound`;
   the other declarations additionally use `sorryAx` from the existing imported
   obligations reported above. No new axiom or hole was introduced. Both equivalences
   have explicit forward maps; inverse choices use proved unique lifting, not a mere
   unproved existence assertion. The retained closed-lift algebra itself is the
   existing concrete colimit construction.

3. **Split statements and correctness: PASS; none split off.** Checked the actual
   argument in every helper. In `index_hom_unique`, finite presentability gives a
   stage factorization, and the equality after `toAlgHom` makes that very factorization
   a morphism of `Index`; its cocone equation gives uniqueness. In `etale_lift_unique`,
   finite presentation supplies a quotient isomorphism; transport along its inverse
   produces the lift, and the previous helper proves uniqueness. For general
   ind-etale sources, the unique stage lifts satisfy the cocone equations, and
   colimit descent and hom-extensionality prove existence and uniqueness globally.
   The quotient equivalence checks that the entire extended ideal is killed, checks
   scalar compatibility over `A/I`, and proves both inverse identities. Checked
   arbitrary ideals, including zero and the unit ideal, zero rings, zero-variable
   presentations, and a one-object filtered presentation: no extra nontriviality,
   properness, nilpotence, or presentation hypothesis is used. There are no new
   public statements or nodes requiring separate source/search records.

4. **Route, shorter proofs, and pruning: PASS after one simplification.** Read
   [Stacks Tag 097P](https://stacks.math.columbia.edu/tag/097P), specifically the
   final Hom-equality and right-adjunction paragraphs; the local literature files
   are absent on this machine. The construction and adjunction agree with those
   paragraphs. Full faithfulness is an additional assertion of the source and is
   not a conjunct of this unchanged Lean theorem, so its reduction-isomorphism
   dependency is correctly pruned. Read the unit's `realized` record: neither pruned
   node realizes a unit statement or step; its route is preserved. A fresh
   LeanFinder search for the universal factorization/coreflection property returned
   finite-presentation and single standard-etale results, not this equivalence;
   `rg` over the source and Sheaf ring-theory modules found no existing equivalent
   proof to apply. Read the source finite-presentability theorem in
   `IndZariski.lean` and the base-change theorem in `IndEtale.lean`. Replaced the
   bundled `RingHom.indEtale_principalZariski_stability.1` by the already available
   `RingHom.IndEtale.isStableUnderBaseChange` and removed
   `import Sheaf.RingTheory.IndEtaleStability`. The remaining new import supplies
   `CommRingCat.isPushout_quotient` and is correctly proof-only. Every removed import
   and both old dependencies no longer used are listed under `## No longer needed`.

5. **DAG agreement: PASS after metadata update.** Read every retained dependency's
   statement and Lean/Mathlib record. Checked the quotient-base-change leaf against
   the actual tensor-quotient transport inside `CommRingCat.isPushout_quotient`;
   checked the finite-presentation dependency against the categorical factorization
   actually used; checked ind-etaleness and colimit dependencies against the
   presentation and descent code. The five revised proof steps describe precisely
   the quotient equivalence, finite-stage uniqueness, etale lift, colimit lift, and
   naturality/functor-law arguments. Their `uses` union is exactly `proof_deps`.
   Updated step 1 and `proof_origin` to name the direct source base-change theorem;
   the stability node remains the mathematical base-change fact used. No new node,
   signature change, or forced adaptation was added.

Second-reading changes: used the direct source-library base-change theorem, removed
one unnecessary proof-only Sheaf import, updated the matching proof metadata and
pruning report, and added this independent review. Final module and scratch axiom
check both compile cleanly after these changes. Holes closed: one; holes added: zero.
