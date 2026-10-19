## Worker report

The delivery states `SSet.RezkLocalModel.segal_categorical_constancy` in
`Sheaf.AlgebraicTopology.SegalCategoricalConstancy`. Its only proof is `by sorry`.
There are no new definitions, dependency repairs, statement corrections, or disputed
statements. The item's node changes only in `lean`.

Source checked: Joyal--Tierney, *Quasi-categories vs Segal spaces*,
https://arxiv.org/html/math/0607820, Proposition 3.4 (rows are quasicategories),
Proposition 4.4 (categorical constancy), and Theorem 4.5 (rowwise categorical
weak equivalences are Rezk weak equivalences). The article was opened online.
Archival copy remains WANTED, as already noted in the node's source record.
The theorem docstring includes all seven steps of the node's proof plan, with
its division, walking-isomorphism, fibrant-test and Quillen-preservation inputs.

Clause-by-clause correspondence:

- A bisimplicial set is `X : RezkLocalModel.Bisimplicial.{u}`, the dependency's
  existing abbreviation `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. Its first stored variable is
  vertical: `X.obj (op ⦋q⦌)` is precisely the outer simplicial set `X_{bullet,q}`.
  For the outer-first Segal predicate the same object is
  `Functor.uncurry.obj X.flip`; flipping changes storage order, not the object.
- The hypothesis “vertically Reedy fibrant complete Segal space” is exactly
  `CategoryTheory.SegalSpace.IsComplete (Functor.uncurry.obj X.flip)`.
  `IsComplete` includes `IsSegal`, which includes `IsReedyFibrant`; no independent
  assumption or structure on X is introduced or lost.
- “Every row is a quasicategory” is the first conjunct
  `(X.obj (op ⦋q⦌)).Quasicategory` for every `q : ℕ`.
- The unique vertical map `[q] → [0]` is
  `SimplexCategory.isTerminalZero.from ⦋q⦌`. Applying `op` and then `X.map` gives
  exactly a map `X.obj (op ⦋0⦌) ⟶ X.obj (op ⦋q⦌)`. There is no choice of a row map
  and no arbitrary comparison map.
- “Categorical equivalence” is rendered by the precise Joyal dependency's test:
  after `uliftFunctor.{v,u}.map` of this degeneracy, `MonoidalClosed.pre` restricts
  the internal functor simplicial sets into each quasicategory `C`;
  `hoFunctor.map` then induces the ordinary homotopy-category functor, and
  `Functor.IsEquivalence` asserts that it is an equivalence. The tests have
  `C : SSet.{max u v}`, with both universes explicitly declared, so every allowed
  larger test universe is covered. This is the same expression as in
  `SSet.exists_joyal_model_structure`, not a newly defined equivalence notion.
- The final assertion is the separate second top-level conjunct, quantified over
  arbitrary `{X Y : Bisimplicial.{u}}` and `f : X ⟶ Y`. Its sole assumption is
  the categorical-equivalence test on `f.app (op ⦋q⦌)` for every `q : ℕ`.
  There is no completeness or fibrancy assumption on X or Y in this conjunct.
- Its conclusion is the exact Rezk dependency's characterization of a Rezk weak
  equivalence: for every complete `Z : Bisimplicial.{u}`,
  `Enhanced.IsWeakHomotopyEquivalence (eHomWhiskerRight SSet f Z)`.
  Mathlib's enrichment on this vertical-first functor category is the vertical
  mapping simplicial set, so this is restriction `Map_ss(Y,Z) → Map_ss(X,Z)`.
  The completeness of Z restricts the testing objects, exactly as the recorded
  Rezk characterization does. It places no condition on the source or target.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RezkLocalModel`:
  `SSet.RezkLocalModel.Bisimplicial` and
  `SSet.RezkLocalModel.exists_rezk_model_structure`. Its existing vertical-first
  storage and the displayed weak-equivalence test are used verbatim.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; its full signature supplies the categorical
  equivalence test, including `max u v` and the actual universe-lift functor.
- The existing Segal predicate re-exported by Rezk is
  `CategoryTheory.SegalSpace.IsComplete` in `Sheaf.CategoryTheory.SegalSpace`.
  Its docstring and full definition, including the inherited Reedy and Segal
  hypotheses, were read. Its definition is reused without modification.
- Existing Mathlib constructions: `SimplexCategory.isTerminalZero`,
  `Functor.flip`, `Functor.uncurry`, `SSet.Quasicategory`, `SSet.hoFunctor`,
  `SSet.uliftFunctor`, `MonoidalClosed.pre`, `Functor.IsEquivalence`, and
  `CategoryTheory.EnrichedCategory.eHomWhiskerRight` (re-exported by the dependencies).
- Non-public proof imports follow every recorded, stated proof dependency:
  `Sheaf.AlgebraicTopology.BisimplicialReedyDivisionCalculus`
  (`SSet.BisimplicialDivision.bisimplicial_reedy_division_calculus`),
  `Sheaf.AlgebraicTopology.CompleteSegalWalkingIsomorphism`
  (`SSet.BisimplicialDivision.complete_segal_walking_isomorphism`),
  `Sheaf.AlgebraicTopology.JoyalWalkingIsomorphismFibrationTest`
  (`SSet.joyal_walking_isomorphism_fibration_test`),
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`
  (`SSet.KanQuillen.right_proper_kan_quillen`),
  `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`
  (`HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`),
  `Sheaf.CategoryTheory.QuillenFibrantTest`
  (`HomotopicalAlgebra.quillen_fibrant_test`), and
  `Sheaf.AlgebraicTopology.SegalVerticalRestrictionInner`
  (`SSet.segal_vertical_restriction_inner`). The Joyal and Rezk proof dependencies
  are already public imports because they are also statement dependencies.

Edge cases checked before writing: at `q = 0` the terminal simplex map is the
identity (the hom-set to `[0]` is unique), so the asserted degeneracy is the row
identity. Empty complete Segal spaces are included, with empty quasicategory rows;
there is no nonemptiness binder. The proof plan retains the empty degree-zero
boundary lifting test. The second conjunct applies to arbitrary nonfibrant
bisimplicial sets, not merely complete Segal representatives. Universe `u` is
arbitrary and `max u v` never chooses tests smaller than the input.

Searches made (2026-10-17):

- `msearch.py ... leanfinder`: “Rows of a complete Segal space are quasicategories
  and categorically constant; rowwise categorical equivalences are Rezk weak
  equivalences”. Eight hits: StrictSegal quasicategory lemmas, strict Segal
  definitions and QCat. These concern one strictly Segal simplicial set; none
  states the Rezk constancy/comparison theorem for a bisimplicial set.
- `msearch.py ... loogle`: `Segal, Quasicategory, IsEquivalence`.
  Zero hits, diagnostic `unknown identifier 'Segal'`.
- `msearch.py ... grep`: `Rezk|categorical.?constan|rowwise.*categorical`,
  subdirectory `AlgebraicTopology`: zero hits.
- `rg` of `Rezk|categorical.?constan|rowwise.*categorical` throughout upstream
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: zero hits.
- `grep -rn` of the exact node id throughout that upstream source: zero hits.
- `rg` of those patterns in `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`:
  related Rezk construction, finite interval, Segal-space and inverse-evaluation
  modules exist; no theorem giving this node's categorical constancy and
  rowwise comparison. A further narrower search of
  `categorical.?constan|rowwise.*categorical|segal_categorical_constancy`:
  zero hits. Existing notions in RezkLocalModel and SegalSpace are reused.
- `rg` of `Segal|CategoricalEquivalence|categorical_constancy` in
  `dag/lean_names_upstream.json`: zero hits. No existing declaration attachment.
- No repair note matching this item is present in `coord/repair-notes/`.

Validation uses only the prescribed `scompile.py`, then `deliver2.py --no-push`
(server preflight and file compilation), and finally `deliver2.py`.

## Second reading by NM

Independent maintainer second reading, 2026-10-17, of immutable delivery
`aef3b3f2ff83e69dca8438839e208c1d29ff6785`. This replaces the delivered author's
self-check; the worker's report above is preserved. I did not write or previously
second-read the delivery.

## Statement and dependency checks

1. Objects and coordinates: `Bisimplicial.{u}` is the recorded
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}` in RezkLocalModel. Its stored outer functor variable is
   the vertical variable of the paper. Thus `X.obj (op ⦋q⦌)` is the requested horizontal
   row, and `Functor.uncurry.obj X.flip` has the outer-first convention of SegalSpace.
2. Hypothesis: the existing `CategoryTheory.SegalSpace.IsComplete` includes `IsSegal`,
   which includes `IsReedyFibrant`; it therefore supplies exactly completeness,
   homotopy Segalness and vertical Kan Reedy fibrancy. I read these definitions,
   including the matching maps in degree zero and the actual degeneracy factor through
   the equivalence-arrow subcomplex. No extra instance or hypothesis occurs here.
3. Row conclusion: for every natural number q, the first conjunct asserts the
   quasicategory condition on that actual row. There is no positivity restriction.
4. Canonical comparison: `SimplexCategory.isTerminalZero.from ⦋q⦌` is the unique
   `[q] → [0]`, by Mathlib's `uniqueHomToZero` and `isTerminalZero`. Applying `.op`
   and X.map produces the requested row-zero-to-row-q map. No comparison is chosen.
5. Categorical equivalence: the test using `uliftFunctor.{v,u}`, `MonoidalClosed.pre`,
   `hoFunctor.map` and `Functor.IsEquivalence` is exactly the weak-equivalence test of
   `SSet.exists_joyal_model_structure`. I read that theorem's signature and docstring,
   and the underlying Mathlib precomposition, universe-lift and homotopy-category API.
   Both u and v are bound and arbitrary; `max u v` permits every larger test universe.
   In particular v is not forced to zero or equated to u. Fixing v in the premise of
   the second conjunct is legitimate because the dependency characterizes the same
   categorical weak-equivalence class for each such enlargement.
6. Arbitrary-map clause: the second top-level conjunct introduces fresh arbitrary X,Y
   and f. Its only hypothesis is the same categorical-equivalence test on each f.app.
   It assumes no Reedy fibrancy, Segalness, or completeness of X or Y.
7. Rezk conclusion: all complete Z in the input universe test the actual
   `eHomWhiskerRight SSet f Z`. This is verbatim the weak-equivalence characterization
   in `SSet.RezkLocalModel.exists_rezk_model_structure`. Mathlib's simplicial-object
   enrichment is in the stored vertical variable, and eHomWhiskerRight reverses the
   source, giving Map(Y,Z) → Map(X,Z). This is the correct vertical mapping complex.

The item's `lean.statement` is byte-for-byte the substring from `theorem` to before
` := by` in the snapshot module, including whitespace. Module, declaration, file,
branch, author, date and existing fields are present and consistent.

## Source and proof-plan checks

Read Joyal–Tierney, *Quasi-categories vs Segal spaces*,
https://arxiv.org/html/math/0607820, §2 (especially Propositions 2.4–2.8),
Propositions 3.4 and 3.10, §4's mapping-space definition, Lemmas 4.2–4.3,
Proposition 4.4 and Theorem 4.5. The source gives the two requested conclusions;
its final rowwise comparison applies to arbitrary bisimplicial maps. This delivery
asserts no converse and does not substitute the later first-row Quillen equivalence.

The seven docstring steps follow the node. Step 1 uses the vertex inclusion,
vertical division lifting, its collapse section and two-out-of-three. Step 2 uses
SegalVerticalRestrictionInner's actual division and inner-fibration conclusions.
Step 3 gets vertical fibrancy from mapping tests and the common monomorphism
cofibrations. Step 4 uses relative division, boundary lifting and two-out-of-three;
its pullback target is a quasicategory by inner lifting. Step 5 uses the full
walking-isomorphism endpoint test, with boundary dimension zero retained.
Step 6 uses QuillenFibrantTest: common trivial fibrations and preservation of
fibrations between fibrant objects suffice. Step 7 uses the cofibrant-object
weak-equivalence preservation conclusion of ModelInfinityDerivedAdjunction;
all horizontal objects are cofibrant. I inspected those exact declaration signatures.
The division and Segal APIs use outer-first storage, so their use requires the
explicit flip/uncurry identification already explained in the module. This is a
coordinate identification, not a missing mathematical assumption or prerequisite.
The proof imports cover the recorded proof dependencies without a downstream cycle
introduced by this delivery. No new node, helper construction, dependency repair,
statement_change or citer audit is required.

## Searches, edge cases and pilot gates

Independent searches used `categorical.?constan`, `rowwise`, `row.wise` and
`segal_categorical_constancy` in the group clone's lean/Sheaf, the upstream
WeilConjectures tree and Mathlib's algebraic topology tree. Related division,
diagonal and downstream comparison modules do not state this theorem. In particular
the downstream CompleteSegalQuasicategoryComparison uses constancy in its proof plan,
not as an existing declaration. The report records semantic search and grep results;
its Loogle query produced an unknown-identifier diagnostic, so I do not count that
as a successful search. The separate LeanFinder search and direct source searches
supply the useful evidence. No duplicate definition is introduced: this module has
no definitions at all and reuses both dependencies' exact tests.

Edge cases checked: q=0 gives the identity by uniqueness of maps to [0]; empty and
terminal complete Segal spaces are included; empty rows are permitted quasicategories;
identity maps and nonfibrant source/target maps remain in the final clause; the
proof plan includes the empty degree-zero boundary. Universes u=0, v=0, u=v and
arbitrary enlargement are allowed. There are no extra finiteness, nonemptiness,
properness or characteristic assumptions.

The sole proof is `by sorry`. There are no hollow data definitions, arbitrary maps,
private notions, local notation or local instances. Source places and blueprint ids
appear in both module and theorem docstrings; the latter includes all seven proof
steps. All lines are at most 100 characters; autoImplicit is false. No pro-etale
substitute is involved.

## Compiler evidence and findings

The immutable report says that validation uses scompile.py and delivery preflight,
but supplies no actual exit status or transcript. I therefore reproduced the only
delivered Lean file using:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py NM lem-coef-segal-categorical-constancy snapshot/lean/Sheaf/AlgebraicTopology/SegalCategoricalConstancy.lean
```

Result: exit 0, no diagnostics; sandbox check 1.4 s, library-path check 1.6 s,
with the 60-second per-file limit. The installed scompile.py currently routes the
private side overlay to the server (`nt_srv_compile.py --wire-confirm`), rather
than the older local route described in the brief. I used that prescribed wrapper
without invoking ssh directly or modifying it. Its output identifies the temporary
`.lbuild` overlay, and separately checks the library module path. There are no sibling
modules in this delivery. No lake/global build, live Lean write, clone edit, Git
mutation, claim, delivery or merge was performed.

Finding H11 was the delivered author self-check in place of independent review.
This section supplies the independent reading and reproducible compiler evidence. No substantive mathematical fault was
found. The source archive remains WANTED as disclosed by the node and worker; the
source itself was read online, so this is not a landing defect. Only review.md and
the complete report replacement under fixes/ were written.
