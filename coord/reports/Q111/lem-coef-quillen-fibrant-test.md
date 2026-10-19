## Worker report

The module `lean/Sheaf/CategoryTheory/QuillenFibrantTest.lean` states
`HomotopicalAlgebra.quillen_fibrant_test`. Its sole proof is `by sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes. Its statement signature is copied verbatim,
including line breaks, from the module, and all universes and variables are explicit.

The earlier BLOCKED diagnosis confused a completed stage-1 split with a completed
stage-2 statement. Q82's report and merged node provide the eight-step natural-language
proof, but the current node has no `lean` record and no corresponding declaration.
This delivery supplies that missing statement rather than re-delivering the stage-1 split.
No repair note exists for this item.

I read the item, its full eight-step proof, its sole statement/proof dependency
`lem-coef-model-infinity-derived-adjunction`, the dependency's Lean record, and the
signature and docstring of
`HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization` in
`Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`. That public module is imported.
Its model-category conventions are reused directly, not redefined. The dependency
already encodes Quillen adjunctions by preservation conditions, rather than by a
separate predicate. Its derived-localization theorem is not applied here: that theorem
starts with a Quillen adjunction, while this item recognizes one.

Source checked: Hirschhorn, *Model Categories and Their Localizations*, Proposition
8.5.4, (3) implies (1), printed pp. 153--155, at
<https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf>.
The proposition permits testing fibrations only between fibrant objects, while its
trivial-fibration test applies to all endpoints. The module docstring carries the
item's eight-step factorization/lifting/retract proof, with Lean-order compositions.

Hypotheses and conclusions, clause by clause:

- The arbitrary model categories are `{A : Type u₁} {B : Type u₂}` with independent
  `[Category.{v₁} A]`, `[Category.{v₂} B]`, `[ModelCategory A]`, `[ModelCategory B]`.
  Mathlib's `HomotopicalAlgebra.ModelCategory` supplies the three morphism classes,
  two-out-of-three, retract closure, lifting axioms and the two factorizations.
- The dependency's complete and cocomplete convention is retained with
  `[HasLimits A] [HasColimits A] [HasLimits B] [HasColimits B]`.
  Both functorial factorizations for each category are explicit via
  `(cofibrations A).HasFunctorialFactorization (trivialFibrations A)` and
  `(trivialCofibrations A).HasFunctorialFactorization (fibrations A)`, and the same
  two instances for `B`. These are part of the model-category notion explicitly
  specified by the node's first sentence, not extra assumptions on the adjunction.
- The ordinary adjunction, without a Quillen hypothesis, is given by
  `(L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)`.
- Preservation of every trivial fibration is `hRt`: for every `p : X ⟶ Y` in `B`,
  `Fibration p → WeakEquivalence p →
  Fibration (R.map p) ∧ WeakEquivalence (R.map p)`.
  There is no fibrancy requirement in this hypothesis. These two properties are
  exactly Mathlib's `trivialFibrations`, as its `mem_trivialFibrations_iff` states.
- Preservation of fibrations between fibrant objects is `hRf`, with both
  `IsFibrant X` and `IsFibrant Y`, followed by
  `Fibration p → Fibration (R.map p)`. `IsFibrant` means that the terminal map
  is a fibration, exactly as in the dependency node.
- The first conclusion quantifies over all arrows of `B` and asserts
  `Fibration p → Fibration (R.map p)`, without either endpoint fibrancy premise.
- The second conclusion asserts `Cofibration i → Cofibration (L.map i)` for
  every arrow of `A`.
- The third conclusion asserts
  `Cofibration i → WeakEquivalence i →
  Cofibration (L.map i) ∧ WeakEquivalence (L.map i)` for every arrow of `A`.
  By `mem_trivialCofibrations_iff` this is preservation of trivial cofibrations.
- These conclusions together with `adj` and the already assumed `hRt` say that
  the adjunction is Quillen, using precisely the dependency's preservation
  convention. No separate duplicate Quillen definition or redundant assumed
  conclusion is introduced.
- No enrichment, properness or combinatoriality assumption occurs. No localization,
  replacement, coherent functor or additional object is required in this recognition
  statement.

Primitive declaration sources read: Mathlib
`AlgebraicTopology.ModelCategory.Basic` (`ModelCategory`),
`AlgebraicTopology.ModelCategory.CategoryWithCofibrations`
(`Fibration`, `Cofibration`, `WeakEquivalence`, `trivialFibrations`,
`trivialCofibrations`, and the two membership equivalences),
`AlgebraicTopology.ModelCategory.IsCofibrant` (`IsFibrant`),
`CategoryTheory.MorphismProperty.Factorization` (`HasFunctorialFactorization`),
and `CategoryTheory.Adjunction.Basic` (`Adjunction`). They are publicly available
through the recorded dependency module. No copy of any notion is defined here.

Edge cases checked before writing:

- For the identity adjunction both preservation tests and all conclusions are
  identities; no extra fibrancy assumption is needed.
- The terminal category with its unique model structure satisfies the statement;
  it is not excluded by a nontriviality or size assumption.
- An empty category cannot satisfy the stated model axioms, since it lacks a
  terminal object; the statement does not add a nonempty binder.
- Trivial fibrations with nonfibrant endpoints remain covered by `hRt`.
  General fibrations with nonfibrant endpoints remain covered by the conclusion.
  Fibrancy of both endpoints occurs only in `hRf`.
- Source and target object/hom universes are independent. No equality of category
  universes, common object type, characteristic, or coefficient restriction appears.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `An adjunction is Quillen if its right adjoint preserves all trivial fibrations and
  fibrations between fibrant objects`: eight hits for fibrant objects, bifibrant
  inclusions and simplicial-set fibrations; no recognition theorem.
- `msearch.py ... loogle` with query `IsRightQuillen, IsFibrant, Fibration`:
  zero hits, with the diagnostic `unknown identifier 'IsRightQuillen'`.
- `msearch.py ... grep` with regex
  `Quillen|quillen|preserves.*fibr|fibrant.*adj` in
  `AlgebraicTopology/ModelCategory`: fourteen hits, mainly references to Quillen
  and the bifibrant homotopy-category adjunction; no such recognition theorem.
- `rg` for `Quillen|quillen` throughout upstream `WeilConjectures` and for the
  exact node id: no upstream declaration. A first attempted narrow upstream
  `Mathlib/AlgebraicTopology` directory did not exist, so the complete upstream
  tree was searched instead.
- `rg` for `IsRightQuillen|IsLeftQuillen|isRightQuillen|isLeftQuillen` in Mathlib's
  algebraic-topology sources and upstream `WeilConjectures`: no hits.
- `rg` for fibrant-test and right-Quillen names in `lean/Sheaf` and Mathlib's
  model-category sources: related Quillen applications and the existing derived
  adjunction, not the recognition criterion. `quillen_fibrant_test` and
  `quillenFibrantTest` are absent from `dag/lean_names_upstream.json`.

No mathematical node fault or STATEMENT-DISPUTED concern was found.

Validation: the prescribed `scompile.py Q111 lem-coef-quillen-fibrant-test` compiled
both the sandbox check and the module at its library path cleanly (1.2 seconds each).
The dry run is recorded below after it completes. No push is made by this worker.

## Second reading by Q111

I independently read the DAG node, its eight proof steps, this module, and the
statement and public source declaration of its sole dependency,
`HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization` in
`Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`. I also read Mathlib's
`ModelCategory`, arrow predicates, `IsFibrant`, and Joyal lifting lemmas.
No repair note exists for this item. No new nodes, dependency modules, or
`statement_change` are included, so the additional-node and correction audits
are inapplicable.

Source verification: I opened [Hirschhorn's book](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf),
Proposition 8.5.4, printed pp. 153--155, including its duality argument. Its
condition (3) is exactly the two tests in this node. I also read the standing
model-category convention in Section 7.1 and Definition 7.1.3, printed
pp. 108--109, and the Quillen-pair definitions and equivalent preservation
conditions in Definition 8.5.2 and Proposition 8.5.3, printed p. 153. These
confirm arbitrary small limits and colimits and functorial factorizations;
no properness, enrichment, or combinatoriality is assumed. There is no Stacks
source for this node.

My object/hypothesis/conclusion checklist, with the node and Lean open:

1. Two arbitrary model categories A and B: `{A : Type u₁} {B : Type u₂}`,
   `[Category.{v₁} A] [Category.{v₂} B]`, and `[ModelCategory A]
   [ModelCategory B]`. Correct. Mathlib's class supplies finite (co)limits,
   the three arrow classes, two-out-of-three, retract closure, lifting, and
   both weak factorizations; it does not by itself supply the stronger
   source convention.
2. The referenced model-category convention is complete/cocomplete with
   functorial factorizations: the four `HasLimits`/`HasColimits` binders
   and the four `HasFunctorialFactorization` binders supply exactly this.
   Correct, and identical to the dependency's category hypotheses, rather
   than extra restrictions added to the adjunction.
3. An ordinary adjunction with no Quillen assumption: `(L : A ⥤ B)` and
   `(R : B ⥤ A)` with `(adj : L ⊣ R)`. Correct orientation and quantifiers.
4. Every trivial fibration of B, with unrestricted endpoints, is preserved:
   `hRt` quantifies over every `p : X ⟶ Y` and takes `Fibration p` and
   `WeakEquivalence p`, concluding both predicates for `R.map p`.
   Correct by `mem_trivialFibrations_iff`; no endpoint fibrancy is assumed.
5. Fibrations between two fibrant objects are preserved: `hRf` quantifies
   over every arrow in B and assumes `IsFibrant X`, `IsFibrant Y`, and
   `Fibration p`, concluding `Fibration (R.map p)`. Correct. `IsFibrant`
   is Mathlib's terminal-map fibration, not a private or cofibrant notion.
6. R preserves all fibrations: the first conjunct universally quantifies
   over arrows of B with only `Fibration p`. Correct, including endpoints
   that are not fibrant.
7. L preserves all cofibrations: the second conjunct universally quantifies
   over arrows of A with only `Cofibration i`. Correct.
8. L preserves all trivial cofibrations: the third conjunct quantifies over
   arrows of A with `Cofibration i` and `WeakEquivalence i` and asserts
   both predicates for `L.map i`. Correct by `mem_trivialCofibrations_iff`.
9. The adjunction is Quillen: clauses 6--8, together with `adj` and `hRt`,
   spell out the dependency's preservation convention. No extra Quillen
   predicate is needed, and no clause of the node is lost or strengthened.
10. No enrichment, properness, or combinatoriality: no such hypotheses or
    structures occur. Correct.

Edge cases: all four object/hom universes are independently bound; no
same-universe restriction occurs. Identity adjunctions and the terminal
category are covered. An empty category cannot be a model category with
terminal object, so there is no omitted empty-category instance. Zero objects
are neither assumed nor excluded; in pointed model categories they are covered
as ordinary objects. There is no index family, degree, characteristic, scheme,
or coefficient ring in this node. In particular the crucial nonfibrant-endpoint
cases remain in `hRt` and in the first conclusion.

Independent H4 searches (new wording, using the prescribed wrapper):

- LeanFinder: `A right adjoint preserving acyclic fibrations and fibrations
  between fibrant objects preserves every fibration`. Eight hits, including
  `isFibrant_of_fibration`, fibrant-subcategory instances and `fibration_iff`;
  these concern individual arrows or objects, not adjunction recognition.
- Loogle: `"fibrant", "Functor"`. Twelve hits in the fibrant/cofibrant
  localization machinery, including resolution functors and their comparison
  isomorphisms; none states the recognition theorem.
- Grep: `adjoint|preserv|joyalTrick` in `AlgebraicTopology/ModelCategory`.
  Three hits: the two Joyal lifting lemmas and the bifibrant localization
  adjunction. I read both Joyal signatures: they assume lifting against all
  arrows in one category and do not give this fibrant-endpoint criterion.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and the project's
  `lean/Sheaf`, using Quillen names and preservation/fibrancy variants.
  Upstream has no Quillen recognition declaration; project hits are Kan model
  structures, specialized boundary-collapse tests, and the already-assumed
  Quillen derived-adjunction theorem. None matches this criterion for arbitrary
  model categories. The exact proposed names are absent from
  `dag/lean_names_upstream.json`. The existing dependency is reused by public
  import; no notion is defined again.

I checked each numbered docstring proof step against the node. In particular,
`j ≫ p ≫ r = j` and `r ≫ p = 𝟙 Y` make `p` an arrow retract of `p ≫ r`,
so the two-out-of-three/retract argument has the correct composition order.
The source and blueprint tags occur in both docstrings. The file contains no
new definition and no proof other than the named theorem's `by sorry`, no
private/local statement notation or instance, and no line exceeds 100 characters.
All variables and universes are explicitly bound. The node's `lean.statement`
is byte-for-byte equal to the file signature before `:= by`.

Mismatches found: none. Changes made: appended this independent second reading
and recorded the fresh searches; left the correct Lean and node binding intact.
Validation: `scompile.py Q111 lem-coef-quillen-fibrant-test
lean/Sheaf/CategoryTheory/QuillenFibrantTest.lean` passed both sandbox and library
checks, in 1.3 and 1.4 seconds, with no warnings or errors.

Delivery validation: the prescribed `deliver2.py Q111
lem-coef-quillen-fibrant-test --no-push` completed successfully: `OK (dry run)`;
its temporary commit passed server preflight and compilation. No source or
statement repair was required by preflight.
