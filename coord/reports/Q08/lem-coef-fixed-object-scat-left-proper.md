## Worker report

The module `Sheaf.AlgebraicTopology.FixedObjectScatLeftProper` states
`fixed_object_scat_left_proper`, the fixed-object left-properness assertion for
simplicial categories. Its proof is `sorry`, as required at stage 2. The module
imports the statement dependency
`Sheaf.AlgebraicTopology.SimplicialIntervalLifting`.

The Lean statement renders each clause of the node as follows:

- `O : Type u` is the small fixed object set in one explicit universe.
- `[m : ModelCategory (Fixed O)]` supplies the model structure on the category
  of simplicial enrichments with object set `O`; the fields `cm1b` of this
  structure provide finite colimits and hence the pushout used below.
- `hweak` identifies the model structure's weak-equivalence class with
  `fixedWeakEquivalences O`. This is exactly the node's objectwise weak
  homotopy equivalence condition, since that dependency definition quantifies
  over every `a b : O` and uses `Enhanced.IsWeakHomotopyEquivalence` on the
  mapping simplicial sets, with no Kan assumption.
- `hcof` identifies its cofibration class with `fixedCofibrations O`, which is
  the left lifting property against the conjunction of objectwise Kan
  fibrations and objectwise weak equivalences, exactly the node's cofibration
  clause.
- `u : A ⟶ B` and `i : A ⟶ C` are maps in `Fixed O`, so their object map is
  literally the identity on `O`.
- `fixedWeakEquivalences O u` and `fixedCofibrations O i` are respectively the
  two hypotheses that `u` is an objectwise weak equivalence and `i` is a fixed-
  object cofibration.
- `pushout.inr u i : C ⟶ pushout u i` is the canonical map from `C` to
  `B ⨿_A C`, and the conclusion `fixedWeakEquivalences O (pushout.inr u i)` is
  the required objectwise weak homotopy equivalence. The pushout is in
  `Fixed O`, supplied by the model-category finite-colimit instance.

Dependency declaration used:

- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`, declarations
  `SSet.Bergner.Fixed`, `SSet.Bergner.fixedWeakEquivalences`, and
  `SSet.Bergner.fixedCofibrations`. I read their full signatures and
  docstrings. `Fixed` is `EnrichedCategory SSet.{u} O`; the weak-equivalence
  property is mappingwise `Enhanced.IsWeakHomotopyEquivalence`; and the
  cofibration property is the LLP against the conjunction of mappingwise Kan
  fibrations and weak equivalences. The dependency theorem
  `SSet.Bergner.simplicial_interval_lifting` supplies the fixed-object model
  structure, but the present statement records the model structure as the
  explicit typeclass `m` and the two identifying equalities.

Edge cases checked: `O = PEmpty` gives no mapping pairs, so the universal
mappingwise conditions and the conclusion are vacuous; `O = PUnit` reduces to
a one-object simplicial monoid; identity-only mapping simplicial sets are
allowed; empty mapping sets are allowed; `A = B`, `A = C`, or `u`/`i` identity
maps reduce to the ordinary pushout identities; no Kan condition is imposed on
any mapping simplicial set; the universe binder `Type u` matches the dependency
`Fixed O` and does not add a size restriction beyond the node.

Searches for an existing declaration were made on 2026-10-17:

- `msearch.py ... leanfinder "left properness pushouts of weak equivalences along cofibrations in fixed-object simplicial categories"` returned only generic Mathlib model-category cobase-change declarations; none concerns fixed-object simplicial categories.
- `msearch.py ... loogle "SSet.Bergner.fixedWeakEquivalences, SSet.Bergner.fixedCofibrations, pushout.inr"` returned no result (the project-specific names are not in the Loogle index).
- `msearch.py ... grep "leftProper|left_proper|fixed_object_scat_left_proper" Mathlib/AlgebraicTopology` returned zero hits.
- `rg` over `WeilConjectures/` and the project's `lean/Sheaf/` found no declaration of this theorem. The only project hit is the citer's docstring in `SimplicialIntervalCellStability.lean`, which references the DAG item but does not declare it.
- `grep -rn "lem-coef-fixed-object-scat-left-proper" WeilConjectures` found no source declaration.

No statement fault or `STATEMENT-DISPUTED` applies.

## Second reading by Q08

I opened the node, its source place, the dependency node and declaration, and the
Lean module independently. The source is Bergner, *A model category structure on
the category of simplicial categories*, Lemma 3.4 (printed p. 11), which invokes
Dwyer--Kan, *Simplicial localizations of categories*, Proposition 7.3(ii) for
properness of the fixed-object model. The source proposition states preservation
of weak equivalences under pushout along cofibrations; it does not require Kan
mapping objects. The node extracts its left-proper half, exactly as stated.

The node's objects, hypotheses, and conclusion match the Lean as follows.

- The small fixed object set is rendered by `(O : Type u)`. `SSet.Bergner.Fixed`
  is the dependency's `EnrichedCategory SSet.{u} O`, so the object set and its
  universe are the same.
- The fixed-object model structure is rendered by
  `[m : ModelCategory (Fixed O)]`. The equalities
  `hweak : m.categoryWithWeakEquivalences.weakEquivalences =
  fixedWeakEquivalences O` and
  `hcof : m.categoryWithCofibrations.cofibrations = fixedCofibrations O`
  identify precisely the model classes supplied by
  `lem-coef-simplicial-interval-lifting`. No additional fibrancy, size, or
  Noetherian hypothesis occurs. The model-category instance supplies finite
  colimits, hence the required pushout.
- The maps `u : A ⟶ B` and `i : A ⟶ C` occur in
  `∀ {A B C : Fixed O} (u : A ⟶ B) (i : A ⟶ C)`. Since `Fixed O` uses
  `FixedHom`, their object map is literally the identity on `O`.
- The two assumptions are rendered by
  `fixedWeakEquivalences O u` and `fixedCofibrations O i`. The first expands to
  `∀ a b : O, Enhanced.IsWeakHomotopyEquivalence (u.map a b)`, and the second
  is the LLP against `fixedFibrations O ⊓ fixedWeakEquivalences O`, exactly the
  objectwise trivial Kan-fibration condition in the node.
- The pushout object and canonical map are rendered by
  `pushout.inr u i : C ⟶ pushout u i`; the conclusion is
  `fixedWeakEquivalences O (pushout.inr u i)`, giving the mappingwise weak
  equivalence required by the node. The implication order is unchanged.

The eight proof clauses in the node are now recorded in the theorem docstring,
in order: strong-free-retract reduction; constant-free coproduct invariance;
degreewise-free diagonal comparison; arbitrary-factor free resolution; the
pushout bar construction; its extra-degeneracy contraction; the comparison of
the identity and weak-equivalence spans; and the final retract argument. Each
step names the same proof dependency as the node where one is used. This was
the only mismatch found: the worker docstring had only a one-paragraph summary,
so I added the eight numbered proof-step summaries. The theorem body remains
`sorry`, as required for stage 2, and the node's `lean.statement` remains
verbatim equal to its signature.

Edge cases checked: `O = PEmpty` makes all mappingwise universal conditions
vacuous; `O = PUnit` gives a one-object simplicial monoid; `A`, `B`, or `C` may
be identity-only or have empty mapping simplicial sets; either map may be an
identity; loops and coincident attaching objects remain allowed; no Kan
condition is imposed on `A`, `B`, or `C`; and `Type u` is the dependency's
universe and does not exclude any small object set covered by the node.

Searches on 2026-10-17 found no existing declaration. `msearch.py` with
LeanFinder queries for fixed-object simplicial-category left properness returned
only generic model-category cobase-change results. The corresponding Loogle
query returned no exact result. `rg` over Mathlib, `WeilConjectures/`, and the
project's `lean/Sheaf/` found no declaration named or equivalent to
`fixed_object_scat_left_proper`; the only project hit is the cited use in
`SimplicialIntervalCellStability.lean`. The dependency definitions
`SSet.Bergner.Fixed`, `fixedWeakEquivalences`, and `fixedCofibrations` were read
from `SimplicialIntervalLifting.lean` and are used directly, with no private
copies. Compilation with `scompile.py` succeeds and reports no warnings.

## Earlier second reading (a previous round; superseded)

The node and module were read independently. The theorem binds the fixed object
set, the model-category instance, and the two class-identification equalities,
then quantifies exactly over the two fixed-object maps and states the canonical
pushout inclusion. `fixedWeakEquivalences` and `fixedCofibrations` are the exact
dependency predicates, and no Kan or extra fibrancy hypothesis is introduced.
The empty-object, one-object, identity, and empty-mapping cases remain covered.
No mismatch was found.
