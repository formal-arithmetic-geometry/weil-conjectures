## Worker report

The module `Sheaf.CategoryTheory.BrownFiniteDirectRectification` states
`HomotopicalAlgebra.FiniteReedy.brown_finite_direct_rectification` with `sorry` proof.
It uses the recorded coherent-diagram definitions and the project’s canonical
`FiniteReedy.IsLocalization`, enlarged nerves, comparison map, and ordinary-diagram
map. The Brown hypotheses are rendered by an ordinary category `A`, initial object
`zero` with `hzero : IsInitial zero`, morphism properties `C` and `W`, inclusion of
isomorphisms, composition and retract/two-out-of-three classes, factorization
`HasFactorization C W`, pushouts along `C`, and cobase-change stability for `C` and
`C ⊓ W`. The finite direct index is `I` with `[Finite I]`, finite hom types, degree
function `d`, and `hd : IsDirect d`.

The first conclusion is `IsLocalization (W.functorCategory I) (comparison I A L q)`,
which is the stated equivalence of the localization of strict `I`-diagrams with
coherent functors on the nerve. The second conclusion quantifies every coherent
`H : largeNerve I ⟶ L` and supplies a strict diagram `D : I ⥤ A` together with
`SSet.Enhanced.AreNaturallyEquivalent H (diagram q D)`, rendering the requested
coherent rectification and retaining its higher compatibility data.

The declaration’s docstring records all eight proof clauses: dual Brown fractions;
finite-limit preservation; induction on outgoing chain length; conservativity by
Reedy matching pullbacks; essential-surjectivity rectification; slice-fraction lifting
of mapping components; finite-colimit approximation on opposites; and dualization
back with empty, singleton, and span checks.

Dependency declarations used are `SSet.Enhanced.AreNaturallyEquivalent` and the
associated enhanced simplicial constructions from `Sheaf.CategoryTheory.EnhancedDiagramsCones`
(the recorded declaration of `def-cbc-enhanced-diagrams-cones`). The localization
interface, enlarged nerve, comparison, `IsDirect`, and `diagram` are the exact
existing declarations in `Sheaf.CategoryTheory.FiniteReedyLocalization`, recorded by
the existing definition node `def-coef-coherent-localization-interface`; no private
copy was introduced.

Edge cases checked in the statement are the empty index (allowed by `[Finite I]`),
the singleton (degree zero), the span (degrees `1,0,1`), parallel arrows (finite hom
types), and arbitrary object/morphism/index universes (`u`, `v`, `w`, `z`, `t`). No
nonemptiness, coproduct, fibration, functorial-factorization, model-structure, or
saturation hypothesis was added.

Searches made:

* `msearch.py ... leanfinder "Every finite direct homotopy coherent diagram in a Brown cofibration category localization is equivalent to a strict ordinary diagram"`: returned only ordinary model-category localization constructors; no exact Brown rectification theorem.
* `msearch.py ... loogle "HomotopicalAlgebra, Functor"`: returned ordinary `CofibrantObject`/`FibrantObject` localization declarations; no exact match.
* `msearch.py ... grep "Brown|finite.direct|rectif" AlgebraicTopology`: found Brown-lemma/model-category files only; no exact match.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` for Brown finite-direct rectification: no existing declaration; the usable localization interface is `FiniteReedy.IsLocalization`.

No `STATEMENT-DISPUTED` flag or node correction was needed.

## Earlier second reading (a previous round; superseded)

I read the node statement, its Cisinski source citation, the dependency declarations, and the
Lean file independently. The objects and hypotheses match as follows.

1. The ordinary category is `A : Type u` with `[Category.{v} A]`; the Lean binder is exact.
   The chosen initial object is `zero : A` with `hzero : IsInitial zero`; exact.
2. The arrow classes are `C W : MorphismProperty A`. The inclusions of isomorphisms are
   `hCiso : isomorphisms A ≤ C` and `hWiso : isomorphisms A ≤ W`; exact. Composition of `C`
   is `[C.IsStableUnderComposition]`; composition of `W` is included in
   `[W.HasTwoOutOfThreeProperty]`, which also supplies the stated two-out-of-three property.
   Retracts of `W` are `[W.IsStableUnderRetracts]`; exact.
3. Every map from the initial object is in `C`, rendered by
   `hcof : ∀ X : A, C (hzero.to X)`; exact.
4. Factorization as a `C` map followed by a `W` map is
   `[HasFactorization C W]`; Mathlib's `HasFactorization` has precisely that order.
5. Pushouts of `C` maps along arbitrary maps exist, rendered by
   `hpush : ∀ (X Y Z : A) (i : X ⟶ Y) (f : X ⟶ Z), C i → HasPushout i f`.
   Stability of the pushout map in `C` and in `C ⊓ W` is rendered by
   `[C.IsStableUnderCobaseChange]` and `[(C ⊓ W).IsStableUnderCobaseChange]`; exact.
6. The finite direct index is `I : Type w` with `[Category.{z} I]`, `[Finite I]`, and
   `[∀ i j : I, Finite (i ⟶ j)]`, matching finitely many objects and morphisms. The degree
   map and strict increase on every nonidentity arrow are `d : I → ℕ` and `hd : IsDirect d`;
   `IsDirect` explicitly permits only transported identities or `d i < d j`.
7. The localization target is `L : SSet.{max u v w z t}` and
   `q : largeNerve.{u,v,max w z t} A ⟶ L`; `hq : IsLocalization.{u,v,max w z t} W q`
   gives the quasicategory and the full coherent-functor universal property for inverting W.
8. The first conclusion is exactly
   `IsLocalization (W.functorCategory I) (comparison I A L q)`, so the natural
   transformations inverted are componentwise W and the comparison is evaluation followed
   by q. The second conclusion is exactly
   `∀ H, ∃ D : I ⥤ A, AreNaturallyEquivalent H (diagram q D)`, retaining the coherent
   natural-equivalence data. The explicit final clause is
   `∀ x : L _⦋0⦌, ∃ X : A, EquivalentObjects L x (object q X)`, matching
   object representability independently of the fixed index I. Empty, singleton, and span indices are all admitted.

I repaired two omissions: the object's explicit representability conclusion was only
mentioned in the docstring, and imports of already-stated proof dependencies were absent.
The final conclusion now includes object representability, including for a fixed empty I;
this is the node's existing clause, not a node correction. I added the proof-only imports
RelativeInfinityCone, EnhancedFunctorConeCalculus, BrownFibrantLocalizationPullbacks,
ParameterConeExtension, and SourceAttachmentGluing. The remaining Brown and approximation
proof nodes currently have no recorded Lean declaration, so cannot yet be imported.
The docstring names all the proof dependencies. I added the existing definition node
`def-coef-coherent-localization-interface` to stmt_deps to record the interface actually used.
The copied lean.statement has been regenerated verbatim from the repaired file.
No other hypothesis, conclusion, index restriction, or extra structure was changed.

For edge cases, `[Finite I]` permits the empty category; `IsDirect` permits a singleton with
constant degree zero; finite hom hypotheses permit parallel arrows; and the span has degrees
`1, 0, 1` as in the source. No nonemptiness, zero-object condition on `I`, coproduct,
fibration, functorial-factorization, model-structure, saturation, characteristic, or universe
equality was introduced. The category and simplicial-set universes remain independent subject
to the displayed maxima.

I searched the project and source checkout with `rg` for Brown finite-direct rectification,
`largeNerve`, and `brown_finite_direct_rectification`; no prior declaration exists. I checked
Mathlib's `MorphismProperty.Factorization`, `Composition`, `Limits`, and `FunctorCategory`
interfaces: `HasFactorization`, `HasTwoOutOfThreeProperty`, cobase-change stability, and
`functorCategory` render exactly the notions used here. The existing
`FiniteReedyLocalization` and `EnhancedDiagramsCones` declarations are the recorded
canonical definitions; no private duplicate was added. The independent LeanSearch/Loogle/
LeanFinder and grep searches recorded in the worker report found no exact Brown rectification
statement. The original and repaired files both compiled cleanly with scompile.py. The repaired module
compiled in 2.0 seconds, after the required BrownFibrantLocalizationPullbacks overlay compiled
in 2.1 seconds. Only the main theorem has a sorry proof.


Independent searches on second reading:

- LeanFinder: "Homotopy coherent diagrams over a finite direct category rectify in a
  cofibration category without a model structure" returned IsCofibrant, CofibrantObject
  and model-category resolution declarations, none an exact theorem.
- Loogle: `"IsLocalization"` returned monoid localizations, none the coherent statement.
- `rg -i 'rectif|finite.{0,20}direct|cofibration category|category of fibrant objects'`
  on Mathlib/AlgebraicTopology, WeilConjectures, and lean/Sheaf/CategoryTheory found
  ordinary model-category homotopy quotients, the stronger finite-Reedy/model-rectification
  theorem, and consumers. None states rectification under these Brown hypotheses alone.

I downloaded and read Cisinski CatLR, Definition 7.1.2, Definition 7.4.12 and
Theorem 7.6.17 (printed pp. 394–395). The definition uses the whole functor category;
Theorem 7.6.17 uses finite direct I and weak equivalences/fibrations and dualizes to the
node. The ordinary all-cofibrant Brown assumptions render its dual exactly as the node
specifies; no saturation hypothesis from the following corollary is needed. The PDF's
printed page 394 is its physical page 410 in this downloaded edition, so the node's
PDF offset is one page early; the numbered theorem and printed pages identify it uniquely.
No new nodes or dependency modules are delivered, and no source-statement correction is needed.


## Worker continuation, 2026-10-17

I rechecked the previous attempt against the current shared node and the full signatures
and docstrings of EnhancedDiagramsCones and FiniteReedyLocalization. The theorem explicitly
includes all three conclusions: the full coherent localization comparison, representation
of every coherent I-diagram by a strict diagram, and representation of every vertex of L.
The last clause is independent of I, so it remains present when I is empty. The universal
property is IsLocalization on the actual curried evaluation comparison, not an arbitrary
existence of an equivalence. The componentwise class is exactly W.functorCategory I.
The object, morphism and indexing universes remain independent through their maxima.

I made the Mathlib imports used by the signature public, as required by the module
conventions, and expanded the theorem docstring to the complete eight-step proof in the
current DAG, including both refinements in conservativity and slice compatibility in
mapping-space lifting. The source PDF retained in the sandbox identifies Theorem 7.6.17
on printed pages 394–395; the docstrings use its actual physical pages 410–411. This is a
bibliographic offset correction only. The node statement and its proof are unchanged.
The record date is 2026-10-17. Only lean and the additional already-landed interface
stmt_dep differ from the shared node; no new node or dependency repair is needed.

Fresh searches used msearch.py LeanFinder with “Every finite direct homotopy coherent
diagram in a Brown cofibration category localization is equivalent to a strict ordinary
diagram”, LeanSearch with “Finite direct diagrams in a Brown cofibration category rectify
in its homotopy coherent localization”, Loogle with
“IsLocalization, functorCategory, largeNerve, comparison”, and grep with
“Brown|finite.direct|rectif” in AlgebraicTopology. LeanFinder and LeanSearch returned
ordinary localization/model-category results. Loogle had no matches (functorCategory
is not indexed there); the grep returned Brown's model-category factorization only.
The source of CofibrantObjectHomotopy was read and is not this coherent statement.
Searches of WeilConjectures, shared lean/Sheaf and dag/lean_names_upstream.json for the
item id and theorem name found no existing statement. No STATEMENT-DISPUTED fault was found.

The recorded proof dependencies currently without Lean modules are
lem-coef-brown-left-fractions, lem-coef-brown-reedy-fibrant-replacement,
lem-coef-brown-right-exact-extension, lem-coef-brown-slice-fraction-calculus and
lem-coef-finite-colimit-approximation. They are proof inputs only and do not prevent
stating this item. Every recorded proof module is imported.

## Second reading by Q77

I read the item node, its Cisinski source place, the dependency node
`def-coef-coherent-localization-interface`, and the declarations in
`FiniteReedyLocalization.lean` and `EnhancedDiagramsCones.lean`. The item-by-item
comparison is:

1. `A : Type u` with `[Category.{v} A]`, `zero : A`, and
   `hzero : IsInitial zero` render the ordinary category and its initial object exactly.
2. `C W : MorphismProperty A`, `hCiso`, `hWiso`, `[C.IsStableUnderComposition]`,
   `[W.HasTwoOutOfThreeProperty]`, and `[W.IsStableUnderRetracts]` render the two
   arrow classes, their isomorphisms, composition, two-out-of-three, and retract closure.
3. `hcof : ∀ X, C (hzero.to X)` is precisely the hypothesis that every map from the
   initial object is in `C`.
4. `[HasFactorization C W]` gives the required `C`-then-`W` factorization.
5. `hpush` gives pushouts of each `C` map along every arrow; the two
   `IsStableUnderCobaseChange` instances give the stated stability for `C` and `C ∩ W`.
6. `I : Type w`, `[Category.{z} I]`, `[Finite I]`, and finite hom types render a
   category with finitely many objects and morphisms. `d : I → ℕ` and `hd : IsDirect d`
   say every nonidentity arrow strictly raises degree.
7. `L`, `q`, and `hq : IsLocalization W q` use the enlarged nerve and the full coherent
   functor universal property from the recorded interface, with independent universes.
8. The first conclusion is localization of strict diagrams at
   `W.functorCategory I` via the canonical `comparison`; the second quantifies every
   coherent `H` and supplies `D : I ⥤ A` with `AreNaturallyEquivalent H (diagram q D)`;
   the final clause represents every vertex of `L` by `object q X`. These are all
   clauses of the node, in the same order and with no stronger or weaker quantifier.

The empty index is admitted by `[Finite I]`; the singleton admits constant degree zero;
the span admits degrees `1, 0, 1`; parallel arrows are covered by finite hom types; and
the object, morphism, index, and simplicial-set universes remain independent. No
nonemptiness, coproduct, fibration, functorial-factorization, model-structure, saturation,
characteristic, or universe-equality assumption appears.

I searched the source and project with `rg`, checked the Mathlib/source declarations,
and ran independent LeanFinder, LeanSearch, Loogle, and grep searches recorded above.
There is no existing Brown finite-direct rectification declaration. The localization,
nerve, comparison, `IsDirect`, diagram, object, and coherent-equivalence notions are the
recorded declarations; no private duplicate is present. The previous reading's repair
adding the explicit object clause and the localization-interface statement dependency is
consistent with the node and remains in the copied node. No mismatch was found in this
reading, so no further source or Lean changes were needed.
