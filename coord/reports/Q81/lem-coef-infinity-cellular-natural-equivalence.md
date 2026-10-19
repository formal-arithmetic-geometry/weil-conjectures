## Worker report

The module `Sheaf.AlgebraicTopology.CellularNaturalEquivalence` states
`SSet.Enhanced.cellular_natural_equivalence`. Its sole proof is `sorry`; it introduces
no definition, auxiliary theorem, extra node, or dependency repair. The node copy
changes only `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The input fixed universe is `u`, with simplicial sets `SSet.{u}`. The independent
  test universe is `max u v`, where `v` is arbitrary. The degreewise lift
  `SSet.uliftFunctor.{v, u}` transports every component map to this test universe.
  Thus test quasicategories are never forced to live below the input universe.
- The ordinary functors and ordinary natural transformation are
  `(P Q : SSet.{u} ⥤ SSet.{u}) (η : P ⟶ Q)`. These are ordinary category-theoretic
  functors and a Mathlib natural transformation, not coherent functors with
  additional data or assumptions.
- `hPMono` and `hQMono` quantify over every simplicial map `f : X ⟶ Y` and require
  injectivity of `(P.map f).app (Opposite.op ⦋n⦌)` and the corresponding `Q` map
  for every `n : ℕ`, provided `f.app (Opposite.op ⦋n⦌)` is injective in every degree.
  This is exactly the degreewise-injection condition, including degree zero.
- `hPConnected` and `hQConnected` quantify over all `J : Type u` with
  `[SmallCategory J] [CategoryTheory.IsConnected J]`, and require
  `PreservesColimitsOfShape J P` and `PreservesColimitsOfShape J Q`.
  Mathlib's `IsConnected` explicitly includes `Nonempty J` and is equivalent to
  connectedness by undirected zigzags. `PreservesColimitsOfShape` quantifies over
  every diagram and sends each colimit cocone to a colimit cocone. In simplicial
  sets these colimits exist, and this is equivalent to the canonical comparison
  from the colimit of the image diagram to the image colimit being an isomorphism.
  No preservation of empty or disconnected colimits is assumed.
- The categorical-equivalence test is expanded in place using
  `IsFunctorEquivalence ((MonoidalClosed.pre (SSet.uliftFunctor.map f)).app E)`.
  Here `E : SSet.{max u v}` and `[E.Quasicategory]` range over every test
  quasicategory in that containing universe. `MonoidalClosed.pre` is the actual
  precomposition map from `Fun(Y,E)` to `Fun(X,E)`; `IsFunctorEquivalence` has the
  quasi-inverse and coherent natural equivalences from the dependency node.
  This tests the whole internal functor quasicategory, not just its vertices,
  its ordinary homotopy category, or a separately selected map on cores.
- `hEmpty` applies that test to `η.app (⊥_ SSet.{u})`. The initial object of the
  simplicial presheaf category is the empty simplicial set, degree by degree.
  Neither `P` nor `Q` is assumed to preserve this initial object.
- `hSimplex` applies the same test to `η.app Δ[n]` for every `n : ℕ`. This includes
  the zero-simplex; natural numbers encode exactly the integers at least zero.
- The conclusion takes arbitrary `(K : SSet.{u}) (E : SSet.{max u v})
  [E.Quasicategory]` and applies the identical test to `η.app K`. Universal
  quantification over the displayed final binders gives every small input and
  every test quasicategory in the arbitrary containing universe.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence`, whose signature is
  `{C D : SSet.{u}} (f : C ⟶ D) : Prop`, with an existential quasi-inverse and
  two `AreNaturallyEquivalent` clauses. I read both full definitions and their
  docstrings, and `AreNaturallyEquivalent`'s `diagramVertex` and
  `IsEquivalenceEdge` definitions. These supply exactly the coherent equivalence
  convention of `def-cbc-enhanced-diagrams-cones`; the primary recorded
  `coneCategory` declaration is not relevant to this node's statement.
- The same dependency imports Mathlib's standard simplex, internal hom and
  quasicategory definitions. The statement uses `Δ[n]`,
  `SSet.uliftFunctor`, `MonoidalClosed.pre`, and `E.Quasicategory` directly.
- `Mathlib.CategoryTheory.IsConnected`: `CategoryTheory.IsConnected`, with the
  nonempty convention and zigzag characterization documented in that module.
- `Mathlib.CategoryTheory.Limits.Preserves.Basic`:
  `CategoryTheory.Limits.PreservesColimitsOfShape`, read together with
  `PreservesColimit` (the mapped-colimit-cocone definition).
- `Mathlib.CategoryTheory.Limits.Shapes.Terminal`:
  `CategoryTheory.Limits.initial` and notation `⊥_`, used for the empty input.

Edge cases checked before drafting:

- `K` empty is allowed and is exactly covered by `hEmpty`; no nonempty input
  hypothesis occurs. Empty test quasicategories are allowed too.
- `n = 0` is included. Arbitrarily many disconnected components and isolated
  vertices are allowed in `K`. No assumption that the functors preserve arbitrary
  coproducts or the initial object has been added.
- Empty indexing categories are excluded only from the connected-colimit
  hypotheses, precisely as the node specifies. Singleton categories, connected
  spans, wide pushouts, and nonempty sequential chains are included.
- The identity natural transformation and constant functors satisfy the expected
  special cases. In particular a constant functor with noninitial value can
  preserve connected colimits and injections, so replacing connected-colimit
  preservation by preservation of all colimits would be a real strengthening;
  the statement does not do that.
- The case of arbitrary larger test universes is retained by explicit `max u v`
  and degreewise lifting; neither site nor coefficient universes are involved.

Searches made (through the prescribed search wrapper unless specified otherwise):

- LeanFinder query: "A natural transformation of simplicial set functors preserving
  monomorphisms and connected colimits is a categorical equivalence on every
  simplicial set if it is on empty set and standard simplices"; repeated as
  "Cellular criterion: natural categorical equivalences between simplicial set
  endofunctors preserving monomorphisms and connected colimits are tested on empty
  set and standard simplices". The inspected results include the Quillen
  generating boundary/horn maps, stability of monomorphisms under filtered
  colimits, balancedness, and skeleton calculations. None is this theorem.
- Loogle query: `"SSet", "Equivalence"`: nine hits, including
  `SSet.opEquivalence`, truncated homotopy-category/fundamental-groupoid
  equivalences and `isEquivalence_mapFundamentalGroupoid`. None tests arbitrary
  natural transformations by simplices.
- Mathlib grep query: `categoricalEquivalence|categorical.equivalence|connected.*colimit`
  in `AlgebraicTopology`: one hit, the equivalence of augmented simplicial and
  cosimplicial objects in `SimplicialObject/Basic.lean`, unrelated to this theorem.
- LeanSearch with the first LeanFinder query: eight hits, including the Quillen
  cofibration characterization, Yoneda, and `NatTrans.mono_iff_mono_app`; these
  provide primitives but not the cellular test.
- Direct `rg` in the upstream `WeilConjectures/` tree for the item id and for
  `IsCategoricalEquivalence|cellular_natural|cellular.*equiv|categoricalEquivalence`:
  no matching declaration. A search of `dag/lean_names_upstream.json` for the id
  also returned no match.
- Direct `rg` in project `lean/Sheaf` found
  `CategoryTheory.CoherentNerve.IsCategoricalEquivalence` in
  `Sheaf.CategoryTheory.CoherentNerveInfrastructure`: this is a mapping-on-cores
  weak-homotopy-equivalence test, not the whole-functor-category test stated here.
  It does not state the cellular theorem. The current statement expands the
  existing internal functor equivalence test without creating another predicate.
  `BluntJoinComparison.lean` cites this node in its proof docstring, but does not
  already declare its general statement.
- Direct `rg` for `cellular_natural_equivalence` over Mathlib, upstream
  `WeilConjectures`, and project `lean/Sheaf`: no existing declaration.

Source check: opened the cited Cisinski PDF (July 30, 2026 revision), especially
Proposition 4.2.3 on printed p. 145 and Corollary 1.3.10. The former explicitly
uses preservation of connected colimits and monomorphisms to make the class of
inputs with equivalence components saturated by monomorphisms, and then reduces
to standard simplices. The proof docstring records this argument and explains the
empty-input/coproduct step. No source-based statement correction is necessary.

Node metadata observation: the supplied node currently has `status: "unsplit"`
and an empty `proof` list, despite the dispatcher assigning stage 2. I preserved
those fields as required; the theorem docstring supplies the complete natural
language cellular proof plan for the postponed theorem. No false-statement or
missing-dependency fault was found.

Validation: `scompile.py Q81 lem-coef-infinity-cellular-natural-equivalence` on the
single delivered module returned success for both the sandbox and library-name
checks (1.3 s and 1.4 s), with no errors or warnings. All declaration binders and
universes are explicit, `autoImplicit` is disabled, and every source line is at
most 100 characters. The only postponed theorem is
`SSet.Enhanced.cellular_natural_equivalence`.

## Second reading by Q81

I independently read the current node, the delivered Lean signature and both
source docstrings, the entire recorded dependency module
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, and the relevant Mathlib
interfaces. The statement is faithful: no mathematical signature repair or
`statement_change` is necessary. There are no new definition nodes, dependency
modules, helper definitions or auxiliary postponed theorems to review.

Source: I opened [Cisinski, Higher Categories and Homotopical
Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf), revision July 30,
2026, specifically Proposition 4.2.3 and its preceding definitions on printed
pp. 144–145, Theorem 1.3.8, Definition 1.3.9 and Corollary 1.3.10 on pp. 11–13,
Theorem 3.6.8 on pp. 115–116, and Corollary 3.9.8 on pp. 134–135. This source
is a PDF, not a Stacks result; there is no corresponding Stacks .tex source
place. The general criterion is explicitly agent-formulated in the node.
Proposition 4.2.3's reduction uses preservation of monomorphisms and connected
colimits, with the empty-input comparison handled separately. It assumes no
finiteness or quasicategory condition on the input simplicial sets. Theorem
3.6.8 confirms that the full internal-functor equivalence test is the intended
categorical-equivalence condition. No background source hypothesis is missing.

My object/hypothesis/conclusion checklist, made from the node before matching
its Lean, is as follows. Each entry passes.

1. Objects: small simplicial sets in a fixed universe, standard simplices,
   arbitrary testing quasicategories in a containing universe. Lean uses
   `SSet.{u}`, `Δ[n]`, `(E : SSet.{max u v}) [E.Quasicategory]`, with both
   universe parameters explicitly declared. `SSet.uliftFunctor.{v, u}` lifts
   only the component map to the test universe, degree by degree. It does not
   restrict the sizes of inputs or equate the two universes.
2. Objects: ordinary endofunctors P,Q and an ordinary natural transformation.
   Lean has `(P Q : SSet.{u} ⥤ SSet.{u}) (η : P ⟶ Q)`; no enriched-functor
   structure or additional coherence hypothesis is imposed.
3. Hypothesis: P preserves every degreewise injection. `hPMono` quantifies over
   every `X`, `Y`, simplicial map `f`, and degree `n : ℕ`; it takes injectivity
   of every `f.app (Opposite.op ⦋n⦌)` to injectivity of every component of
   `P.map f`. There is no stronger hypothesis on the input map.
4. Hypothesis: Q preserves every degreewise injection. `hQMono` is exactly the
   same condition for `Q.map f`, with the same quantifiers.
5. Hypothesis: P preserves all small connected colimits. `hPConnected` ranges
   over `(J : Type u) [SmallCategory J] [CategoryTheory.IsConnected J]` and
   asserts `PreservesColimitsOfShape J P`. I read `IsConnected` at Mathlib
   `CategoryTheory/IsConnected.lean:64–78` and its zigzag converse at
   lines 443–464: connectedness includes nonemptiness and is precisely the
   undirected-zigzag condition. I read `PreservesColimit` and
   `PreservesColimitsOfShape` at `Limits/Preserves/Basic.lean:58–73`: all diagrams
   and all colimit cocones are included. Since simplicial sets have these
   small colimits, this is equivalent to the node's canonical comparison
   being an isomorphism. Both indexing universes are the fixed small universe;
   no independent smaller index universe makes this hypothesis vacuous.
6. Hypothesis: Q preserves those same connected colimits. `hQConnected` states
   the identical condition for Q. Neither binder requires preservation of
   empty-index or disconnected colimits.
7. Convention: categorical equivalence tests the specified precomposition map
   on whole internal functor quasicategories, with a quasi-inverse and coherent
   natural inverse equivalences. Lean expands the test as
   `IsFunctorEquivalence ((MonoidalClosed.pre
   (SSet.uliftFunctor.{v, u}.map f)).app E)`. I read `MonoidalClosed.pre` and its
   `uncurry_pre_app` characterization in Mathlib
   `CategoryTheory/Monoidal/Closed/Basic.lean:244–273`: this really is
   precomposition, with source Fun(target(f),E) and target Fun(source(f),E).
   I read `SSet.Enhanced.IsFunctorEquivalence`, `AreNaturallyEquivalent`,
   `diagramVertex` and `IsEquivalenceEdge` in the dependency module. Its
   existential inverse and its two equivalence edges give exactly the node's
   convention, retaining all higher simplices. The primary recorded
   `coneCategory` declaration is not mistaken for this auxiliary declaration
   of the same recorded module. No separate categorical-equivalence predicate
   is introduced here.
8. Hypothesis: the empty component is a categorical equivalence. `hEmpty`
   applies that exact test to `η.app (⊥_ SSet.{u})`, for every displayed test E.
   The presheaf initial object is the empty simplicial set in every degree;
   P(empty) and Q(empty) need not themselves be empty.
9. Hypothesis: the simplex components are categorical equivalences for every
   n ≥ 0. `hSimplex` applies the same test to `η.app Δ[n]`, with `n : ℕ` before
   E. This includes n = 0 and all higher dimensions, with no boundedness.
10. Conclusion: for every small input K, its specified component is a
    categorical equivalence. The final binders `(K : SSet.{u})
    (E : SSet.{max u v}) [E.Quasicategory]` assert the identical test for
    `η.app K`, in that order. The arbitrary universe v permits every containing
    test universe; no test is replaced by a condition only on vertices, cores,
    or the ordinary homotopy category. There are no extra conjuncts.

Edge cases: the empty input is allowed and is exactly the separate `hEmpty`
case. Empty testing quasicategories are allowed by Mathlib's inner-horn-only
quasicategory condition. Degree zero is included in both injection hypotheses
and the simplex hypothesis. Empty indexing categories are excluded only from
connected-colimit preservation, as required; singleton and nonempty filtered
indexing categories are included. Arbitrary disconnected and infinitely large
small inputs are allowed. Constant endofunctors with nonempty constant value
explain why requiring preservation of all colimits would be stronger; the
Lean correctly makes no such requirement. Identity natural transformations
are covered. No ring, characteristic, scheme or zero-object hypothesis is
applicable. The category of simplicial sets has no zero object, so the relevant
edge case is the empty simplicial set, already included.

Independent H4 searches (all through the prescribed msearch wrapper, plus
local rg; results are in `searches.jsonl`):

- LeanFinder: "Simplicial set endofunctors preserve connected colimits and
  injections, equivalence of natural transformation detected at representable
  simplices and initial object". Eight hits, including `SSet.cosk`, Yoneda,
  finite presentability and nerve fully-faithfulness; none states this criterion.
- Loogle: `SSet, PreservesColimitsOfShape` returned unknown identifier, so this
  attempt is inconclusive. The corrected query `"SSet", "equivalence"`
  returned nine opposite/truncated homotopy-category/fundamental-groupoid
  equivalences; none is this theorem.
- LeanSearch: "A componentwise categorical equivalence of natural
  transformations on all simplicial sets can be checked on standard simplices
  for functors preserving injections and connected colimits". Eight hits,
  chiefly `SSet.hom_ext`, Yoneda and component formulas; none is the theorem.
- Mathlib grep: `cellular|saturated|connected.*colimit` in AlgebraicTopology
  returned no hit. The broader `cellular|saturated.*mono|preserv.*connected`
  search returned unrelated CW-complex, saturation and Galois connectedness
  declarations.
- Independent rg over upstream `WeilConjectures`, project `lean/Sheaf`, and
  Mathlib AlgebraicTopology for cellular/natural-equivalence and connected
  colimit formulations found no existing general criterion. The project
  `BluntJoinComparison.lean` cites this node but does not declare its theorem.
  I opened `CategoryTheory.CoherentNerve.IsCategoricalEquivalence` at
  `CoherentNerveInfrastructure.lean:105`: its expression tests the induced map
  of cores, rather than this whole-Fun condition, and is not the desired
  cellular theorem. I also opened Mathlib
  `CategoryTheory.hoFunctor.isIso_prodComparison_of_stdSimplex` in
  `NerveAdjunction.lean:450–458`; it tests a particular product comparison
  for an ordinary categorical isomorphism, not the general criterion here.
  Neither justifies dropping this module. Searching `dag/lean_names_upstream.json`
  and upstream/project sources for the delivered declaration/module name found
  no duplicate.

Mismatches and repairs: the mathematical signature is correct and was preserved
verbatim. The worker report's last metadata paragraph is stale: the supplied
node copy and current shared node already agree outside `lean`, and both have
`status: split`, six proof steps and four proof dependencies. The old theorem
docstring did not reproduce that current proof. I replaced only its proof plan
with all six current node steps, including the explicit finite span-factorization
argument, filtered limit step, refinement to individual boundary-cell
attachments, dimension induction and final omega-skeleton argument. I updated
the source citations in the module and theorem docstrings accordingly. I added
`import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` as a non-public proof
import for `lem-coef-infinity-monomorphism-boundary-cells`, whose exact
`SSet.relativeCellComplexOfMono` declaration I read at lines 428–446. The other
three proof dependencies have no recorded Lean declaration yet, so there is
no corresponding module to import. No node statement, proof, dependency list,
target or definition was changed. The node's lean date was refreshed.

For additional consumer sanity, I read the citing steps in
`lem-coef-infinity-blunt-join-comparison` and
`lem-coef-infinity-blunt-sharp-join-equivalence`. Both supply injection and
connected-colimit preservation, the empty component and every simplex
component, and use the full-Fun conclusion. Both uses remain valid; the
statement itself needed no correction and no formal citer audit is triggered.

H5/H6/H8/H9 checks: one theorem with one `sorry`, no definitions or proved
auxiliaries; both source/blueprint docstrings present; full current proof plan
present; no private declarations, local notation, local instances, hidden let
binders or unbound variables. All lines are at most 100 characters. The node's
`lean.statement` is byte-for-byte the displayed signature before `:= by`.
`scompile.py Q81 lem-coef-infinity-cellular-natural-equivalence
lean/Sheaf/AlgebraicTopology/CellularNaturalEquivalence.lean` passed sandbox and
library-name compilation (1.6 s and 1.9 s), with no warnings or errors.
