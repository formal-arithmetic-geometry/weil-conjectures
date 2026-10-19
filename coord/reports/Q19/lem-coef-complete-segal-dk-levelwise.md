## Worker report

The module `lean/Sheaf/CategoryTheory/CompleteSegalDKLevelwise.lean` states
`CategoryTheory.SegalSpace.completeSegal_dk_iff_levelwise`. It contains one theorem,
whose entire proof is `sorry`, with the node's nine-step natural-language proof in
its source/blueprint docstring. It introduces no definition or additional theorem.
The mathematical assertion is unchanged; the representation clarification and proof-route
correction are recorded under `## Statement corrected` below.

Source read: Rezk, *A model for the homotopy theory of homotopy theory*, Sections
5.1--5.8, Section 6, Proposition 6.4, Corollary 6.5, Section 7.4 and Proposition
7.6, printed pp. 11--17. The PDF and extracted text from the earlier attempt remain
in the sandbox. Proposition 7.6 identifies DK equivalences of complete Segal spaces
with Reedy weak equivalences. Under the mapping-space condition, the induced
homotopy-category functor is fully faithful, so essential surjectivity is precisely
the remaining categorical condition in Section 7.4.

Hypotheses and clauses, matched individually:

- A simplicial space is `Space.{u}` from the published `def-coef-segal-space`:
  a functor on the product of the outer and inner opposite simplex categories.
  Mathlib's `Functor.currying` identifies this with the node's functor
  `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. `Functor.curry.obj` and `Functor.curry.map`
  retain the given objects and arrows in every bidegree. This is a representation
  equivalence, with no mathematical restriction. The one arbitrary universe `u`
  covers small simplicial sets; `U`, `V`, `f` and all variables are explicitly bound.
- `f : U ⟶ V` is the given natural transformation in both simplicial directions.
- `hU : IsComplete U` and `hV : IsComplete V` each include `IsSegal`.
  `IsSegal` includes the actual opposite-injective Reedy matching maps being Kan
  fibrations and requires weak equivalences of the consecutive-edge `segalMap`
  for every `2 ≤ n`. Its target `chains W n` consists of composable strings,
  exactly the strict consecutive-edge products over `W₀`.
- The mapping spaces are the existing `mappingSpace W x y`, the strict pullbacks
  of `endpoints W = (d₁,d₀)` along the constant vertex pair `(x,y)`.
  `mappingSpaceMap f x y` is the actual pullback map induced by `f₁` and `f₀`.
  No right-pinched mapping space or arbitrary replacement is substituted.
- The homotopy category has the vertices of `row W ⦋0⦌` as objects and components
  of these strict fibers as hom sets. The dependency expresses isomorphisms by
  `IsEquivalenceArrow`: an inverse edge, two outer triangles for the two composites,
  and equality of their long-edge components with the identity components in the
  specified endomorphism fibers. This is exactly invertibility for composition
  induced by the degree-two Segal map and `d₁`; identities are `s₀`.
- `equivalenceArrows W` is the existing full subcomplex on components containing
  such an invertible arrow, so it is the node's `W_eq`.
- The remaining clause of `IsComplete W` requires a factor `s` of the actual
  degeneracy with `s ≫ (equivalenceArrows W).ι = s₀` and requires that `s` be a
  weak homotopy equivalence. The inclusion is monic, so the factor is unique;
  this existential formulation adds no arbitrary choice and defines no data.
- The theorem's left side is `∀ n : ℕ, SSet.Enhanced.IsWeakHomotopyEquivalence
  ((Functor.curry.map f).app (op ⦋n⦌))`. These are precisely the outer level maps,
  including degrees zero and one.
- The first right-side clause quantifies all vertices `x,y` of `row U ⦋0⦌` and
  requires weak equivalence of `mappingSpaceMap f x y`.
- The second right-side clause is the published `IsEssentiallySurjective f`.
  Unfolding it, every target vertex `z` admits a source vertex `x` and an
  equivalence arrow with source `f(x)` and target `z`. Its inverse and both inverse
  equations say exactly that `z` is isomorphic to `f(x)` in `hV`, rather than just
  admitting an arrow from it. For Segal spaces every homotopy-category morphism
  is represented by an edge, so this does not strengthen essential surjectivity.
- Every weak equivalence is the recorded `SSet.Enhanced.IsWeakHomotopyEquivalence`:
  realization induces a bijection on path components and on all positive based
  homotopy groups at all basepoints. No connectedness, discreteness, nonemptiness,
  vertex bijection, or additional fibrancy hypothesis is imposed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and `fullSubcomplex`. Read their full
  signatures, data and docstrings, and the node's recorded `coneCategory` signature.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, including its fixed fibration class,
  and the realization-based `weakEquivalenceStructure`. Read the full theorem
  signature and proof docstring. The Segal dependency uses the horn RLP directly.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.matchingFrom` and `model_structure`. Read their full
  signatures and docstrings, including the ground category and universe binders.
- `Sheaf.CategoryTheory.SegalSpace`: read its entire module and owning node
  `def-coef-segal-space`. Used `Space`, `row`, `endpoints`, `mappingSpace`,
  `mappingSpaceMap`, `chains`, `segalMap`, `IsReedyFibrant`, `IsSegal`,
  `SameMappingComponent`, `IsEquivalenceArrow`, `equivalenceArrows`, `IsComplete`
  and `IsEssentiallySurjective`. The existing owning node is added to `stmt_deps`
  under brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). Its dependencies are
  exactly the original three prerequisites, so this creates no dependency cycle.
- Mathlib `CategoryTheory.Functor.Currying`: `Functor.curry`, `Functor.currying`,
  and its strict curry/uncurry identities; read the signatures and definitions.

The available proof-only modules are imported without `public`, as the stage
requires: strict/path pullback comparison, path-fibration replacement, homotopy-fiber
detection, Kan realization comparison, realization of finite limits, path-boundary
bijections, basepoint change, and homotopy-pullback invariance. The arbitrary-base
fiber criterion was deliberately removed from the repaired route to break the recorded
DAG cycle; the degree-zero argument now uses the completeness path zigzag directly. The proof-only nodes `lem-coef-segal-homotopy-category-components` and
`lem-coef-sset-anodyne-pushout-product` have no recorded module on the snapshot;
there is no import for them. Neither is needed to elaborate the statement.

Edge cases checked mathematically before finalizing: empty-to-empty satisfies both
sides with vacuous vertex conditions; empty-to-nonempty fails essential surjectivity
and the degree-zero component bijection. Empty mapping fibers remain allowed.
Discrete nerves of sets detect bijections; the nerve of `[1]` shows why an arrow
cannot replace an isomorphism. A nontrivial group nerve has invertible nonidentity
arrows and is not complete merely because it is Segal. The quantifier includes
`n=0,1`; the Segal condition begins at `n=2`. Currying preserves each of these cases.

Searches and results:

- `msearch.py leanfinder`: “A map between complete Segal spaces is a levelwise weak
  equivalence if and only if it is fully faithful on mapping spaces and essentially
  surjective”. Eight hits about nerves and fully faithful functors; no DK criterion
  for complete Segal spaces.
- `msearch.py loogle`: `"Segal", "Equiv"`. Four strict-Segal spine and truncated-nerve
  results; no complete-Segal criterion.
- `msearch.py grep`: `IsCompleteSegal|completeSegal|mappingFiber|SegalSpace`, Mathlib
  `AlgebraicTopology`: no hits.
- `rg` on upstream `WeilConjectures` for complete-Segal terminology and the item id:
  no declaration. The upstream declaration-name table has only unrelated
  exact-couple completeness predicates.
- Broader `rg` on project `lean/Sheaf` for `Segal|mappingFiber` located both the
  published `SSet.Segal` interfaces and `CategoryTheory.SegalSpace`. Reading the
  latter and its owning `def-coef-segal-space` node found exactly the required
  completeness and essential-surjectivity definitions. They are reused wholesale.
  No existing theorem there states Proposition 7.6. The homotopy-Segal diagonal
  theorem is a different conclusion under different hypotheses.

The continuation audit found that the saved attempt duplicated completeness despite
this published definition node and also exposed a cyclic arbitrary-base fiber dependency;
the repaired route removes that theorem from step 7. That duplication and its factorization helper theorem
have been removed. The final module uses the canonical published Segal definitions
and requires just the single criterion theorem. There is no statement dispute, new DAG node, or replacement dependency module.
The source-faithful clarification and proof correction are recorded below.

Validation: `scompile.py` compiled the final module in sandbox and library-path
checks cleanly (2.1 s and 2.2 s), with no errors or warnings. The sole `sorry` is the
criterion theorem. Its recorded signature matches the file verbatim, all Lean lines
are at most 100 characters, and all variables and universes are explicitly bound.
The prescribed `deliver2.py --no-push` performs the delivery dry run.
The independent second reading is left to the next worker; nothing is pushed here.

## Earlier second reading (a previous round; superseded)

Node statement read as a list and matched against
`CategoryTheory.SegalSpace.completeSegal_dk_iff_levelwise`:

- The objects are small simplicial spaces `U` and `V`, represented by
  `Space.{u} = SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u`. `Functor.curry` identifies
  this with a simplicial object in simplicial sets; the level map in outer degree `n` is
  `((Functor.curry.map f).app (op ⦋n⦌))`. Verdict: same bisimplicial object and same map,
  with one universe `u` and no restriction on the simplicial-set size beyond the node's
  smallness convention.
- The map is `f : U ⟶ V`. Verdict: present exactly once and used to induce all level and
  mapping-fibre maps.
- The hypotheses are completeness of both spaces. Lean has
  `hU : IsComplete U` and `hV : IsComplete V`; the canonical definition expands to
  `IsSegal` (Reedy fibrant plus weak-equivalence Segal maps for every `n ≥ 2`) and a weak
  equivalence factor of the actual `s₀` through `equivalenceArrows`. Verdict: exactly the
  source's complete Segal hypotheses; no extra fibrancy, nonemptiness, connectedness,
  characteristic, or finiteness assumption.
- `M_W(x,y)` is the strict fibre of `(d₁,d₀)` over vertices `(x,y)`. Lean's
  `mappingSpace W x y` is precisely that pullback, and `mappingSpaceMap f x y` is its
  canonical induced map. Verdict: exact object and variance.
- The first conclusion clause quantifies every `x,y` in `U₀` and requires the induced
  mapping-space map to be `SSet.Enhanced.IsWeakHomotopyEquivalence`. Lean's
  `∀ x y : (row U ⦋0⦌) _⦋0⦌, ...` is exactly that quantifier and predicate.
- The second conclusion clause is essential surjectivity on the homotopy category.
  Lean's `IsEssentiallySurjective f` quantifies every target vertex and supplies a source
  vertex plus an `IsEquivalenceArrow` from its image to that target, matching the source's
  isomorphism condition.
- The left conclusion clause quantifies all `n : ℕ`, including `n = 0` and `n = 1`, and
  requires weak equivalence of every outer level. This is the source's Reedy weak
  equivalence because the recorded Reedy model structure has objectwise weak
  equivalences. Verdict: no degree omitted or added.
- The connective and quantifier order is the source's “if and only if” between levelwise
  equivalence and (fully faithful mapping spaces ∧ essential surjectivity). Verdict: exact.

Source check: Rezk, Proposition 7.6 (printed pp. 16--17), with §7.4 and Proposition 6.4.
The proposition states that a map of complete Segal spaces is a Dwyer--Kan equivalence iff
it is a Reedy weak equivalence; §7.4 defines the former by mapping-space weak equivalences
and equivalence of homotopy categories, with essential surjectivity expressible by
isomorphism classes. The Lean statement renders these clauses through the canonical Segal
definitions and the published strict mapping fibres.

Edge cases checked: `U₀` or `V₀` empty (the universal mapping clause is vacuous and
essential surjectivity has the expected truth value), empty-to-nonempty maps, `n = 0` and
`n = 1`, empty mapping fibres, discrete nerves (detecting bijections), a nontrivial
groupoid nerve (invertible nonidentity arrows), and arbitrary universe `u`. No zero-object,
characteristic, or nonemptiness hypothesis occurs in the source or Lean.

Searches repeated: `msearch.py` LeanFinder for “complete Segal space Dwyer Kan equivalence
levelwise weak equivalence”, Loogle for `CategoryTheory.SegalSpace.IsComplete`, grep for
`completeSegal_dk_iff_levelwise|Dwyer.Kan|IsEssentiallySurjective|mappingSpaceMap` in
Mathlib/AlgebraicTopology, and `rg` over the project and slopmaster2 sources. These found
no existing theorem matching the criterion. The only matching project definitions are the
canonical declarations in `Sheaf.CategoryTheory.SegalSpace`, which this module imports;
there is no duplicate definition.

Dependency audit: `EnhancedDiagramsCones`, `KanQuillenRightProper`, `ReedyModelStructure`,
and `SegalSpace` were read at their recorded declarations. Currying is Mathlib's strict
`Functor.curry`, so no private representation or universe coercion is introduced. The
proof-only imports are used only to expose the node's planned proof route.

Mismatches found: none. No file, statement, dependency, or definition was changed in this
second reading. The node copy's `lean.statement` remains verbatim equal to the theorem
signature. Validation with `scompile.py` succeeded for the sandbox and library-path checks
with no errors or warnings; the only postponed proof is the named criterion theorem.

## Statement corrected

The returned packet exposed a dependency cycle: the item’s recorded proof route used
`lem-coef-kan-fibration-arbitrary-base-fibers`, whose statement dependencies reach
`lem-coef-segal-dk-diagonal-equivalence`, and that theorem uses this item. The source
statement was clarified by explicitly identifying a simplicial space with the strictly
curried bisimplicial representation used by `Space`; this does not add a mathematical
hypothesis or change any conclusion. The proof route was repaired by removing the
arbitrary-base fiber criterion from step 7. The mapping-space equivalence on
`E_U(x,x) -> E_V(fx,fx)` and the completeness zigzag directly give the loop-space
map, after which step 8 proves degree zero and step 9 uses the already available
homotopy-fiber detection theorem for degree one. The only citer is
`lem-coef-segal-dk-diagonal-equivalence` (holds: its use of the criterion theorem is
unchanged). The old proof and proof-dependency lists are recorded verbatim in the
node’s `statement_change` record.


## Second reading by Q19

I read the corrected node against Rezk first, then read the Lean theorem and the full
published `SegalSpace` module. Rezk §§2.1--2.4 use simplicial sets as spaces and
simplicial objects therein as simplicial spaces; §4.1 assumes Reedy fibrancy and the
consecutive-edge weak equivalences; §§5.1, 5.3, 5.5 and 5.7 define the mapping spaces,
composition, invertibility and equivalence-arrow components; §6 defines completeness.
Proposition 7.6, with §7.4, is exactly the asserted criterion. There is no Stacks source
for this node. I read the saved PDF extraction at those sections and Proposition 6.4,
Corollary 6.5 and Proposition 7.6 (printed pp. 14--17).

The node's objects, hypotheses and conclusion clauses, with their Lean counterparts:

- Small simplicial spaces `U,V`: `{U V : Space.{u}}`, where the published `Space`
  is the functor category on the product of the two opposite simplex categories.
  I read Mathlib `Functor.curryObj`, `Functor.curry` and `Functor.currying`: the
  curried objects and arrows are the same bidegree data, and curry/uncurry are inverse
  equivalences. Verdict: precisely the node's simplicial objects in simplicial sets.
- The specified map `f:U→V`: `(f : U ⟶ V)`. The conclusion uses that same natural
  transformation for both level maps and strict-fiber maps. Verdict: exact.
- Both spaces are complete Segal spaces: `hU : IsComplete U`, `hV : IsComplete V`.
  `IsComplete` contains `IsSegal`, which contains the actual Reedy matching-map horn
  RLP and `∀ n, 2 ≤ n → IsWeakHomotopyEquivalence (segalMap W n)`.
  `IsReedyFibrant` uses the opposite-monomorphism negative simplex subcategory;
  `chains` uses `SSet.Path` and `segalMap` the actual spine restriction. Verdict:
  the specified matching fibrancy and consecutive-edge products, with no stronger
  fibrancy or discrete-object assumption.
- Strict mapping spaces at vertices `(x,y)`: the dependency's `mappingSpace W x y`
  is `pullback (endpoints W) (SSet.const (x,y))`; `endpoints` orders its faces as
  `(δ 1,δ 0)`. `mappingSpaceMap f x y` is `pullback.map` with the curried `f₁`,
  identity on the point, and `f₀ × f₀`. Verdict: the same strict fiber and canonical
  induced map, with the correct source/target order.
- Homotopy-category isomorphisms: `SameMappingComponent` uses equality in `SSet.π₀`
  of the strict fibers. `IsEquivalenceArrow` requires one inverse edge and two
  degree-two simplices with the two composite classes equal to the appropriate
  `s₀` classes. Rezk's degree-two Segal map is a trivial fibration, so inverse
  classes can be represented by exactly these triangles. Verdict: exactly
  invertibility in the category defined in §§5.3--5.5, not merely an arrow.
- The union `W_eq`: `equivalenceArrows W` uses the existing `fullSubcomplex` on
  components containing `IsEquivalenceArrow` vertices. I checked `fullSubcomplex`
  retains precisely simplices all of whose vertices satisfy its predicate; here
  the predicate is component invariant. Verdict: the node's union of components.
- Completeness via the actual `s₀`: the rest of `IsComplete` is an existential map
  into that subcomplex, with composite equal to the actual outer degeneracy and
  with `IsWeakHomotopyEquivalence`. The subcomplex inclusion is monic, hence the
  factor is unique. Verdict: this is the specified degeneracy, not an arbitrary
  weak equivalence or a chosen hollow object.
- Levelwise weak equivalence in every degree: the left side is
  `∀ n : ℕ, IsWeakHomotopyEquivalence ((Functor.curry.map f).app (op ⦋n⦌))`.
  Verdict: the exact outer-level maps, including zero and one.
- Fully faithful mapping spaces: the first right-hand conjunct quantifies
  `∀ x y : (row U ⦋0⦌) _⦋0⦌` and asserts weak equivalence of
  `mappingSpaceMap f x y`. Verdict: all pairs of source vertices, as required.
- Essential surjectivity: the second conjunct `IsEssentiallySurjective f` unfolds
  to every target vertex `z` admitting a source vertex `x` and an equivalence edge
  from `f(x)` to `z`. Every homotopy-category morphism has an edge representative.
  Verdict: precisely the node's isomorphism-to-an-image clause. The mapping-space
  weak equivalences already give full faithfulness on components, so this is
  equivalent to the homotopy-category equivalence in Rezk §7.4.
- The iff and conjunction order are unchanged. `Enhanced.IsWeakHomotopyEquivalence`
  uses bijections on realized path components and on every positive based homotopy
  group at every source basepoint. Verdict: every weak equivalence in the node
  has the recorded realization-based meaning.

Dependency review: I opened the four statement-dependency JSON records and the
recorded source declarations in `EnhancedDiagramsCones`, `KanQuillenRightProper`,
`ReedyModelStructure` and `SegalSpace`. In particular the Kan-Quillen witness fixes
its fibrations to the horn RLP and its weak equivalences to the realization predicate;
Reedy `matchingFrom` is the actual limit-cone map and `model_structure` has objectwise
weak equivalences. These are the dependency notions, not similarly named substitutes.
There are no new nodes or dependency modules in this packet.

Correction/citer audit: the representation clarification leaves Rezk's mathematical
assertion unchanged. The revised step 7 obtains the pointed loop-space equivalences
from the natural completeness zigzag and invertible-endomorphism weak equivalences,
without presupposing degree-zero equivalence. I searched every DAG node's statement
and proof dependency lists. There is exactly one direct citer, so there is no second
citer to inspect: `lem-coef-segal-dk-diagonal-equivalence`. I opened its statement and
proof step 2: it applies this criterion to the completed spaces after establishing
mapping-space equivalences and essential surjectivity. Its `holds: true` verdict is
correct. The occurrence in `lem-coef-segal-homotopy-category-components` is ancestry
metadata, not a dependency on this item.

Edge cases: empty-to-empty has vacuous mapping and essential-surjectivity clauses;
empty-to-nonempty fails essential surjectivity and degree-zero equivalence. A map
from nonempty to empty cannot exist. Empty individual mapping fibers are allowed.
All degrees `n=0,1` are included, while the Segal comparisons start at two. Discrete
set nerves recover bijections; the nerve of `[1]` distinguishes an arrow from an
isomorphism. Nontrivial group nerves show completeness is a genuine hypothesis.
The universe `u` is arbitrary and shared by the original simplicial-set category;
no independent test universe, finiteness, characteristic, zero-object or nonemptiness
restriction occurs. No scheme or ring is present, so their edge cases do not apply.

Independent searches, with different wording from the worker:

- `msearch.py leanfinder`: “Reedy weak equivalence between complete Segal spaces
  detected by homotopy category and mapping spaces”: eight unrelated nerve,
  bifibrant-object and model-category results; no matching criterion.
- `msearch.py loogle`: `"Segal", "Weak"`: no hits.
- `msearch.py leansearch`: “A fully faithful and essentially surjective map of
  complete Segal spaces is a levelwise weak equivalence”: eight ordinary categorical
  fully-faithful/essential-image or abstract weak-equivalence results; no match.
- `msearch.py grep`: `Dwyer|Rezk|complete.*Segal|Segal.*complete|dk_iff`: only a
  bibliographic Rezk hit in Mathlib's pushout-product file. Independent `rg` over
  slopmaster2 `WeilConjectures`, Mathlib's algebraic topology, the upstream-name
  table and project `lean/Sheaf` found the published Segal definitions and the
  different homotopy-Segal diagonal theorem, not an existing levelwise criterion.

Mismatches and repairs: the theorem signature and dependency definitions need no
change. The Lean proof docstring's step 7 still described common-base fiber detection
and a homotopy-pullback pasting argument, unlike the repaired DAG proof. I replaced
that paragraph by the node's direct natural-loop-space comparison. I also corrected
the stale `lean.note` and worker-report claims that no correction had been recorded.
The superseded earlier reading remains explicitly labeled as historical. No theorem
is proved, no definition is introduced, and the sole proof remains `sorry`.

Validation of the repaired file: prescribed `scompile.py` completed both sandbox
and library-path checks cleanly (1.5 s and 1.6 s), with no errors or warnings.
I checked by eye the explicit binders and `universe u`, and checked programmatically
that `lean.statement` equals the file signature verbatim and all Lean lines are at
most 100 characters.
