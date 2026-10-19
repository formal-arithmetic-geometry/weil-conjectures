## Worker report

The module `Sheaf.AlgebraicTopology.SharpSimplexCriterion` states
`SSet.sharp_simplex_criterion`, with its sole proof `sorry`. Its docstring contains
all eight proof steps from the node, including the finite face-union induction,
horn-cell reduction, slice retract argument, and final factorization of an
arbitrary weak equivalence. No definition, dependency record, or statement is
changed. Only the item's `lean` field is added to the current node copy.

The inherited retry message described a previous stage-1 supersession and a
cancelled dry run. No sandbox directory for this item was present when this
worker started. The current shared node is split and reviewed PASS by NV; this
worker formalized that current statement rather than reviving an older split.
There is no repair note for this item under `coord/repair-notes`.

Hypotheses and clauses, matched individually:

- Small simplicial sets and an arbitrary map are `(E B : SSet.{u}) (p : E ⟶ B)`.
  The explicit universe `u` is unrestricted. There are no Kan, fibration,
  nonemptiness, monomorphism, or dimension-positivity assumptions.
- Condition (i) is the existing predicate `SSet.IsSharp p`, used as the left-hand
  side of both equivalences. Its definition quantifies over every small
  simplicial set `T` and map `t : T ⟶ B`, and applies the recorded
  `SSet.IsHomotopyCartesian` to the actual strict pullback square.
- Condition (ii) is the right-hand side of the first equivalence:
  `∀ (n : ℕ) (σ : stdSimplex.{u}.obj ⦋n⦌ ⟶ B),
  IsHomotopyCartesian (pullback.fst p σ) (pullback.snd p σ) p σ`.
  `ℕ` includes zero. The two projections give precisely the square with corners
  `pullback p σ`, `E`, `stdSimplex.obj ⦋n⦌`, `B`, in that order.
- Condition (iii) is the right-hand side of the second equivalence. Both
  dimensions range independently over `ℕ`, and `δ` ranges over ALL morphisms
  between the two standard simplices, rather than just face inclusions.
  The composite `δ ≫ σ` is the node's `σδ` in categorical composition order.
  `pullback.map p (δ ≫ σ) p σ (𝟙 E) δ (𝟙 B) (by simp) (by simp)` is the
  canonical map from `E ×_B Δ^m` to `E ×_B Δ^n`. Its maps on the two factors
  are respectively the identity of `E` and `δ`, and its map on `B` is the
  identity. The two `simp` terms only certify the commutative squares of that
  universal construction. They are not mathematical hypotheses or added lemmas.
  `Enhanced.IsWeakHomotopyEquivalence` imposes the recorded realization-based
  notion of weak homotopy equivalence on this map.
- The pair `(i ↔ ii) ∧ (i ↔ iii)` expresses equivalence of all three conditions.
  It neither assumes sharpness nor asserts the conditions unconditionally.
- The final no-fibrancy clause is rendered by the absence of such binders;
  neither `E` nor `B` nor either standard simplex is required to be Kan.

Dependency interfaces read, including their full source signatures and docstrings:

- `lem-coef-kan-quillen-right-proper`: module
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declarations
  `SSet.KanQuillen.weakEquivalenceStructure`,
  `SSet.KanQuillen.replacementMap`, and
  `SSet.KanQuillen.right_proper_kan_quillen`. Its weak-equivalence structure
  is defined from `Enhanced.IsWeakHomotopyEquivalence`; its theorem fixes the
  model structure and gives horn/boundary generation and right properness.
  The module is publicly imported as recorded by the statement dependency.
- `lem-coef-sharp-pullback-calculus`: module
  `Sheaf.AlgebraicTopology.SharpPullbackCalculus`, declarations
  `SSet.IsHomotopyCartesian`, `SSet.IsSharp`, and
  `SSet.sharp_pullback_calculus`. The two predicates are genuine definitions:
  the first uses weak-equivalence/fibration factorizations of both legs and
  the actual comparison into their pullback; the second quantifies this over
  all base changes. These definitions do not assume original Kan objects and
  agree with Rezk Section 2.3 and Proposition 2.7. The module is publicly
  imported; no private replacement is introduced.
- Mathlib `SSet.stdSimplex` in
  `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex` is `uliftYoneda`, hence
  the recorded representable standard simplex, with the correct universe.
- `Enhanced.IsWeakHomotopyEquivalence` from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` requires a bijection on realized
  path components and on every positive based homotopy group.
- The two further recorded proof dependencies are ordinary imports:
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits`
  (`SSet.realization_finite_limits`) and
  `Sheaf.AlgebraicTopology.SSetGluingFilteredEquivalences`
  (`SSet.gluing_filtered_weak_equivalences`). They supply the simplex
  contractibility and weak-equivalence gluing inputs in the proof plan.

Edge cases checked before writing: both dimensions zero; the identity simplex
map; face maps, degeneracies and maps between different dimensions; empty `E`;
empty `B` (then `E` is empty and there are no simplex maps to test); `p` an
identity; and `B` a point. For a vertex inclusion into `Δ[1]`, which is not
sharp, condition (iii) fails at the opposite vertex, since its comparison has
empty source and nonempty target. Thus the criteria are not vacuous for
arbitrary maps. No edge case is excluded by the signature. No
STATEMENT-DISPUTED flag or node correction is needed.

Searches made using the prescribed wrapper:

- LeanFinder query: `A simplicial map is sharp iff its pullbacks along maps
  between standard simplices are weak homotopy equivalences`. Eight hits:
  `SSet.modelCategoryQuillen.fibrations_eq`, `fibration_iff`, model structure
  data and generators, and general fibrant-object/homotopy lemmas. None states
  the sharp-map criterion.
- Loogle query: `SSet.IsSharp, SSet.IsHomotopyCartesian`. Zero hits; the tool
  reports `SSet.IsSharp` unknown in its Mathlib index. These are project notions.
- Mathlib grep query: `IsSharp|sharp_simplex|IsHomotopyCartesian` in
  `AlgebraicTopology`. Zero hits.
- LeanSearch query: `A map of simplicial sets is sharp if and only if all
  pullback squares over standard simplices are homotopy cartesian`. Eight hits
  about Kan lifting, cofibrations, simplices and balanced categories; no match.
- `rg` for `sharp_simplex|simplex.*sharp|IsSharp|IsHomotopyCartesian` in the
  upstream `WeilConjectures` tree and project `lean/Sheaf/AlgebraicTopology`:
  the upstream tree has no match; the project supplies the recorded predicates
  and sharp pullback/diagonal theorems but no simplex criterion.
- Search for the exact node id in upstream `WeilConjectures`: no match.

Source read online: Charles Rezk, *Fibrations and Homotopy Colimits of Simplicial
Sheaves*, https://rezk.web.illinois.edu/rezk-sharp-maps.pdf , Remark 4.2(1)--(3),
printed page 9. All three clauses agree with the node, without a fibrancy
restriction. Section 2.3 also agrees with the dependency's homotopy-cartesian
predicate. The paper's missing local archive does not prevent this source check.

Validation: `scompile.py Q107 lem-coef-sharp-simplex-criterion` compiled this
module both as sandbox source and at its library path, each clean in 1.6 s,
with no errors or unexpected warnings. `set_option autoImplicit false` enforces
explicit variable binding. Every Lean line is at most 96 characters. The
prescribed `deliver2.py --no-push` is run next; the independent second reader
will add their reading and perform the actual delivery.

## Second reading by Q107

Independent reading on 2026-10-17. I opened the current node, the sandbox node
and Lean module, both statement-dependency nodes and their recorded modules,
the two additional proof-dependency signatures, and the definitions underlying
the weak-equivalence and standard-simplex notation. There is no repair note for
this item. Only `lean` differs between the sandbox node and the current node;
there is no `statement_change`, new node, or dependency module to review.

Source check: I independently read Rezk, *Fibrations and Homotopy Colimits of
Simplicial Sheaves*, Remark 4.2(1)--(3), printed page 9, together with Section
2.3, Proposition 2.7 and the surrounding Theorem 4.1. The source is
https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, as the node records; this is
not a Stacks-tag item. Remark 4.2 specializes to ordinary simplicial sets and
allows any map, without assuming either object Kan. The node agrees with it.

Object, hypothesis and conclusion checklist, in the node's order:

1. Small simplicial sets and an arbitrary map: `(E B : SSet.{u}) (p : E ⟶ B)`.
   PASS. The universe `u` is explicitly bound and arbitrary, and there are no
   further typeclass or mathematical hypotheses. Monomorphisms belong to the
   model-structure context; the node does not require `p` to be a monomorphism,
   and neither does the Lean.
2. Standard simplices: `stdSimplex.{u}.obj ⦋n⦌`.
   PASS. I opened Mathlib's `SSet.stdSimplex`, defined by `uliftYoneda`, and
   its full-faithfulness declaration. These are the representables, lifted
   into the same coefficient universe as `E` and `B`; arbitrary morphisms
   between them are exactly the simplex operators, not a restricted family.
3. Condition (i): `IsSharp p`.
   PASS. The dependency's real definition quantifies over every
   `(T : SSet.{u}) (t : T ⟶ B)` and tests the actual pullback square.
   It is exactly the sharpness convention in the dependency node, consistent
   with Rezk Proposition 2.7. No alternative predicate is defined here.
4. Condition (ii): `∀ (n : ℕ) (σ : stdSimplex.{u}.obj ⦋n⦌ ⟶ B),
   IsHomotopyCartesian (pullback.fst p σ) (pullback.snd p σ) p σ`.
   PASS. `n` includes zero. The square has upper-left corner `pullback p σ`,
   upper-right corner `E`, lower-left corner the standard simplex and
   lower-right corner `B`, with precisely the four specified arrows.
   I read `SSet.IsHomotopyCartesian`: it existentially factors both legs
   by realization weak equivalences followed by Kan fibrations and requires
   the comparison, specified by both projection equations, to be a weak
   equivalence. This is Rezk Section 2.3, including commutativity, with no
   Kan hypothesis on any original corner and no hollow choice of data.
5. Condition (iii), quantifiers: `∀ (m n : ℕ)
   (δ : stdSimplex.{u}.obj ⦋m⦌ ⟶ stdSimplex.{u}.obj ⦋n⦌)
   (σ : stdSimplex.{u}.obj ⦋n⦌ ⟶ B), ...`.
   PASS. Both dimensions, every simplex map and every simplex of `B` are
   universally quantified in the same order as the node. Degeneracies and
   constant operators are included along with face maps.
6. Condition (iii), map and conclusion:
   `Enhanced.IsWeakHomotopyEquivalence
   (pullback.map p (δ ≫ σ) p σ (𝟙 E) δ (𝟙 B) (by simp) (by simp))`.
   PASS. Its domain is `pullback p (δ ≫ σ)` and codomain `pullback p σ`.
   The maps on the two factors are the identity of `E` and `δ`, over the
   identity of `B`, so this is the canonical induced map required by the
   node, not a chosen arbitrary map. The two `simp` proofs certify the
   defining commutativities only. I opened the weak-equivalence definition:
   it requires a bijection on realized path components and on every positive
   based homotopy group, as the Kan--Quillen dependency specifies.
7. Equivalence of all three conditions: the whole result is
   `(IsSharp p ↔ condition_ii) ∧ (IsSharp p ↔ condition_iii)`.
   PASS. This is precisely joint equivalence; none of the conditions is
   supplied as a hypothesis or asserted unconditionally.
8. No fibrancy hypothesis on `E` or `B`: PASS by inspection of the entire
   signature and of the predicates it uses. Mathlib's horn-defined
   fibration structure occurs inside the homotopy-pullback definition only;
   it does not restrict the input map or objects.

Edge cases: `m = 0`, `n = 0`, the identity operator, vertex inclusions,
degeneracies and constant operators are all present. Empty `E` is allowed:
all its pullbacks are empty. If `B` is empty, any map to it forces `E` empty
and there are no standard simplices of `B` to test, consistently with
sharpness. Identity maps and maps to a point are covered. As a nonvacuity
check, the inclusion of one vertex into the one-simplex fails (iii) on
pullback to the other vertex: the induced map has empty source and point
target. There is no indexing family needing nonemptiness, no ring or
characteristic restriction, and no scheme or zero-object hypothesis.
The single unrestricted universe is the ordinary category of small
simplicial sets throughout, including all test objects in `IsSharp`.

Independent searches, with different wording from the worker's:

- LeanFinder through `msearch.py`: `simplicial sets universal quasifibration
  criterion simplex base change weak equivalences`. Eight hits about
  Mathlib's Kan fibrations, horn generators and model-category lifting;
  none is this criterion.
- Loogle through `msearch.py`: `SSet.stdSimplex,
  CategoryTheory.Limits.pullback, _ ↔ _`. Zero hits.
- LeanSearch through `msearch.py`: `Universal quasifibrations of simplicial
  sets detected by simplex pullbacks`. Eight hits on Kan fibrations,
  finite pullbacks and cofibrations; none is a sharpness criterion.
- `rg` for `IsSharp|sharp_simplex|quasifibration|quasi.fibration` across all
  Mathlib and project `lean/Sheaf`, plus the broader
  `IsSharp|sharp_simplex|quasifibration|quasi.fibration|homotopy.cartesian`
  across the full upstream `WeilConjectures` tree. The upstream search
  has no hits; Mathlib has no matching notion. Project hits are the
  recorded sharp-pullback predicates/calculus, their use by
  `RezkDiagonalSharp`, and a prose quasifibration mention in
  `CofibrantHomotopyGroupoidCompletion`; none states this criterion.
  A further project-wide `homotopy.cartesian|simplex.criterion` search
  found no alternate criterion. Thus dropping this module for an existing
  declaration would be incorrect.

The ordinary imports of `realization_finite_limits` and
`gluing_filtered_weak_equivalences` supply the disk-contractibility and
pushout-gluing inputs of the node's proof. I checked their signatures.
The module and theorem docstrings have the correct source and blueprint
identifier; the theorem docstring retains all eight node proof steps,
including the face-union induction, horn reduction, slice retract and
arbitrary-weak-equivalence factorization. There are no definitions or
extra theorems in this delivery; the only theorem proof is `sorry`.
The `by simp` terms in the signature are structural map obligations.
All variables and the universe are explicitly bound, with
`autoImplicit false`; the longest line has 96 characters. The node's
`lean.statement` is verbatim equal to the complete source signature.

Verdict: PASS. No mathematical or interface mismatch was found, so I left
the Lean module and node record unchanged and added only this second
reading. Independent validation with the prescribed `scompile.py Q107
lem-coef-sharp-simplex-criterion` and the absolute sandbox module path
passed both the sandbox and library-path checks (1.4 s and 1.5 s), with
no errors or unexpected warnings. Delivery preflight and delivery follow.
