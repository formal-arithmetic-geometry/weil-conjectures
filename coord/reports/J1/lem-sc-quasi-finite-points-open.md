## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen` states
`AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAtPoint`. For a morphism
`f : X ⟶ S` of schemes, it asserts existence of an open `U : X.Opens`; the
biconditional `x ∈ U ↔ IsQuasiFiniteAtPoint f x` identifies exactly the locus;
and `IsLocallyQuasiFinite (U.ι ≫ f)` states that the induced morphism on this
open is locally quasi-finite. The proof is `sorry`, as required for stage 2.

The dependency declaration used is
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
`AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint` and
`AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`.

Edge cases checked: `U` may be empty, and the existential statement allows the
quasi-finite locus to be empty; arbitrary universe `u` is bound explicitly; no
separation, finite-type, or nonemptiness hypotheses are added.

Searches: LeanSearch for “quasi-finite locus of a scheme morphism is open” (no
declaration); Loogle for “quasi-finite locus open morphism schemes” (no result);
grep of Mathlib found `Scheme.Hom.isOpen_quasiFiniteAt` in
`AlgebraicGeometry/ZariskisMainTheorem.lean`, but it concerns Mathlib's
`QuasiFiniteAt` under a `LocallyOfFiniteType` hypothesis and does not state the
Stacks notion or the induced restriction. `rg` of project sources found no
matching theorem.

## Earlier second reading (a previous round; superseded)

The theorem signature was read against the node clause by clause. The binder
`f : X ⟶ S` introduces exactly the scheme morphism; `∃ U : X.Opens` is the open
subset; the biconditional gives precisely membership in the quasi-finite locus;
and the final conjunct is local quasi-finiteness of the restriction `U.ι ≫ f`.
No mismatch was found and no changes were needed.


## Second reading by J1

Read the sandbox node and module independently, the recorded dependency node
`pqf-def-quasifinite` and its landed module
`lean/Sheaf/AlgebraicGeometry/QuasiFiniteMorphism.lean`, and the underlying
`Algebra.IsQuasiFiniteAtPrime` declaration in
`lean/Sheaf/RingTheory/QuasiFiniteAtPrime.lean`.

Source checked directly in the available Stacks TeX copy
`/tmp/stacks-project2/morphisms.tex`: lines 15201–15227,
`lemma-quasi-finite-points-open` (Tag 01TI), and lines 3520–3566,
`definition-quasi-finite` (Tag 01TD), including the section introduction.
The source introduces an arbitrary scheme morphism and has no standing
Noetherian, separated, finite-type, or field assumption. Also read
`/tmp/stacks-project2/algebra.tex` at `definition-quasi-finite` (Tag 00PL)
and `lemma-quasi-finite-open` (Tag 00QA).

Object, hypothesis, and conclusion checklist:

- Schemes X and S: `{X S : Scheme.{u}}`, with explicit `universe u`.
  Verdict: the same arbitrary schemes as the source.
- Scheme morphism f: `(f : X ⟶ S)`. Verdict: exact, no additional instances
  or hypotheses on f.
- Quasi-finiteness at x in the sense of `pqf-def-quasifinite`, clause 1:
  `IsQuasiFiniteAtPoint f x`. Opened its declaration: witnesses are an affine
  `W` containing x, an affine `V`, inclusion `W ≤ f ⁻¹ᵁ V`, the induced
  `appLE` algebra, finite type, and `Algebra.IsQuasiFiniteAtPrime` at the
  canonical prime of x. The latter uses openness of the singleton in the
  fibre spectrum through `preimageHomeomorphFiber`. Verdict: exact Tag 01TD
  and Tag 00PL notions, including finite type locally; no private copy.
- An open U contained in X: `∃ U : X.Opens`. Verdict: exact; the type
  carries openness and the subscheme inclusion.
- U consists of exactly all quasi-finite points of f:
  `∀ x : X, x ∈ U ↔ IsQuasiFiniteAtPoint f x`.
  Verdict: both directions and all points present, after the existential U.
- The induced morphism U → S is locally quasi-finite:
  `IsLocallyQuasiFinite (U.ι ≫ f)`. Opened its declaration, which is
  `∀ x : U, IsQuasiFiniteAtPoint (U.ι ≫ f) x` for the open subscheme.
  Verdict: exact clause 2 of Tag 01TD on the correct induced morphism.

Edge cases: the empty scheme and empty quasi-finite locus are allowed
(`U = ⊥`), and the pointwise conditions on an empty domain are vacuous.
There is no indexed family, natural-number parameter, or characteristic
restriction. All schemes in every universe u are covered; schemes initially
in distinct universes can be placed in a common larger universe. No field,
Noetherian, separation, compactness, or global local-finite-type restriction
appears. No binder or universe is left implicit or unbound.

Independent searches (actual calls recorded in searches.jsonl):

- LeanSearch: “The isolated finite type locus of a scheme morphism is open
  and its restriction is locally quasi finite”: service unavailable
  (Internal Server Error); no mathematical verdict attributed to it.
- LeanFinder: “For an arbitrary scheme morphism the points having an affine
  neighbourhood of finite type and isolated fibre form an open subscheme
  locally quasi finite”: eight hits, consisting of Mathlib's component
  `LocallyQuasiFinite` / `LocallyOfFiniteType` declarations; no exact theorem.
- Loogle: `"QuasiFiniteAt"`: twelve component ring-level hits, no exact theorem.
- Logged Mathlib grep: `isOpen.*quasi|quasi.*locus|QuasiFiniteAtPoint` in
  AlgebraicGeometry. Opened `Scheme.Hom.isOpen_quasiFiniteAt` in
  `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:292–293`, which requires
  `[LocallyOfFiniteType f]` and only states openness of Mathlib's
  `QuasiFiniteAt` locus. Read that predicate's declaration in
  `Morphisms/QuasiFinite.lean:339`: it is quasi-finiteness of the stalk map,
  omitting the local-finite-type witness. This candidate is not the node's
  arbitrary-morphism statement and does not include its final clause.
- Direct rg of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  repository `lean/Sheaf` for `QuasiFiniteAt`, `quasiFiniteAt`,
  `quasi.finite.*(locus|open)`, and `IsQuasiFiniteAtPoint`: related
  Zariski-main, isogeny, and ring-level results, but no existing exact
  statement. The recorded dependency provides the required notions.

Mismatch found and repaired: H8, the theorem docstring only listed proof
ingredients rather than carrying the node's five-step proof. Expanded it
with affine witnesses, localization, transport to D(g), union of open
neighbourhoods, and the same witnesses on the restriction, naming every
non-elementary dependency. Removed a redundant source/blueprint repetition.
No mathematical mismatch was found: theorem signature and node lean.statement
are unchanged and verbatim equal. The module has its source docstring,
upstream namespace, one used import, bound universe, lines at most 100
characters, one named theorem with proof `sorry`, and no definitions.
No new nodes, dependency modules, or statement correction are needed.

Verification: scompile.py compiled the reviewed module on the server in
1.6 seconds, exit code 0, without errors or warnings. A literal signature
comparison confirmed lean.statement matches the module; all Lean lines
are at most 100 characters.
