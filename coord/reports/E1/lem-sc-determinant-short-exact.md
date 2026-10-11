## Worker report

The item module is `Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact`, declaring
`AlgebraicGeometry.Scheme.Modules.determinant_shortExact`. Its proof is `sorry`.
The only added statement dependency is `def-sc-sheaf-exterior-power`; the item's original
statement, proof, proof dependencies, and all other fields are unchanged.

Hypothesis and clause correspondence:

- A scheme X: `{X : Scheme.{v}}`, using the `def-pc-scheme` Mathlib match.
- The three O_X-module sheaves and their maps: `S : ShortComplex X.Modules`, with
  `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, and `S.g`. The complex includes `S.f ≫ S.g = 0`.
- Short exactness including the zero endpoints: `hS : S.ShortExact`, Mathlib's exactness,
  monomorphism of `S.f`, and epimorphism of `S.g`. This is sheaf exactness; no surjectivity
  on sections of all opens is imposed.
- Finite locally free of constant ranks: `r₁ r₂ r₃ : ℕ` and each
  `[S.Xᵢ.IsFiniteLocallyFreeOfRank rᵢ]`. These are the source's existing
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, also the notion in the proof dependency
  `def-amb-finite-locally-free-module`; no duplicate rank predicate is introduced.
- Rank relation: `hr : r₂ = r₁ + r₃`.
- Determinants: `exteriorSheaf S.Xᵢ rᵢ`, defined by sheafification of actual Mathlib exterior
  powers. No rank, affine, or generic-point replacement is used.
- Invertible modules: the three conjuncts `(exteriorSheaf S.Xᵢ rᵢ).IsInvertible`, using the
  original recorded `def-sc-invertible-module` declaration.
- Isomorphism in the specified direction:
  `e : exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃`.
- Canonical: `∃! e` satisfying the source's wedge formula. On each open U, `a` are sections
  of the first term, `b` sections of the third, and `c` arbitrary lifts of `b` in the middle
  term. The premise is exactly `∀ i, S.g.val.app (op U) (c i) = b i`. The formula for
  `e.inv` sends the tensor of their wedges to the wedge of `S.f(a)` followed by `c`.
  `Fin.append` fixes this order; `Fin.cast hr` only transports the index length.
  This characterizes the source's canonical isomorphism, rather than choosing an arbitrary
  isomorphism class. Uniqueness is of maps satisfying this formula, not of all line-bundle
  isomorphisms. It follows locally where lifts exist and pure wedges generate.
- Restriction to opens: `e` is an isomorphism of sheaves, whose components are natural for
  all inclusions of opens. Its local wedge characterization quantifies over every `U`.
  Restricting this map gives the same canonical map for the restricted sequence: the formula
  restricts and characterizes it uniquely on a locally split cover. There is no separately
  chosen family of noncompatible local isomorphisms.
- The convention det(0) = O_X: degree zero is supplied by `exteriorSheaf_zero_iso` in the
  definition module: it uniquely identifies the empty wedge with 1 on every open. Equality here is the usual canonical identification, not equality of
  implementation representations of sheafification and the structure sheaf.

Dependencies and APIs read in full:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme` (locally affine locally ringed spaces and their morphisms).
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (every point has an open on which
  the pullback is the unit sheaf); this module also supplies the tensor category structure.
  It is imported transitively by the used `TensorSection` module.
- `SheafOfModules.IsFiniteLocallyFreeOfRank`, in
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: local free
  generators indexed by types equivalent to `Fin r`.
- `ShortComplex.ShortExact`, in `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
- `AlgebraicGeometry.Scheme.Modules.tmulSection`, in
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`: actual sheaf tensor sections.
- The new node uses existing `SheafOfModules` (`def-weil-sheaf-of-modules-category`),
  `ExteriorAlgebra.exteriorPower` and `exteriorPower.ιMulti`
  (`def-weil-pbc-exterior-algebra`), and `PresheafOfModules.sheafification` and its adjunction.
  Relevant signatures and docstrings were read in the source checkout. The item source is
  absent in this machine's literature mirror, so its lines 130-152 were read over ssh in
  the server's literature copy. Lines 140-147 explicitly give the lift-independent wedge
  formula and gluing, agreeing with the node's proof.

Edge cases checked before writing:

- r₁ = 0: no first-term factors; the formula is the wedge of quotient lifts, with the empty
  wedge representing 1 in O_X. r₃ = 0: no quotient lifts; the formula is the induced wedge
  of the inclusion. All three ranks zero: multiplication O_X tensor O_X to O_X.
- Empty scheme and empty open: no nonemptiness hypotheses; all zero-ring sections are
  covered, and invertibility is vacuous on the empty scheme. Empty tuples use Fin 0.
- Arbitrary characteristic including 2: the exterior algebra imposes v wedge v = 0, not
  merely skew symmetry or division by factorials; no characteristic assumption appears.
- Nonsplit global extension: lifts are quantified conditionally on each open. Local splitting
  suffices; no global splitting or global surjectivity on sections is assumed.
- Arbitrary schemes, with neither Noetherian, affine, separated nor curve assumptions.
  Universe v is explicit; the sheaf module universe follows the existing X.Modules API.

Searches for an existing statement, executed with msearch.py (and logged in searches.jsonl):

- LeanFinder: "determinant line sheaf exterior power multiplicative short exact sequence
  finite locally free modules": eight hits, including LinearMap.det_eq_det_mul_det and
  Picard-group ring-module results; none is this sheaf determinant isomorphism.
- LeanSearch, same query: service unavailable, HTTP Internal Server Error; no search verdict.
- Loogle: "exteriorPower": unknown identifier, no hits.
- Mathlib grep: "exteriorPower|ExteriorPower|determinant.*exact": exterior-power module
  constructions and basis lemmas, not the sheaf statement.
- rg over WeilConjectures for sheaf exterior powers and determinants, and grep for the item
  id: no implementation or item-tag hit. The representation/matrix exterior powers have
  different objects. rg over lean/Sheaf: only unrelated matrix determinant mentions.
- All new names were also checked in dag/lean_names_upstream.json, Mathlib, and
  WeilConjectures: no collision.

Both modules compiled together on the server without warnings or errors. All theorem proofs
are sorry; definitions contain no sorry. There is no statement correction or disputed claim.

## New nodes

`def-sc-sheaf-exterior-power` defines the exterior sheaf and wedge of local sections, with
its degree-zero identification and determinant terminology. Source: the blueprint
Riemann--Roch determinant paragraph, especially lines 140-147. DAG grep and
`tools/blueprint_refs.py search 'exterior power'` found no existing definition of exterior
powers of O_X-module sheaves (nine blueprint hits concern representations or theorem
statements). Mathlib/module and project searches found no such construction.

Additional msearch queries: LeanFinder "exterior power of a sheaf of modules sheafification
of exterior powers of sections" returned module exterior powers and the generic
PresheafOfModules.sheafification; neither combines them with varying-ring semilinear
restrictions. LeanSearch with this query was unavailable. Mathlib grep "exterior|determinant"
in Algebra/Category/ModuleCat/Sheaf gave no hits. rg in WeilConjectures and lean/Sheaf gave
no matching sheaf exterior-power implementation. The new node records these searches as
returned, including the unavailable service.

The module fixes each section module explicitly as a Mathlib exterior power. The induced
restriction is selected from its unique existence theorem, completely characterized on
spanning pure wedges. Identity/composition are separate named theorems, and the presheaf
and its sheafification are explicit definitions. This follows the project's established
AssociatedModule.lean pattern: postpone proofs of unique well-defined maps and their laws,
not the object data. The three helper theorems each have their complete natural-language
proof in a docstring and are recorded in this definition node's lean.declarations. The
new node's proof and proof_deps are empty as required for definition nodes.

## Second reading by E1

I reread the item node, its source paragraph, every recorded statement dependency, and both delivered
modules. The correspondence is as follows.

- The node's scheme (X) is Lean `{X : Scheme.{v}}`; this is Mathlib's `AlgebraicGeometry.Scheme`,
  with no affine, separated, Noetherian, proper, or characteristic assumption.
- The node's sequence of three O_X-modules and maps is `S : ShortComplex X.Modules`,
  with terms `S.X₁`, `S.X₂`, `S.X₃` and maps `S.f`, `S.g`. `hS : S.ShortExact` supplies exactness,
  `Mono S.f`, and `Epi S.g`, including the zero-endpoint convention; no sectionwise surjectivity
  was added.
- The three constant ranks are `r₁ r₂ r₃ : ℕ`, the hypotheses are the three exact
  `S.Xᵢ.IsFiniteLocallyFreeOfRank rᵢ` instances, and `hr : r₂ = r₁ + r₃`.
  These use the recorded `SheafOfModules.IsFiniteLocallyFreeOfRank` declaration.
- The determinant objects are exactly `exteriorSheaf S.Xᵢ rᵢ`, with the new module's
  sectionwise Mathlib exterior powers followed by sheafification. The conclusion contains all
  three requested invertibility clauses `(exteriorSheaf ...).IsInvertible`.
- The isomorphism has the node's direction and tensor product exactly:
  `exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃`.
- Its canonical characterization quantifies in the node's order over every open `U`, first-term
  tuple `a`, quotient tuple `b`, and middle tuple `c`; the premise is exactly
  `∀ i, S.g.val.app (op U) (c i) = b i`. The equation uses `e.inv`, `tmulSection`, and the
  `Fin.append` order (first `S.f(a)`, then lifts `c`) with `Fin.cast hr`. Thus it expresses the
  source's lift-independent wedge map and its restriction compatibility, while `∃!` makes the
  map canonical rather than merely an isomorphism of line objects.
- `exteriorSheafSection` handles the empty wedge; `Fin 0`, all ranks zero, and either zero
  endpoint are included. No nonempty-scheme or nonzero-ring hypothesis is present. The
  construction is characteristic-free and universe-polymorphic.

The source paragraph in `lem-sc-riemann-roch.md` (determinant paragraph of the proof of (*))
uses local splitting, top exterior powers, independence of quotient lifts, and gluing. The
Lean theorem's docstring records these proof steps and the rank-zero convention. The source's
surrounding curve hypotheses are not repeated by the node itself; the delivered Lean follows
that node statement exactly.

Searches were rerun and checked against `searches.jsonl`: LeanFinder (no sheaf determinant
statement), Loogle (only Mathlib exterior-power and unrelated Picard declarations), grep over
Mathlib (no sheaf determinant/exact statement), grep over `WeilConjectures` and `lean/Sheaf`
(no existing declaration), and blueprint/node search (no existing sheaf exterior-power
notion). LeanSearch was unavailable and is recorded as unavailable, with no verdict inferred.

One mismatch was found in the added definition node: its statement used “finite locally free of
constant rank” without citing the existing notion node. I repaired `def-sc-sheaf-exterior-power`
by adding `[def-amb-finite-locally-free-module]` to its statement and adding that id to
`stmt_deps`; no Lean declaration needed changing. The determinant item itself and both Lean
signatures were otherwise unchanged. The new definition has no hollow data: all object
`def`s are explicit, and postponed well-definedness, functoriality, and degree-zero facts are
named theorem declarations with `sorry` proofs. Both modules compile together cleanly with no
warnings other than permitted `sorry` declarations.

## New nodes

`def-sc-sheaf-exterior-power` was reread against the source's exterior-power/sheafification
paragraph. Its objects, restriction characterization, sheafification, local wedge section,
and degree-zero identification are all present; its finite-locally-free determinant clause now
cites `def-amb-finite-locally-free-module`.
