## Worker report

The module `Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents` states
`AlgebraicGeometry.Scheme.Modules.degree_weighted_irreducible_components`, with
`sorry` as its entire proof. There are no definitions, helper theorems, new nodes,
dependency repairs, or changes to the natural statement. Stacks Project,
Varieties, Tag 0AYW (`lemma-degree-in-terms-of-components`, lines 9694–9775 in
`literature/stacks-project/varieties.tex`) gives this exact rank-one formula and
the preceding paragraph defines the generic multiplicities. The theorem docstring
records all eleven steps of the node's reviewed coherent-filtration proof.

Hypotheses and clauses, in the order of the node:

- A field k: `(k : Type u) [Field k]`.
- X proper over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
  `[IsProper (X ↘ Spec (.of k))]`. No Noetherianity hypothesis is added: it
  follows from properness over a field as in proof step 1.
- Topological dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`.
  Mathlib's dimension has value bottom for the empty scheme, so that case is included.
- An invertible O_X-module: `(N : X.Modules) [N.IsInvertible]`, using the
  recorded upstream scheme-module predicate.
- Finiteness of the one-dimensional irreducible component set: the first conclusion
  is `Set.Finite {c : Set X | c ∈ irreducibleComponents X ∧ topologicalKrullDim c = 1}`.
  This is asserted before quantifying over finite enumerations, so finiteness is
  a conclusion from properness, rather than assumed through an enumeration.
- C_1,...,C_t: `∀ (t : ℕ) (C : Fin t → Scheme.{u}) (j : (i : Fin t) → C i ⟶ X)`.
  The zero-based indexing is only an indexing convention. Every list is allowed,
  and the conditions below say it contains exactly the components, without repetitions.
- Reduced induced closed subscheme structures: `_hclosed : ∀ i, IsClosedImmersion (j i)`
  and `_hreduced : ∀ i, IsReduced (C i)`. `_hcomponent` requires each image
  `Set.range (j i)` to belong to `irreducibleComponents X` and to have dimension one.
  `_hcomplete` requires every such component to be an image, while `_hdistinct`
  requires the image function to be injective. A reduced closed immersion with given
  closed image is precisely the reduced induced structure, by the recorded
  `reduced_induced_closed_subscheme` uniqueness statement. Its affine radical ideals
  are prime for an irreducible image; this is part of the same notion, not an
  additional independent assumption. C is not assumed integral or proper.
- Each C_i is an integral proper curve: the second conclusion includes, for every i,
  `IsIntegral (C i) ∧ IsProper (j i ≫ X ↘ Spec (.of k)) ∧ topologicalKrullDim (C i) = 1`.
- Generic points in X: `(ξ : Fin t → X)` and
  `_hgeneric : ∀ i, closure ({ξ i} : Set X) = Set.range (j i)`.
  This is the node's explicit closure characterization. Each point belongs to its
  component, and the closed embedding identifies it with the component's generic point.
- Ambient generic multiplicities: `Module.length (X.presheaf.stalk (ξ i))
  (X.presheaf.stalk (ξ i))`. These are lengths of O_{X,ξ_i} over itself, not lengths
  of O_{C_i,ξ_i}, and not lengths of the line bundle.
- Every multiplicity is a finite positive integer: the per-component conclusion
  contains `∃ m : ℕ, 0 < m ∧ Module.length ... ... = m`. As the equality is in
  `ℕ∞`, it excludes infinite length and zero. Only after this assertion does the
  formula use the length's `toNat`, cast to `ℤ`.
- Restriction is j_i^*N: `((tensorPullback (j i)).obj N)` is the dependency's tensor
  pullback, not Mathlib's separately named pullback.
- Degree is χ(N)-χ(O): the existing `Scheme.Modules.degree` is used on both sides.
  The component degree is written with the explicit structural instance
  `@degree k _ (C i) ⟨j i ≫ X ↘ Spec (.of k)⟩ ...`. Thus every component uses
  its actual induced k-structure. There is no arbitrary structural morphism,
  no compatibility assumption and no hidden `let` in the statement.
- The weighted formula is `degree k N = ∑ i : Fin t, (length.toNat : ℤ) *
  @degree k _ (C i) ⟨j i ≫ X ↘ Spec (.of k)⟩ ((tensorPullback (j i)).obj N)`.
- The empty-sum clause is also stated explicitly as `(t = 0 → degree k N = 0)`.
  Completeness permits t=0 exactly when there are no one-dimensional components;
  this includes empty X and schemes of dimension at most zero.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `AlgebraicGeometry.IsProper`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`
  (def-weil-proper-morphism).
- `topologicalKrullDim`, `Mathlib.Topology.KrullDimension`
  (def-kun-topological-krull-dimension).
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (def-sc-invertible-module).
- `irreducibleComponents`, `Mathlib.Topology.Irreducible`
  (def-weil-irreducible-components).
- `AlgebraicGeometry.IsReduced` and `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties` (def-pc-reduced-scheme, def-pc-integral-scheme).
- `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (def-weil-closed-immersion).
- `PresheafOfModules.moduleStalkFunctor` and `stalkObj`,
  `WeilConjectures.Topology.PresheafModuleStalkFunctor` (def-weil-pbc-module-stalk),
  read with `scompile.py --source` because the older source checkout lacks the file.
  Here the structure-sheaf stalk itself is `X.presheaf.stalk (ξ i)`.
- `Module.length`, `Mathlib.RingTheory.Length` (def-weil-pbc-module-length).
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, publicly imported through the
  recorded `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
  (def-pc-module-pullback). The upstream definition was read with `scompile.py --source`.
- `AlgebraicGeometry.Scheme.Modules.degree`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` (def-pc-degree-line-bundle).
- `AlgebraicGeometry.Scheme.Modules.eulerChar`,
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` (def-pc-euler-characteristic),
  publicly imported by EulerChar; the body is the signed cohomological `finsum`.

The recorded modules for all already-stated proof dependencies are imported without
`public` unless already imported publicly for the statement. The unrecorded
`lem-trf-curve-euler-tensor-generic-rank` has no module to import yet; its role is
recorded in the proof docstring. Mathlib's Noetherian and ZariskisMainTheorem
modules supply the Mathlib proof leaves for Noetherianity, finitely many components,
and proper closed immersions. No proof dependency is restated in this delivery.

Edge cases checked:

- Empty X: dimension bottom satisfies hdim; there are no components, and Fin 0
  families of schemes, maps and points exist even with empty X. The formula and
  explicit empty-list clause give degree zero.
- A nonempty proper zero-dimensional scheme, including a nonreduced finite scheme:
  no one-dimensional components; positive multiplicity assertions are vacuous and
  degree zero agrees with triviality of line bundles on each Artinian local piece.
- One integral curve: one component and generic local-ring length one; the formula
  identifies the degree with its restriction to the same reduced integral scheme.
- A doubled curve: the ambient generic local ring has length two, so the theorem
  retains the required factor two rather than collapsing it to the reduced value.
- Two intersecting components: both appear once, without disjointness hypotheses.
  Embedded or isolated zero-dimensional supports contribute no degree, as in the proof.
- Arbitrary fields and characteristics: no algebraic closedness, smoothness,
  normality, connectedness, or reducedness of X is assumed. The universe u is
  explicitly bound and agrees with the existing field, scheme and degree interfaces.

Searches for an existing statement:

1. `msearch.py ... leanfinder` with query
   "Degree of an invertible module on a proper scheme of dimension at most one is
   the sum over irreducible components weighted by generic local ring length":
   eight hits, involving module rank at stalks, regular sequences and free-module
   length; none states the component degree formula.
2. `msearch.py ... loogle` with query
   "AlgebraicGeometry.Scheme.Modules.degree, Module.length, irreducibleComponents":
   zero hits; the search service does not index the project-specific `degree` name.
   This is not used as proof of absence: the source searches below check the project.
3. `msearch.py ... grep` with regex
   `degree.*(irreducible|component)|((irreducible|component).*degree)` in
   Mathlib/AlgebraicGeometry: two unrelated hits, Proj degree-zero localization
   and irreducibility of an elliptic-curve polynomial.
4. `rg -n` in WeilConjectures and lean/Sheaf for degree/component combinations,
   then the narrower `degree_eq_sum|degree.*(irreducible|weighted)|length.*degree`:
   no matching theorem. The upstream `Modules.Ample` theorem
   `Scheme.Modules.degree_eq_sum_of_pairwise_disjoint` was opened and checked:
   it applies to disjoint OPEN pieces and contains no generic multiplicities, so it
   does not state this node. `Scheme.Hom.degree_eq_sum` was also opened: it expands
   a Hilbert-function finite difference, and is a different degree construction.
5. Search for the item id throughout WeilConjectures found no attachment.
   `rg` in `dag/lean_names_upstream.json`, WeilConjectures/AlgebraicGeometry and
   lean/Sheaf/AlgebraicGeometry also found no declaration with the intended name
   `degree_weighted_irreducible_components` or a degree/irreducible-component name.
   The only relevant side-library occurrence was the proof-plan reference in
   `CurveDegreeTensorAdditive.lean`, which does not state this theorem.

No STATEMENT-DISPUTED flag or node fault remains. The previous attempt's objection
concerned the completed stage-1 split; this delivery leaves that split untouched and
adds only the stage-2 Lean record authorized by the current brief.

Validation: `scompile.py Q05 lem-trf-degree-weighted-irreducible-components
<module>` compiled both the sandbox and final module names cleanly (2.0 seconds
for each), with no diagnostics. Delivery preflight is run after this report is written.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
