## Worker report

The module `Sheaf.AlgebraicGeometry.FieldExtensionIrreducibleComponents` states
`AlgebraicGeometry.field_extension_irreducible_components`, with the whole proof `sorry`.
It introduces no definitions and no auxiliary theorems. The node is unchanged except for `lean`.
I read Stacks `literature/stacks-project/varieties.tex`, the complete statements and proofs of
Tags 04KW and 04KX (lines 1595–1670). They give precisely the three asserted component properties.
Nonemptiness is explicit in the last paragraph of 04KX, and is also implied by surjectivity of
field base change. There is no statement dispute or source fault.

Hypotheses and clauses, in the order of the node:

| Node text | Lean rendering |
| --- | --- |
| k a field | `(k : Type u) [Field k]` |
| K/k a field extension | `(K : Type u) [Field K] [Algebra k K]`, with the specified map `algebraMap k K` |
| X a scheme over k | `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))`; f is its structure map |
| X_K = X ×_{Spec k} Spec K | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))` |
| p the projection to X | `pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))` throughout |
| for every irreducible component T of X | the first `∀ T ∈ irreducibleComponents X` |
| p⁻¹(T) is nonempty | `((pullback.fst ...) ⁻¹' T).Nonempty` |
| p⁻¹(T) is a union of components of X_K | `∃ S : Set (Set ↥(pullback ...)), S ⊆ irreducibleComponents ↥(pullback ...) ∧ (pullback.fst ...) ⁻¹' T = ⋃₀ S` |
| every component C upstairs has actual image a component | the second conjunct, `∀ C ∈ irreducibleComponents ↥(pullback ...), (pullback.fst ...) '' C ∈ irreducibleComponents X` |
| C ↦ p(C) surjects onto components downstairs | the third conjunct, `∀ T ∈ irreducibleComponents X, ∃ C ∈ irreducibleComponents ↥(pullback ...), (pullback.fst ...) '' C = T` |
| no finite type, quasi-compactness, reducedness, algebraicity, or separability assumptions | none of these occurs in the binders or premises |

The last two conjuncts are precisely well-definedness and surjectivity of the stated assignment
on the component subtypes: its value is the image set, so no arbitrary component map is assumed.
There is no closure in the conclusion. `S` is an unrestricted set of subsets, not a finite set.
The explicitly bound universe u is the common ambient universe for the scheme category and its
field spectra, as in the recorded base-change convention; there is no quantified test-object
universe, smallness hypothesis, or bound on the number of components. `autoImplicit false`
ensures every variable is explicitly bound.

Statement dependencies used, after reading their node records and source declarations:

| Node | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs`, `Algebra`, `algebraMap` |
| def-weil-scheme-over-base | `Mathlib.AlgebraicGeometry.Over`, `AlgebraicGeometry.Scheme.Over`; the explicit structure-map presentation is used |
| def-pc-base-change | `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; its docstring specifies `pullback f T.hom`, with projection to X equal to `pullback.fst`. Its recorded `Scheme.Modules.moduleBaseChange` is the module-sheaf clause, not a replacement for scheme base change. |
| def-pc-fibre-product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`, `pullback.fst` |
| def-weil-irreducible-components | `Mathlib.Topology.Irreducible`, `irreducibleComponents` (maximal nonempty irreducible subsets) |

The additional recorded `Scheme.baseChangeField` abbrev was read in
`WeilConjectures.AlgebraicGeometry.BaseChangeField`; its body is exactly the same pullback.
No alternative notion is defined here. All modules of the available proof dependencies are
plain imports; statement modules are public imports. The declaration docstring reproduces all
eight proof steps and their dependency-node names, including the arbitrary-extension comparison
square through an algebraic closure.

Edge cases checked mathematically before writing:

- Empty X: there are no components on either side. All three universal assertions are vacuous;
  the first conjunct does not assert that X or X_K is globally nonempty.
- k = K: base change is canonically X; each inverse image is the single corresponding component,
  and each image is that component. The theorem does not demand a proper extension.
- X = Spec C over R and K = C: the one downstairs component has two upstairs components in its
  inverse image. A union, rather than one component or a bijection, is essential and is retained.
- Transcendental extensions are allowed; the proof does not infer that their projections are
  integral. Integrality is used only for the algebraic comparison legs in the docstring.
- Purely inseparable extensions and positive characteristic are included with no extra class.
- Nonreduced X, for example Spec(k[ε]/ε²), is allowed; the theorem uses the underlying topology.
- Infinite disjoint unions of spectra are allowed; no quasi-compactness or finiteness of S occurs.

Searches for an existing statement (all launcher msearch calls used group Q15 and this item):

- LeanSearch query: “For any field extension and any scheme over the field the images of
  irreducible components of its base change are irreducible components and every component is
  attained”. Eight hits included integral base-change stability, integral universally closed,
  finite components for Noetherian schemes, and
  `image_mem_irreducibleComponents_of_isPreirreducible_fiber`. None states this theorem.
- LeanFinder query: “Field extension base change scheme inverse image irreducible component is
  union of components and actual images are components”. Eight hits concerned pullback triplets,
  purely inseparable spectrum homeomorphisms, fibre inclusion images and residue-field fibres.
  None handles arbitrary extensions and all three clauses.
- Loogle initial query `irreducibleComponents, pullback` reported unknown identifier `pullback`;
  I repaired the query to `"irreducibleComponents"`. Twelve hits included the component
  definitions and general component-image/preimage lemmas with irreducible-fibre hypotheses.
  I read their complete signatures in Mathlib/Topology/Irreducible.lean:463–520. Their extra
  irreducible-fibre hypothesis fails for Spec C over R after C-base change.
- msearch grep `irreducibleComponents|irreducible_components` in `AlgebraicGeometry`: 25 hits,
  including `Scheme.Hom.irreducibleComponentsEquiv`. I read its signature and docstring in
  Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean:86; it assumes geometrically
  irreducible fibres and is not the arbitrary field-extension result.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `irreducibleComponents` and related names
  found component-descent and geometric-component results. I read the closest candidates
  `component_preimages_of_closed_descent` and
  `exists_finite_intermediateField_component_preimages` in full: the former assumes finite
  upstairs components and closed descent; the latter is finite-type finite-separable descent.
  Neither is an exact match. `FieldTensorUniqueMinimalPrime` is the existing proof dependency
  over a separably closed base, not the item itself.
- `rg` for this node id, `04KW`, `04KX`, and the intended new declaration name in
  `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` returned no match.

Validation: prescribed `scompile.py Q15 lem-sfb-field-extension-irreducible-components` compiled
both its sandbox probe and final library module cleanly (1.9 s and 1.7 s). No diagnostic commands
remain in the source, and its only postponed proof is the named theorem above.

## Second reading by Q15

This is the dispatcher's requested author self-check; independent review is the maintainer's.
I reread the node with the final signature: k, K and the algebra map are all bound; f supplies
exactly the k-scheme structure; the first projection is to X, not Spec K. The first conjunct
contains both nonemptiness and an unrestricted union of components. The second uses actual
set image rather than closure. The third chooses an upstairs component whose actual image is
the specified downstairs component, exactly surjectivity of that same assignment. The empty
scheme is not excluded. No auxiliary map, finiteness assumption, irreducible-fibre premise or
choice of a closed subscheme has leaked from the proof into the statement. No mismatch was
found and no node correction or dependency repair was made.
