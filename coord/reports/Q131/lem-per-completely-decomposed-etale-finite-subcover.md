## Worker report

The module `Sheaf.AlgebraicGeometry.CompletelyDecomposedEtaleFiniteSubcover` states
`AlgebraicGeometry.completelyDecomposed_etale_finite_subcover`, with `sorry` as its
only proof. It introduces no definitions. The node changes only in `lean`.

Source checked directly: ILO, Travaux de Gabber, Exposé II, Proposition 2.2.3 and
Corollary 2.2.4, printed p. 27, in the supplied PDF. The corollary extracts a finite
subfamily of an étale decomposed cover over a Noetherian scheme; the node is its
completely decomposed case. The source's proof uses compactness of the constructible
topology and openness of the decomposition loci. The declaration docstring carries
all five steps of the node's proof, including the residue-field argument.

Clause-by-clause correspondence:

- A Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with a finite affine
  cover by spectra of Noetherian rings, exactly the node's hypothesis.
- An arbitrary set of indices: `{I : Type w}`, with `w` independent of `u` and no
  nonemptiness, finiteness, countability or decidable-equality assumption.
- A family of scheme morphisms: `(U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)`.
- Every morphism is étale: `[∀ i : I, Etale (f i)]`.
- For every point there is a lift in some source:
  `∀ x : X, ∃ (i : I) (z : U i), f i z = x ∧ ...` in `hcover`.
- The induced residue-field map is an isomorphism:
  `IsIso ((f i).residueFieldMap z)`. This is the actual induced morphism
  `X.residueField (f i z) ⟶ (U i).residueField z`; the adjacent equality identifies
  its source point with `x`. A categorical isomorphism in `CommRingCat` is precisely
  an isomorphism of these fields. No arbitrary comparison map is substituted.
- A finite subset of the original indices: `∃ I₀ : Set I, I₀.Finite ∧ ...`.
- The same property after restriction: `∀ x : X, ∃ (i : I) (_ : i ∈ I₀) (z : U i),
  f i z = x ∧ IsIso ((f i).residueFieldMap z)`. The finite subset is chosen before
  quantifying over `x`, and each selected index belongs to that same subset.
- No hypothesis is placed on the sources besides their morphisms being étale;
  in particular no quasi-compactness, separation or finiteness assumption occurs.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff`; the scheme hypothesis uses
  `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
  Its finite-affine-cover equivalence uses exactly those Noetherian rings.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

All these dependency modules are public imports. Plain imports retain the stated
proof dependencies: finite presentation, finite type, closed and open immersions,
Noetherian spaces, spectral spaces and constructible topology. No module is imported
for `lem-per-rational-lift-locally-closed-section`, whose record currently has neither
a Lean declaration nor a Mathlib match; it is a proof prerequisite and does not enter
this statement's interface. No missing statement notion or dependency repair is needed.

Edge cases checked before writing:

- Empty `X`: `hcover` is vacuous and the empty subset of `I` satisfies the conclusion.
- Empty `I`: allowed; a nonempty `X` would make `hcover` impossible, while empty `X`
  still permits the empty finite subset.
- Empty individual `U i`: allowed and contributes no witnesses; such an index need
  not be selected.
- An identity morphism supplies a residue-field-isomorphism lift at each point and
  gives the expected singleton subfamily.
- A nontrivial residue-field extension alone is insufficient: the `IsIso` clause
  excludes replacing complete decomposition by ordinary surjectivity.
- Infinite disjoint unions as étale sources and infinite index types remain allowed.
  The index universe is independent; this theorem constructs no indexed scheme limit.
- Nonreduced and disconnected Noetherian bases are allowed. No integrality or
  characteristic assumption has been introduced.

Searches on 2026-10-24 (the wrapper also recorded `searches.jsonl`):

- `msearch.py leanfinder`, query: "A completely decomposed etale covering family of a
  Noetherian scheme admits a finite completely decomposed subfamily". Eight hits:
  small étale sites, ordinary open finite subcovers, algebraic étale descent,
  irreducible components and quasi-compact covers; none is the required assertion.
- `msearch.py leansearch`, query: "A Noetherian scheme completely decomposed etale
  covering family has a finite completely decomposed subfamily". Eight hits:
  Noetherian schemes and finite affine covers, ordinary open finite subcovers and
  étale pretopology; no completely decomposed finite-subfamily theorem.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.Hom.residueFieldMap`: zero hits.
- `msearch.py grep`, query: `completely.decomposed|Nisnevich|rational.*subcover`,
  subdirectory `AlgebraicGeometry`: zero hits.
- `rg -n 'completelyDecomposed_etale_finite_subcover|completely.decomposed|Nisnevich'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: no hits.
- `grep -rn 'lem-per-completely-decomposed-etale-finite-subcover'` in
  `lean/WeilConjectures`: no hits.

The old `lean_removed` record documents a deleted module, not an existing declaration;
the declaration search confirms it is absent. The sample `Sheaf.CategoryTheory.CompactObject`
is now an empty withdrawn module; its node points to the upstream module, which was read
for the module-mode and docstring conventions. No statement correction or dispute arises.

## Second reading by Q131

This is a separate self-review pass by the assigned worker; the dispatcher brief forbids
starting another agent and assigns independent review to the maintainer.

I reopened the node and the finished declaration and compared every binder and quantifier.
The finite-affine Noetherian hypothesis is represented by the equivalent Mathlib class;
the arbitrary family and the étale condition are preserved. The residue-field map is the
canonical contravariant map at the actual lift, with the point equality included both in
the hypothesis and the conclusion. The existential finite subset precedes all pointwise
witnesses, and membership in it is required in the conclusion. Empty cases are retained,
and the family has no extra hypotheses. Every variable and universe is explicitly bound,
with `autoImplicit` disabled for the declaration. No mismatch was found and no statement
field was changed. The only postponed proof is the named theorem for this DAG node.
