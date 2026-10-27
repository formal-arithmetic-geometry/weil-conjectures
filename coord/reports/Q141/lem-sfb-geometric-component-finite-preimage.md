## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricComponentFinitePreimage` states
`AlgebraicGeometry.exists_finite_geometric_irreducibleComponents_preimage`, with
` sorry` as its entire proof. No definitions or additional nodes are introduced.
The node is unchanged outside `lean`.

Source read: `literature/stacks-project/varieties.tex`,
`lemma-galois-action-irreducible-components-locally-finite-type` (Tag 04KZ),
assertion (3), including its affine-chart argument; also
`lemma-separably-closed-field-irreducible-components` (Tag 038H), and the first
paragraph of `proposition-units-general` (Tag 04L7). The last explicitly explains
why the component statement also applies to the full algebraic closure.

Hypothesis and conclusion correspondence:

- The field k is `{k : Type u} [Field k]`.
- The algebraic closure K/k is `{K : Type u} [Field K] [Algebra k K]
  [IsAlgClosure k K]`. Unlike an arbitrary algebraically closed extension,
  `IsAlgClosure` includes algebraicity. Both the embedding and the selected
  algebraic closure are arbitrary.
- The scheme over k is `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))`.
  This explicitly named structure morphism is needed to form the base change.
- Locally of finite type is exactly `[LocallyOfFiniteType f]`, with no
  quasi-compactness instance or finite-type assumption on all of X.
- W is the actual scheme `pullback f (Spec.map (CommRingCat.ofHom
  (algebraMap k K)))`; r is `pullback.fst` of the same two maps.
- Every component T is an arbitrary `(T : Set X)` with
  `(hT : T ∈ irreducibleComponents X)`.
- Finitely many C_1,...,C_n with n at least one is
  `∃ n : ℕ, 0 < n ∧ ∃ C : Fin n → Set W, ...`. Zero-based `Fin n`
  merely reindexes the paper's 1,...,n. No distinctness beyond the node is imposed.
- Each C_i is an actual irreducible component of the ambient W through
  `∀ i : Fin n, C i ∈ irreducibleComponents W`.
- The asserted equality is the set equality `r ⁻¹' T = ⋃ i : Fin n, C i`;
  it is the entire inverse image, not its closure or a dense subset.
- No connectedness, reducedness, quasi-compactness or global finiteness of the
  components of X is assumed.

All variables and the one ambient universe `u` are explicit; `k`, `K` and X
are in the ordinary shared scheme universe. The theorem is universe polymorphic,
so any collection of such objects can be placed in a common universe. No
separability or characteristic restriction appears.

Statement dependencies read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, including its docstring.
- `def-weil-algebraic-closure`: `IsAlgClosure`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (lines 262–274); the recorded match
  explicitly identifies this predicate as the arbitrary-closure interface.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (lines 35–75).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (lines 38–46).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme` (lines 469–480).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (lines 94–112),
  with scheme pullbacks supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  `Mathlib.Topology.Irreducible` (lines 104–108), defined by maximal
  `IsIrreducible` subsets; its nonemptiness requirement was read at lines 49–53.

The proof docstring reproduces all four DAG steps, naming their dependencies.
Available proof dependencies are imported: `IsOpenImmersion` and its base-change
projection instance from `Mathlib.AlgebraicGeometry.OpenImmersion`;
`AlgebraicGeometry.pullbackSpecIso` from `Mathlib.AlgebraicGeometry.Pullbacks`;
`Algebra.FiniteType.isNoetherianRing` from `Mathlib.RingTheory.FiniteType`;
the prime-spectrum Noetherian instance from
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`;
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` from
`Mathlib.Topology.NoetherianSpace`; and
`TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding` from
`Mathlib.Topology.Sets.Closeds` (lines 510–536).
The proof-only dependency `lem-sfb-field-extension-irreducible-components`
currently has neither a Lean record nor a Mathlib match, so there is no recorded
module to import. This does not obstruct stating this item; its import remains
for the maintainer when that proof prerequisite is stated.

Edge cases checked mathematically before writing: empty X has no T, so hT
makes the implication vacuous. For X = Spec k, the algebraic closure gives one
component and n=1. For already algebraically closed k and K=k, n=1 with C=T
is allowed. For a non-geometrically irreducible component, n may exceed one.
Inseparable extensions and nonreduced X are retained. An infinite disjoint union
of finite-type affine schemes is allowed, since no global compactness is assumed.
The index is required to be positive, preventing an empty decomposition of a
nonempty component preimage.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: “For a scheme locally of finite type over a field the inverse image
  of each irreducible component under base change to an algebraic closure is a
  finite nonempty union of irreducible components”. Eight hits: finite global
  sections of proper schemes, finite-morphism fibres and base-change stability;
  none states the item.
- Loogle: `"AlgebraicGeometry", "irreducibleComponents"`. Six hits. The closest
  `Scheme.Hom.irreducibleComponentsEquiv` assumes geometrically irreducible
  fibres, and `finite_irreducibleComponents_of_isNoetherian` requires global
  Noetherianity; neither applies in the stated generality.
- Mathlib grep: `finite.*irreducibleComponents|irreducibleComponents.*finite|
  preimage_mem_irreducibleComponents`, restricted to AlgebraicGeometry.
  Twelve hits, concerning Noetherian schemes or geometrically reduced morphisms;
  no exact match.
- LeanSearch: “An irreducible component of a scheme locally of finite type over
  a field has inverse image a nonempty finite union of irreducible components
  over an algebraic closure”. Eight hits, including Noetherian finiteness and
  irreducible-fibre preimage lemmas; no exact match.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `geometric.*component|finite.*irreducibleComponents|irreducibleComponents.*finite|
  preimage_mem_irreducibleComponents`, plus the mandatory node-id grep in
  `lean/WeilConjectures`. The node-id grep has no hit. Opened
  `WeilConjectures.AlgebraicGeometry.ComponentsFiniteSeparableDescent` and
  `FiniteFieldClosedComponentDescent`: both assume finiteness of all components
  after separable closure and assert a different descent conclusion.
  `Sheaf.AlgebraicGeometry.SepClosedFieldComponentsBijection` concerns connected
  components over a separably closed field. None is an exact match.
- The chosen full declaration name was searched in both project roots, Mathlib,
  and `dag/lean_names_upstream.json`; no existing declaration was found.

No statement correction, disputed statement, new node, or dependency repair.

## Second reading by Q141

Self-check of the completed node and module; the maintainer supplies the independent
review, and no other worker is claimed to have read this delivery. Rechecked every
binder against the node: `IsAlgClosure` retains algebraicity; local finite type
has no quasi-compactness companion; T is an ambient component; the C_i are
components of W rather than components of an arbitrary subspace; positivity of n
retains nonemptiness; and the equality uses the canonical first projection and
its full preimage. The first compiler pass required explicit scheme-to-carrier coercions `↥` in
the component family and component membership, to prevent Lean from inferring
a pullback in `Type`. These were corrected; no mathematical mismatch or
statement change was found.

Validation: `scompile.py` compiled both the sandbox and library module cleanly.
The first dry run caught that the signature record must omit its terminating
`:=`; corrected the metadata to the exact signature expected by preflight.
