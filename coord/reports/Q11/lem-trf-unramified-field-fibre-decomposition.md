## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition` states
`AlgebraicGeometry.unramified_iff_exists_iso_coproduct_spec_finite_separable`.
It has one theorem, with `sorry` as its entire proof; it introduces no definitions.
The natural-language proof in its docstring follows all five DAG proof steps.
The node is unchanged apart from `lean`. No statement correction, missing interface,
new node, dependency repair, or statement dispute was needed.

Source checked directly: `literature/stacks-project/morphisms.tex`,
`lemma-unramified-over-field` (Stacks Tag 02G7), part (1) and proof,
lines 7789--7821. The source gives precisely this equivalence.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- A scheme X over k and its structure morphism: `(X : Scheme.{u})`
  and `(f : X ⟶ Spec (.of k))`. The explicit structure map is appropriate here:
  the equivalence concerns that map, its compatibility with every summand,
  and the recorded restriction/decomposition declarations take such maps.
- Unramifiedness: `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`.
  This is exactly the inline interface recorded by `def-weil-unramified-morphism`,
  with no replacement of its notion by formal unramifiedness alone.
- If and only if: `↔`; both directions of the original node are included.
- Arbitrary, possibly empty index set: `∃ (I : Type u)`. There is no `Finite`,
  `Fintype`, or `Nonempty` constraint on I.
- A field extension for each index: `(L : I → Type u)`,
  `(_ : ∀ i, Field (L i))`, and `(_ : ∀ i, Algebra k (L i))`.
  The existential field and algebra structures are the ones used in all following terms.
- Each extension is finite: `∀ i, Module.Finite k (L i) ∧ ...`.
  Over a field this is precisely finite vector-space dimension, not merely finite type
  as a field extension.
- Each extension is separable algebraic: `Algebra.IsSeparable k (L i)`.
  The recorded Mathlib class includes algebraicity: a nonalgebraic element has zero
  minimal polynomial, which is not separable.
- A disjoint union of the spectra as schemes: the scheme coproduct
  `∐ fun i : I ↦ Spec (.of (L i))`, with an isomorphism `e` to X.
  Mathlib's `AlgebraicGeometry.Limits` constructs these coproducts as disjoint unions;
  its `disjoint_opensRange_sigmaι` and `sigmaOpenCover` give disjoint open summands.
  This is a scheme isomorphism, including the structure sheaf.
- The decomposition is over k, with the stated extension structures:
  `∀ i, Sigma.ι (fun j : I ↦ Spec (.of (L j))) i ≫ e.hom ≫ f =
  Spec.map (CommRingCat.ofHom (algebraMap k (L i)))`.
  Thus the map on each summand is exactly the one induced by its k-algebra structure;
  no unrelated scheme isomorphism or arbitrary morphism is substituted.

Universe/edge-case checks made before writing:

- I can be empty; the coproduct is the empty scheme and the compatibility condition
  is vacuous. The structure morphism of the empty scheme is unramified.
- Infinite I is permitted, so infinitely many copies of Spec k are included;
  no quasi-compactness, finite type, or global finiteness was imposed on X.
- I and the L i lie in the scheme universe u. This does not restrict possible
  decompositions of `Scheme.{u}`: use the point set of X as I and its residue fields
  (or the finite affine-chart factors) in that universe. There is no independently
  smaller index universe, and u is explicitly bound.
- Spec k uses a one-element I with its identity extension; a finite disjoint union
  uses a finite I without requiring finiteness globally.
- A nontrivial purely inseparable finite extension does not satisfy the separability
  conjunct and its spectrum map is not unramified. Characteristic p is allowed.
- A nonreduced point such as Spec(k[epsilon]/epsilon^2) is not silently admitted:
  the scheme isomorphism forces the disjoint union of field spectra, including its
  reduced structure sheaf. A homeomorphism of point sets would not suffice.
- Spec of an infinite product of fields is not being substituted for the coproduct;
  the latter is the genuine disjoint union, with no extra nonprincipal primes.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map`.
- `def-weil-unramified-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `AlgebraicGeometry.IsOpenImmersion` (Mathlib.AlgebraicGeometry.OpenImmersion) and
  `CategoryTheory.Limits.pullback.diagonal` (Mathlib.CategoryTheory.Limits.Shapes.Diagonal).
  Their full signatures and docstrings were read; the node records an inline conjunction.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`,
  with its actual `algebraMap`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; read its docstring and algebraicity instance.

Additional existing Mathlib notions: `Module.Finite` from
`Mathlib.RingTheory.Finiteness.Defs`, and the scheme coproduct with `Sigma.ι` from
`Mathlib.AlgebraicGeometry.Limits`. No new definition node is needed.

Imports for recorded proof dependencies (non-public, since used by the proof plan):

- `WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`,
  `AlgebraicGeometry.unramified_baseChange_restrict_open`; the module was absent
  in the older checkout, so its current source was read using `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`,
  `AlgebraicGeometry.exists_algEquiv_pi_finite_separable_of_unramified_spec`.
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`,
  `AlgebraicGeometry.spec_finite_product_fields`.
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`,
  `Algebra.Etale.of_finite_of_isSeparable`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- The affine criterion node's Mathlib match is
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`, imported through
  `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`, together with the
  already imported finite-type interface. The criterion node has no `lean` record
  because it is a Mathlib leaf, as permitted by the brief.

Searches for an existing statement (all via the authorized read-only sources):

- `msearch.py leansearch`, query "unramified scheme over a field disjoint union
  finite separable spectra": 8 hits, including
  `Algebra.FormallyUnramified.iff_isSeparable` and scheme coproduct infrastructure;
  no scheme-level equivalence.
- `msearch.py leanfinder`, query "A scheme over a field is unramified if and only
  if it is a disjoint union of spectra of finite separable field extensions":
  8 hits, including `Algebra.Etale.iff_exists_algEquiv_prod` and formal-unramified
  classes; these are algebra-level results, not this arbitrary scheme coproduct statement.
- `msearch.py loogle`, query
  `AlgebraicGeometry.FormallyUnramified, AlgebraicGeometry.Scheme`: 12 hits;
  general formal-unramified interfaces and diagonal/residue-field results,
  no disjoint-union equivalence.
- `msearch.py grep`, query
  `unramified.*field|unramified.*Field|disjoint union of spectra`,
  subdirectory `AlgebraicGeometry`: 0 hits.
- Direct `rg` of the same concept and node id in the upstream WeilConjectures
  and project lean/Sheaf trees found residue-field properties, the affine
  decomposition, and `discreteTopology_of_unramified_over_field`.
  The latter gives only discreteness, not an over-k scheme decomposition or the converse.
  The node-id search found no existing declaration for this item.
- `rg` of the proposed full declaration name in Mathlib, upstream WeilConjectures,
  lean/Sheaf, and `dag/lean_names_upstream.json` found no duplicate.

Validation: single-file compilation is performed only through `scompile.py`;
`deliver2.py --no-push` and then `deliver2.py` perform the required preflight and delivery.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
