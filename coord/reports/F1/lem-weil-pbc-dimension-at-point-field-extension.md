## Worker report

The module `Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension` states
`AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension`, with the
stage-2 proof `sorry`. It introduces no definitions. The node statement and all other
node fields are unchanged, apart from the new `lean` record.

Source checked: [Stacks Tag 00P4](https://stacks.math.columbia.edu/tag/00P4),
Lemma 10.116.6 and its proof. The local literature checkout contains only literature
indices, so the source was read on the Stacks website. The source uses `K ⊗[k] S`;
the node and this module use the swapped tensor product `S ⊗[k] K` as the node explicitly
specifies. The swap preserves the corresponding spectrum points and their local dimensions.
The theorem docstring carries all five proof steps and the dependency names used in them.

Hypotheses and clauses, matched individually:

- Fields `k` and `K`: `{k : Type u} {K : Type v} [Field k] [Field K]`.
- The ring homomorphism `ι : k → K`: `[Algebra k K]`, whose structural homomorphism is
  `algebraMap k K`. This is data, not an extra restriction: every ring homomorphism between
  the two fields defines this algebra structure, and no algebraicity, finiteness,
  separability or characteristic condition is assumed.
- The commutative `k`-algebra `S`: `{S : Type w} [CommRing S] [Algebra k S]`.
- Finite type over `k`: `[Algebra.FiniteType k S]`, the dependency's Mathlib class.
- `S_K = S ⊗_k K`: the actual Mathlib tensor product `S ⊗[k] K`, not an abstract
  replacement. Its right-factor `K`-algebra structure is
  `Algebra.TensorProduct.rightAlgebra`, whose structural map is the canonical
  `includeRight`, `λ ↦ 1 ⊗ₜ λ`. The equality of dimensions depends on the underlying
  topological spaces and requires no additional binder for this canonical structure.
- The map `j : S → S_K`, `s ↦ s ⊗ 1`:
  `Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)`.
- A prime `q_K` of `S_K`: `(qK : Spec (.of (S ⊗[k] K)))` is a point of its affine
  spectrum, hence a bundled prime ideal with its primality proof.
- `q = j⁻¹(q_K)`, a prime of `S`: `PrimeSpectrum.comap j qK`, used directly rather
  than introducing a redundant prime and an equality hypothesis. The point is read in
  `Spec (.of S)` by the explicit argument `X := Spec (.of S)`.
- Dimensions of the two topological spaces at the respective points:
  `topologicalKrullDimAt (X := Spec (.of S)) (PrimeSpectrum.comap j qK)` and
  `topologicalKrullDimAt qK`. These are exactly the dependency definition's minima of
  open-neighbourhood dimensions, not the Krull dimensions of the local rings.
- The conclusion is equality of those dimensions, in the order specified by the node.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType` (docstring and full class signature read).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and its underlying prime spectrum,
  `Mathlib.AlgebraicGeometry.Scheme`. `Spec.map_apply` identifies contraction with
  `PrimeSpectrum.comap`; the latter avoids the common-universe restriction of scheme
  morphisms while allowing independently sized rings. The definition and signatures
  of `Spec`, `Spec.map`, and `Spec.map_apply` were read.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt`,
  `WeilConjectures.Mathlib.Topology.KrullDimension`. The full definition and docstring
  were read: `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`.
- Canonical tensor product ring map and prime contraction:
  `Algebra.TensorProduct.includeLeftRingHom` in `Mathlib.RingTheory.TensorProduct.Basic`,
  and `PrimeSpectrum.comap` in `Mathlib.RingTheory.Spectrum.Prime.RingHom`.

Edge cases checked before writing:

- The zero algebra is permitted. Its tensor product has no prime-spectrum point, so the
  universal assertion over `qK` is vacuous; no nontriviality assumption is added on `S`.
- Identity field extension gives the expected equality under the canonical tensor
  isomorphism. Infinite transcendental and inseparable extensions are both permitted.
- Any characteristic is allowed; fields supply only their usual nontriviality.
- Zero-dimensional algebras and presentations with no variables are not excluded.
- Generic points are permitted. For example the dimension at a point of an affine
  line is one, even at its generic point; this is why replacing the dimension with
  the height of the point or the dimension of its local ring would be incorrect.
- Reducible and nonreduced finite type algebras are permitted, with no domain or
  smoothness hypothesis. Three explicit universes `u v w` allow arbitrary sizes.

Searches made (the online and Mathlib searches are also recorded in `searches.jsonl`):

- `msearch.py leansearch`: "dimension at a point of a finite type algebra preserved by
  field extension". Service returned Internal Server Error; unavailable, no verdict.
- `msearch.py leanfinder`: "Krull dimension of Spec at a point is unchanged by extension
  of the ground field for a finite type algebra". Eight hits, including
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, and
  `Algebra.IsAlgebraic.finrank_of_isFractionRing`; none states this local topological
  dimension result under arbitrary field extension.
- `msearch.py loogle`: `"krullDim", TensorProduct`. No hits.
- `msearch.py grep`: `krullDimAt|dimensionAt|krullDim.*tensor|tensor.*krullDim`.
  Only a polynomial global ring-dimension calculation; no match.
- `rg` in the source library and project library for `dimensionAt|dimension_at|DimensionAt|krullDimAt`
  and for the full new declaration name: no exact existing statement. A case-sensitive
  `topologicalKrullDimAt` search also read the existing local-dimension definition and
  located smooth-relative-dimension results, not this result.
- `rg` for `dimension-at-point-field-extension` in the source, project library and
  `dag/lean_names_upstream.json`: no source declaration tagged for this item.
- Existing project modules `FibreDimensionAfterBaseChange` and
  `ClosedPointDimensionLocalRing` were inspected: the former compares relative fibres
  for a cartesian square of schemes and also asserts a fibre isomorphism; the latter
  compares local dimension with localization at a maximal ideal. Neither is the same
  statement about every prime of the tensor algebra.

No statement dispute, correction, missing notion, or unusable dependency was found.


## Second reading by F1

Read the delivered node and module independently, then opened all three statement
dependency nodes and the full signatures used from their recorded modules. Source:
Stacks Tag 00P4, `algebra.tex`, label
`lemma-dimension-at-a-point-preserved-field-extension`, statement and complete proof;
also the introduction to `section-dimension-finite-type-algebras-reprise`.
The local literature tree has no Stacks checkout. I read the raw Stacks `.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex and checked
https://stacks.math.columbia.edu/tag/00P4. The section adds no standing hypothesis
beyond those in the lemma. Its domain assumption belongs to the preceding lemma,
not to 00P4. The source uses the swapped tensor product; the symmetry carries the
canonical inclusion and corresponding primes to the node's convention.

The statement checklist, in introduction and conclusion order:

| Node object, hypothesis or clause | Lean rendering | Verdict |
| --- | --- | --- |
| Fields k and K | `{k : Type u} {K : Type v} [Field k] [Field K]` | Exact; no characteristic constraint. |
| Ring homomorphism iota from k to K | `[Algebra k K]`, with `algebraMap k K` | Exact equivalent data for a homomorphism out of a commutative field; not an algebraicity hypothesis. |
| Commutative k-algebra S | `{S : Type w} [CommRing S] [Algebra k S]` | Exact, including the zero ring. |
| S finite type over k | `[Algebra.FiniteType k S]` | Exact dependency definition: the top subalgebra is finitely generated. No module-finiteness assumption. |
| S_K is S tensor_k K | `S ⊗[k] K` | Actual tensor product, not a ring assumed isomorphic to it. |
| Right-factor K-algebra structure | Canonically available as `Algebra.TensorProduct.rightAlgebra` | The dimension statement uses only the underlying ring and topology; this canonical data requires no extra hypothesis or instance in the signature. |
| j sends s to s tensor 1 | `Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)` | Exact, read its definition in TensorProduct.Basic. |
| Arbitrary prime q_K in S_K | `(qK : Spec (.of (S ⊗[k] K)))` | Exact: the underlying type of the affine scheme is the bundled prime spectrum. |
| q is the inverse image along j | `PrimeSpectrum.comap ... qK` | Exact: comap has ideal `Ideal.comap j qK.asIdeal`; its primality is inferred. q is defined, so no additional prime or lying-over hypothesis is needed. |
| The spaces are Spec S and Spec S_K | `X := Spec (.of S)` on the left, and the type of `qK` on the right | Uses the dependency's actual affine schemes and Zariski topologies. |
| Dimension at each point | `topologicalKrullDimAt` | Exact dependency declaration: infimum over open neighbourhoods, not height or local-ring dimension. |
| Equality, in the node's order | `topologicalKrullDimAt (X := Spec (.of S)) (PrimeSpectrum.comap ... qK) = topologicalKrullDimAt qK` | All of the conclusion, with the same universal prime quantifier. |

Dependency signatures read: `Algebra.FiniteType` in
`Mathlib/RingTheory/FiniteType.lean:39`; `AlgebraicGeometry.Spec` and `Spec.map`
in `Mathlib/AlgebraicGeometry/Scheme.lean:470,479`; `topologicalKrullDimAt`
in `WeilConjectures/Mathlib/Topology/KrullDimension.lean:333`.
The last definition is exactly the infimum stated by the dependency node.
Also read `PrimeSpectrum.comap` and `comap_asIdeal` in Spectrum/Prime/RingHom,
and `includeLeftRingHom` and `rightAlgebra` in TensorProduct/Basic. Contraction
as a prime-spectrum function allows different universes without imposing the
common-universe condition of a scheme morphism.

Edge cases: if S is zero then Spec S_K is empty, and the theorem is vacuous in
qK. Empty schemes and the empty set of points are therefore covered. There is
no index-set binder to restrict. Presentations with n = 0 and zero-dimensional
algebras are covered by finite type. Identity, transcendental, inseparable,
and infinite field extensions are allowed. All characteristics are allowed.
Reducedness, irreducibility, smoothness and a chosen Noetherian instance are
not assumed. Generic primes are allowed: for example, at the generic point of
the affine line the neighbourhood dimension is one although the localized
ring has dimension zero. This checks that the correct notion was used.
The explicitly bound universes u, v and w impose no equality of sizes;
all names and instances in the signature are bound.

Independent searches performed in this reading:

- `msearch.py leanfinder`: "dimension of an open neighborhood in the spectrum
  unchanged after extending the base field". Eight hits: algebra-presentation
  dimension, algebraic ranks after fractions, and localization/height results;
  no exact statement.
- `msearch.py loogle`: `"topologicalKrullDim"`. Seven hits, including global
  homeomorphism invariance and the global prime-spectrum/ring-dimension equality;
  none concerns dimension at a point after arbitrary field extension.
- `msearch.py leansearch`: "local topological dimension of spectrum invariant
  under arbitrary scalar extension of a finitely generated algebra". Service
  unavailable (Internal Server Error); no no-match verdict asserted.
- `rg` on Mathlib for `krullDim.*[Bb]ase[Cc]hange`, its reversed order, and
  tensor/Krull-dimension combinations: no hits.
- `rg` on WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `topologicalKrullDimAt`, tensor/topological-dimension combinations and the
  item id. Opened the source smooth-relative-dimension theorem and the project
  `fibre_dimension_after_base_change` and
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal` signatures.
  They respectively impose smoothness, state relative fibre comparisons with
  an additional isomorphism clause, and concern maximal-prime localization.
  None is this node's exact statement. No duplicate definition is introduced.

H5/H6/H8/H9: the module contains no definitions and just one theorem, whose proof
is `sorry`. Both docstrings cite 00P4 and the exact blueprint id. I matched the
five docstring proof steps to the node's five steps: finite presentation and
contracted primes; Noetherian rings and flat extension maps; quotient-fibre
identification; cancellation in the height formula; the polynomial quotient
neighbourhood-dimension formula. Dependency names and the natural-language
argument are retained. Imports are used, the namespace has no Sheaf prefix,
and no line exceeds 100 characters. The recorded `lean.statement` matches
the theorem signature verbatim up to `:=`.

No mathematical or signature mismatch was found, so I left the module and node
unchanged. There are no new definition nodes, dependency modules or statement
corrections requiring additional review. The only change is this second-reading
section. Compilation and delivery preflight results are recorded below.

Validation: `scompile.py` compiled the sole module in 1.6 seconds, exit 0,
with no warnings or errors. Exact signature and line-width checks passed.
The `deliver2.py --no-push` dry run printed OK: preflight and compilation passed.
