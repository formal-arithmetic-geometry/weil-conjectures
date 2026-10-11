## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteOpenCoverDegreeSum` states
`AlgebraicGeometry.finite_open_cover_degree_sum`. A field `k`, scheme `T`,
and structure morphism `t : T ⟶ Spec (.of k)` are explicit. The finite cover is
indexed by `Fin m` (including `m = 0`) with open subschemes `U i : T.Opens`.
The hypothesis `hcover : ∀ x : T, ∃ i : Fin m, x ∈ U i` renders the open-cover
condition. The hypothesis `hfinite` says each restricted structure morphism
`(U i).ι ≫ t` is finite. The function `n : Fin m → ℕ` supplies the integers
`n_i`; `hbound` renders the degree bounds using `finrankΓ`. The conclusion is
`IsFinite t ∧ t.finrankΓ ≤ ∑ i : Fin m, n i`, rendering finiteness and the sum
bound. The proof is `sorry` as required for stage 2.

Dependencies used are Mathlib's `AlgebraicGeometry.Scheme`/`Scheme.Opens`,
`AlgebraicGeometry.Spec`, `AlgebraicGeometry.IsFinite`, and the project
extension `AlgebraicGeometry.Scheme.Hom.finrankΓ` from
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.

Edge cases checked: `m = 0` makes `hcover` force `T` empty, and the finite sum
is zero; each `n i` is allowed to be zero. The universe is uniform and all
variables are explicitly bound.

Searches made: LeanFinder query “scheme over a field covered by finitely many
open subschemes each finite over the field; degree bounded by sum” (no matching
statement); LeanSearch query “scheme covered by finitely many affine opens each
finite over a field is finite with degree sum” (no match); Loogle query
`AlgebraicGeometry.IsFinite, Scheme.Opens, finrankΓ` (no matching theorem);
`rg` over `WeilConjectures/` and `lean/Sheaf` for
`finite_open_cover_degree_sum|degree_sum|finrankΓ` (only unrelated finite-cover
results). The recorded dependency declarations are used directly; no private
notions are introduced.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, every node clause has a direct Lean
counterpart: `k`, `T`, and `t` are explicit; `Fin m` permits all finite covers
including the empty one; `U i` and `hcover` express open subschemes and their
union; `hfinite` expresses finiteness over `k` through the restricted map; and
`hbound` and the conclusion use exactly the corresponding `finrankΓ` values and
sum. No mismatch was found.

## Second reading by F1

I independently read the node, its three statement dependency nodes, their
Mathlib declarations, the upstream degree definition, and the delivered Lean.
The repository's literature/stacks-project/morphisms.tex is absent on this
machine; I read the available Stacks source copy at
/home/ubuntu/c1-stacks-review/morphisms.tex, lines 15495–15550 (03JA) and
15310–15395 (03J5/03J6). The 03JA source reduces to finite affine pieces on a
fibre and asserts the sum bound; 03J6 explicitly obtains affineness from a
finite discrete underlying space. The node isolates this fibre argument.
The ambient locally quasi-finite morphism and quasi-compact source in 03JA
produce the finite covering; they are not further hypotheses on this lemma's
already supplied finite pieces.

Object/hypothesis/conclusion checklist, each with verdict:

- Field k: `{k : Type u} [Field k]`. Exact; arbitrary characteristic, no
  algebraic closure or perfection assumption.
- Scheme T and morphism to Spec k: `{T : Scheme.{u}}` and
  `(t : T ⟶ Spec (.of k))`. Exact. `Scheme` is a locally ringed space locally
  isomorphic to affine spectra (Scheme.lean:42); `Spec` is the affine spectrum
  (Scheme.lean:470). Neither supplies an extra separatedness or finiteness
  assumption.
- Finite list of m open subschemes, m ≥ 0: `(m : ℕ)` and
  `(U : Fin m → T.Opens)`. Exact: reindexes W_1,...,W_m by 0,...,m-1.
  Restrict.lean:46/52 defines `U.toScheme` as the scheme restriction and `U.ι`
  as its open immersion, so these are the specified open subschemes.
- Cover T = union W_i: `hcover : ∀ x : T, ∃ i : Fin m, x ∈ U i`.
  Exact; overlapping or repeated pieces allowed.
- Each restricted structure morphism finite over k:
  `hfinite : ∀ i : Fin m, IsFinite ((U i).ι ≫ t)`. Exact.
  Finite.lean:39 defines finiteness as affineness plus finite ring maps on
  every affine target open, exactly the dependency node's notion.
- Nonnegative integer bounds: `(n : Fin m → ℕ)`. Exact.
- Each degree ≤ n_i:
  `hbound : ∀ i : Fin m, ((U i).ι ≫ t).finrankΓ ≤ n i`. Exact.
  FiberDegree.lean:80–94 defines ΓAlgebra through ΓSpecIso and the morphism's
  appTop, and finrankΓ as Module.finrank of its global section ring with that
  algebra structure. Thus the scalar map is the one specified by t|W_i,
  not an independently chosen k-algebra. Finiteness of each piece ensures
  finrank represents its dimension rather than the infinite-dimensional
  fallback value.
- T finite over k: first conjunct `IsFinite t`. Exact.
- Global section dimension bounded by sum: second conjunct
  `t.finrankΓ ≤ ∑ i : Fin m, n i`. Exact, with the same induced scalar map;
  the first conjunct ensures the dimension is finite. Quantifier order is
  k,T,t,m,U,n, then the three hypotheses, then both conclusions.

Edge cases: m=0 makes hcover imply T is empty; empty global sections are
subsingleton, degree and the empty sum are zero. Empty T with a nonempty
cover is also admitted. Each n_i may be zero; with finiteness this forces
that piece empty, and all-zero bounds force T empty. The zero section
algebra is allowed; the base is a field exactly as in the node. There is
no characteristic restriction. Universe u is explicitly polymorphic and
covers every small scheme/field pair in a common universe (lift smaller
objects to their common universe); the dependency signatures likewise use
Scheme.{u} and CommRingCat.{u}. No binder or universe is unbound.

Independent searches (different wording from the first worker):

- LeanFinder via msearch: "dimension of sections bounded by sum over finite
  open covering finite schemes over field": eight hits, including
  Scheme.zero_of_zero_cover, finiteSubcover_f, iSup_opensRange and
  openCoverOfIsOpenCover_I₀; none states finiteness plus the sum bound.
- Loogle via msearch: `"finrankΓ"`: zero hits.
- LeanSearch via msearch: "A scheme covered by finite open schemes over a
  field is finite and its global sections dimension is bounded by the sum
  of dimensions": service unavailable (Internal Server Error); no verdict
  inferred from this failure. The other services and source grep worked.
- rg in Mathlib/AlgebraicGeometry, all WeilConjectures, and lean/Sheaf for
  `finrank.*(cover|iSup)|finite.*(openCover|isOpenCover)|IsFinite.*(iSup|cover)`,
  plus `finrankΓ` and the proposed declaration name. The closest result is
  upstream `AlgebraicGeometry.finite_and_finrank_sections_iSup` in
  EffectiveCartierSum.lean:130. I opened its complete signature: it assumes
  pairwise disjoint opens and already finite sections over their union,
  concluding equality of dimensions; it neither proves finiteness of the
  scheme nor handles overlapping pieces. It cannot replace this lemma.
  Project FiberDegreeBound and BoundsFiberDegreesFieldPoints concern fibre
  bounds, not finite open-cover sums. The proposed full name is absent from
  Mathlib, upstream source, dag/lean_names_upstream.json and project Lean.

No mathematical mismatch found, and no new definition node, dependency
module, or statement correction is necessary. All notions use the recorded
Mathlib declarations or the existing upstream finrankΓ; no private or hollow
notion is introduced. The one theorem remains `sorry`, nothing is proved.
The proof docstring was too compressed for H8: it omitted the discrete-space
argument and named dependencies. I replaced it with the node's five proof
steps, including each cited ingredient, scalar compatibility, finite product
injection and the empty-cover case. I also made lean.statement literally
match the multiline signature, without changing its mathematical content.

## Reviewer fix (R-fod1019)

The covering hypothesis `hcover : ∀ x : T, ∃ i : Fin m, x ∈ U i` was restated as `hcover : ⨆ i, U i = ⊤`, the recorded open-cover form of the landed modules (DimensionAffineOpenCover, EtaleAffineCoverStratification, GlueComponentTransitionCocycle); mathematically the same condition T = W_1 ∪ ... ∪ W_m. Nothing else changed.
