## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupoidInvariantRankFiltration` states
`AlgebraicGeometry.groupoid_exists_rank_filtration`, with the sole proof `sorry`.
Its source is Stacks Project More on Groupoids, Tag 0AB9, lemma-finite-stratify,
read in `literature/stacks-project/more-groupoids.tex`, lines 2420–2459.
The complete six-step DAG proof is rendered in the theorem docstring.
No node statement or dependency list was changed; no additional definition is needed.

Clause-by-clause correspondence:

- Schemes U and R: `{U R : Scheme.{u}}`, with explicit universe `u`.
- The source, target, identity, inverse and composition: `s t`, `e`, `i`, and
  `c : pullback s t ⟶ R`, with `hG : IsGroupoidScheme s t e i c`.
- Finiteness of both projections: `[IsFinite s] [IsFinite t]`.
- Closed subschemes `Z n`: `∃ J : ℕ → U.IdealSheafData`; the represented scheme
  is `(J n).subscheme` and its closed immersion is `(J n).subschemeι`.
  Mathlib supplies the closed immersion instance, not a new hypothesis.
- `Z 0 = U`: `J 0 = ⊥`. Mathlib's `isIso_subschemeι_iff_eq_bot` identifies
  the zero ideal with the entire scheme, including its nilpotents.
- Descending closed inclusions: `Monotone J`. Increasing quasi-coherent ideals
  give closed subscheme inclusions in the opposite direction, via
  `Scheme.IdealSheafData.inclusion`, not just inclusions of their supports.
- Empty intersection: `(⋂ n : ℕ, ((J n).support : Set U)) = ∅`.
- Scheme-theoretic invariance for every n:
  `∀ n : ℕ, (J n).comap s = (J n).comap t`.
  Mathlib `comap` is the kernel of the base-changed closed immersion; its
  `comapIso` identifies the associated subscheme with the fibre product.
  Thus the equality retains the whole ideal, rather than only its radical.
- Positive ranks r: `∀ n : ℕ` with `r = n + 1`, covering exactly all r ≥ 1.
- `D_r = Z_(r-1) ∖ |Z_r|`: the canonical open subscheme of `(J n).subscheme`
  with open set `(J n).subschemeι ⁻¹ᵁ (J (n + 1)).support.compl`.
  `Scheme.Opens.ι` followed by `(J n).subschemeι` is its actual map to U.
- Projection from `R ×_(s,U) D_r`: `pullback.snd s` applied to that composite.
- Finite locally free of degree r: `.IsFiniteLocallyFreeOfDegree (n + 1)`.
  The existing class includes finite, flat, locally of finite presentation and
  the equality of the dimension of each fibre algebra with n + 1.
- There are no Noetherian, quasi-compact, flatness or finite-presentation
  assumptions. No global bound on n is imposed.

Recorded statement dependencies read and used:

- `def-a1-groupoid-scheme`: `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme`. Read its full structure and laws.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (affine plus finite on every affine open).
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; closed subschemes use Mathlib's existing
  `Scheme.IdealSheafData.subscheme` and `subschemeι`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical inclusion is `Scheme.Opens.ι`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.snd`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`, including its parent
  `IsFiniteLocallyFree`. Read the actual current definitions, at lines 894–910.

Mathlib's ideal-sheaf `support`, `comap`, `comapIso`, `subschemeι` and `inclusion`
were also read in IdealSheaf/Basic, Functorial and Subscheme. This is the same
closed-subscheme encoding used by the existing related theorem
`groupoid_exists_finitePresentation_rank_filtration` in
`Sheaf.AlgebraicGeometry.FinitePresentedGroupoidRankFiltration`.
That theorem has additional finite-presentation assumptions and conclusion,
so it is not the present node's statement and cannot be an existing match.

The stated proof dependency modules are imported, including groupoid source
translation, affine pushforward base change, quasi-coherent finite type on affines,
Fitting local generation, finite free algebra spectrum, affine fibre sections and
etale descent for degree. The Mathlib-matched proof dependencies are supplied by
Morphisms.Affine, Morphisms.Separated, AlgebraicGeometry.Limits and Morphisms.Etale.
The two proof dependencies `lem-trf-fitting-ideal-sheaf-pullback` and
`lem-sfb-bounded-generators-fitting-pullback-criterion` currently have no Lean record;
no module is available to import for them. They are not needed to type this statement
and remain explicitly cited in the proof docstring.

Edge cases checked before writing:

- Empty U forces empty R since s maps to U. Every support and stratum is empty;
  finite local freeness of any positive degree over an empty target is vacuous.
- Empty individual strata are allowed by the same existing degree class.
- Rank 1 is the n = 0 clause, and uses Z_0 exactly. Rank 0 is intentionally absent.
- The identity groupoid permits J_0 = 0 and J_n = 1 for n ≥ 1; its only nonempty
  stratum has degree 1, confirming the indexing direction.
- Nonreduced bases retain their nilpotent structure through actual ideal sheaves
  and equality of comaps, rather than reduced vanishing ideals.
- Non-quasi-compact bases with unbounded local ranks are allowed: the conclusion
  requires only pointwise eventual exclusion, not a single globally empty Z_n.
- No finite-presentation assumption was imported from the related stronger theorem.

Searches actually run (2026-10-24):

- msearch.py leanfinder: “A finite groupoid scheme admits an invariant descending
  closed rank filtration with finite locally free source on each rank stratum”.
  Eight hits concern finite morphisms/fibres and approximation, not this statement.
- msearch.py loogle: `"IsGroupoidScheme", "IsFiniteLocallyFreeOfDegree"`:
  successful search, zero hits.
- msearch.py grep: `groupoid.*(stratif|rank)|invariant.*Fitting`:
  successful search, zero Mathlib hits.
- msearch.py leansearch: “A finite groupoid scheme has an invariant descending
  filtration by closed subschemes with empty intersection and finite locally free
  source of rank r on each successive difference”: eight hits, concerning finite
  morphisms and ordinary module filtrations, not scheme groupoids.
- rg in `lean/WeilConjectures` and `lean/Sheaf` with
  `groupoid.*(stratif|rank)|invariant.*Fitting|invariant_rank_filtration`:
  no upstream match; the project has affine rank results and the related theorem
  with finite-presentation assumptions described above.
- grep of this item's exact node id in `lean/WeilConjectures`: no match.
- rg of `groupoid_exists_rank_filtration` in Mathlib, upstream, Sheaf and
  `dag/lean_names_upstream.json`: no declaration-name collision.

Validation: scompile.py compiled both sandbox and library module forms successfully
(5.5 seconds and 3.3 seconds respectively), with no errors or unexpected warnings.
No statement dispute or source correction is needed.

## Second reading by O4

I reread the node, source and completed file after the first compile. This is a
worker self-check; the independent review is performed by the maintainer, as the
assignment specifies, and no second agent was started.

The binders match all seven groupoid data and their laws, and impose only finiteness
of s and t. The zero ideal at index zero gives the full scheme, rather than just
full support. Monotonicity has the correct reversed direction for closed schemes.
Equality of comaps is scheme-theoretic. The stratum is the preimage in Z_n of the
complement in U of |Z_(n+1)|; thus it is the specified open subscheme, with its
canonical map to U, and the second pullback projection has this stratum as target.
The degree is n + 1, including rank 1 and all empty strata. The unbounded sequence
and empty intersection preserve the non-quasi-compact case. No mismatch was found
and no statement correction was made.
