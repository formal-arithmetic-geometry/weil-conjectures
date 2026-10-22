## Worker report

Stage 2, group NO, item lem-sfb-quasi-compact-restriction-acyclicity, 2026-10-22.
The module Sheaf.Topology.QuasiCompactRestrictionAcyclicity states
TopCat.Sheaf.subsingleton_H'_of_quasiCompact_restriction_surjective with proof `sorry`.
It introduces no definitions or helper theorems. The node is changed only in `lean`.

Hypothesis and conclusion correspondence:

- A topological space X: `(X : Type u) [TopologicalSpace X]`.
- The quasi-compact open subsets form a basis: `hBasis : IsTopologicalBasis
  {U : Set X | IsOpen U ∧ IsCompact U}`. Mathlib's `IsCompact` is quasi-compactness:
  it assumes no Hausdorff property.
- Intersections of two quasi-compact opens are quasi-compact: `hInter` quantifies
  over `U V : Opens X`, assumes their `IsCompact`, and concludes `IsCompact` for
  their infimum, whose underlying set is their intersection.
- G is an abelian sheaf: `G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
  AddCommGrpCat.{u}`. This is precisely the category of abelian sheaves on the open site.
- Surjectivity whenever U is contained in V and both are quasi-compact opens:
  `hres` quantifies over these opens and `hUV : U ≤ V`, assumes compactness of
  both, and says `Function.Surjective (G.obj.map (homOfLE hUV).op)`. Taking the
  opposite arrow gives the actual restriction G(V) → G(U), not a locally
  surjective morphism of sheaves.
- Every quasi-compact open V: arbitrary `(V : Opens X)` and `hV : IsCompact (V : Set X)`.
- Every integer q > 0: `(q : ℕ) (hq : 0 < q)`. Every positive integer is a unique
  positive natural number; the dependency's right-derived cohomology uses ℕ.
- Ordinary G restricted to the open subspace V: Mathlib's
  `Topology.IsOpenEmbedding.sheafPullback AddCommGrpCat.{u}` applied to the
  inclusion `TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩` with its proof
  `V.isOpenEmbedding'`, and then to G. Read Functors.lean: this naive pullback
  composes with the open-image functor, so its sections over W are G(W) on the
  image open of X. It is ordinary open restriction, not an arbitrary sheaf/map.
- H^q(V,G|V) = 0: `Subsingleton (@CategoryTheory.Sheaf.H' ... (G|V) q ⊤)` on
  the open site of V. A subsingleton abelian group is the zero group. The top open
  is terminal, so H' there is right-derived global sections by the recorded
  cohomology dependency. The HasExt witness is supplied explicitly from enough
  injectives; it is not an extra hypothesis.
- Neither quasi-compactness of X nor a Noetherian condition is assumed: no such
  binder is present. No separation, sobriety, or spectrality binder occurs either.

Dependency declarations read and used:

- def-sc-topological-abelian-cohomology: Mathlib.CategoryTheory.Sites.SheafCohomology.Basic,
  `CategoryTheory.Sheaf.H'` (its full signature and docstring read). This is
  cohomology over an object; specializing to the top open of V gives the stipulated
  right-derived global sections of its restricted abelian sheaf.
- The restriction is the existing `Topology.IsOpenEmbedding.sheafPullback` from
  Mathlib.Topology.Sheaves.Functors, with `TopologicalSpace.Opens.isOpenEmbedding'`.
- The explicit cohomology witness uses `hasExt_of_enoughInjectives`,
  `IsGrothendieckAbelian.enoughInjectives`, and the existing upstream
  `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'`.
- Proof dependency def-weil-pbc-sites-and-cohomology: imported the recorded module
  Sheaf.CategoryTheory.SiteCoveringAxioms (`CategoryTheory.Precoverage.IsSiteForCoverings`).
- Proof dependency lem-weil-pbc-site-cech-vanishing-criterion: imported the recorded
  WeilConjectures.CategoryTheory.SiteCechVanishingCriterion, whose full statement
  `CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing` and docstring were read.
- Proof dependency lem-sfb-cech-vanishing-surjective-unions has no Lean record yet;
  consequently there is no module to import. It is used only in the natural-language
  proof, not needed to state this item. Its DAG statement is read and cited verbatim
  in substance in the proof docstring; no second statement of that node is introduced.

Source checked: cohomology.tex, lemma-vanishing-ravi (0A36),
lemma-cech-vanish-basis (01EW), and proposition-cohomological-dimension-spectral
(0A3G), especially its proof of (1) from (2). The finite-cover argument only needs
binary stability of quasi-compact opens, and not compactness of X. The module
contains the four-step proof plan of the item's current stage-1 split.

Edge cases checked before writing: X empty; V empty; the zero sheaf; equality U=V;
U empty; noncompact X (e.g. an infinite discrete space); covers of the empty open;
q=1; q=0 excluded exactly as in the node. Quasi-compact opens in an infinite
non-Hausdorff space are allowed as well: no T2 hypothesis is used. Arbitrarily
large spaces and coefficients can be represented in a common universe u; the
statement places no bound on u and imposes no additional structural hypothesis.
The finite-cover proof includes empty index sets and repeated tuple indices.
No statement fault or disputed assertion was found.

Searches for an existing declaration (all 2026-10-22):

- msearch.py leanfinder: "Surjective restrictions between quasi compact opens of a
  coherent topological space imply vanishing higher sheaf cohomology". Eight
  results: coherent-topology local surjectivity, condensed local surjectivity,
  toSheafCompHausLike, qcqs vanishing of local sections, and QuasicoherentData.coversTop.
  None states higher acyclicity from restrictions on quasi-compact opens.
- msearch.py loogle: `TopCat.Sheaf.IsFlasque`. Six results: the flasque definition,
  pushforward flasqueness, two skyscraper statements and two short-exact-sequence
  statements. Full flasqueness is stronger than the present restriction hypothesis.
- msearch.py grep: `flasque|flabby|acyclic` in Topology/Sheaves. Five hits, all in
  Flasque.lean, for flasqueness and its basic consequences; no matching theorem.
- msearch.py leansearch: "A sheaf with surjective restriction maps on a basis of
  quasi compact opens is acyclic for global sections". Eight hits on global section
  restriction, sheaf conditions, local surjectivity and quasicoherence; no match.
- rg in both lean/WeilConjectures and lean/Sheaf for the item id,
  `isZero_H.*[Cc]ompact`, and `quasiCompactRestriction` / `quasi_compact_restriction`:
  only the citation in Sheaf.Topology.SpectralSpaceCohomologyDimension; no declaration.
  Read that module's statement and cohomology witness as an existing consumer.
- More general rg searches in the topology directories for restriction acyclicity,
  basis quasi-compactness and restriction cohomology found constructible-basis and
  spectral-dimension material, but no theorem matching this statement.

Validation: scompile.py compiled the sandbox and library forms separately,
2.5 seconds each, with no errors or warnings other than permitted sorry diagnostics.
The only postponed proof is the named theorem of the item, whose docstring carries
its source and complete natural-language proof. The earlier NM merge is stage 1
only (as its report explicitly states); this item has no existing Lean record on
that base. Therefore that merge does not supply the stage-2 statement.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
