## Worker report

The module `Sheaf.AlgebraicTopology.FinalFaceEdgeHornFiltration` states
`SSet.exists_final_face_edge_horn_filtration`. It uses the standard simplex
`Δ[n]`, its subcomplex faces, Mathlib horns `Λ[d,a]`, and categorical pushouts.
The proof is postponed with the single expected `sorry`.

The Lean signature renders the node statement as follows. The hypothesis `n > 0`
is `(n : ℕ) (hn : 0 < n)`. The initial face
`T = Δ^{\{0,\ldots,n-1\}}` is
`stdSimplex.face ({Fin.last n}ᶜ : Finset (Fin (n + 1)))`; the final edge
`I = Δ^{\{n-1,n\}}` is
`stdSimplex.face ({⟨n - 1, by omega⟩, Fin.last n} : Finset (Fin (n + 1)))`.
Their union is the required `K 0`. A finite filtration is represented by
`t : ℕ` and `K : Fin (t + 1) → (Δ[n] : SSet).Subcomplex`, with
`K (Fin.last t) = ⊤` representing `K_N = Δ^n` and
`K h.castSucc ≤ K h.succ` representing every inclusion.

For each `h : Fin t`, the attachment data are `d : ℕ`, `a : Fin (d + 1)`,
a horn map `g : Λ[d,a] ⟶ K h.castSucc`, and a simplex map
`f : Δ[d] ⟶ K h.succ`. The clauses `2 ≤ d`, `0 < a`, and
`a < Fin.last d` render `d ≥ 2` and `0 < a < d`. The compatibility equation
is `Λ[d,a].ι ≫ f = g ≫ Subcomplex.homOfLE hle`; the categorical pushout is
`IsPushout Λ[d,a].ι g f (Subcomplex.homOfLE hle)`. The phrase that the
pushout is computed degreewise in sets is rendered explicitly by the final
clause, requiring `IsPushout` of the four evaluated maps for every
`q : SimplexCategoryᵒᵖ`.

The statement dependencies used are:

- `def-cbc-enhanced-diagrams-cones`: `SSet.stdSimplex`, the simplicial-set
  standard-simplex convention, and the horn convention; imported through
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- `def-weil-pbc-category-colimit`: Mathlib's
  `CategoryTheory.Limits.colimit`/`IsColimit` convention; the module imports
  `Mathlib.CategoryTheory.Limits.HasLimits` and uses `IsPushout` for the
  displayed finite colimits.

Edge cases checked before writing: for `n = 1`, the initial face and the final
edge both lie in the full 1-simplex and the theorem permits `t = 0`, so the
attachment quantifier over `Fin t` is empty. For `n ≥ 2`, the penultimate and
last vertices are distinct and the inner index satisfies `0 < a < d`. The
Finset face definitions include all degenerate simplices because membership in
`stdSimplex.face` is degreewise image containment; the degreewise pushout clause
therefore covers degeneracies as well. The empty attachment family is covered
by `Fin 0` without a nonemptiness assumption.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "finite filtration of the union of the initial face and final edge of a standard simplex by inner horn pushouts"`: returned Mathlib horn primitives (`SSet.horn`, `horn_eq_iSup`, low-dimensional horn pushouts), with no theorem for this filtration.
- `msearch.py ... loogle "IsPushout innerAnodyneExtensions"`: no result (the unqualified `IsPushout` query is not a Loogle identifier).
- `msearch.py ... grep "innerAnodyne|horn.*pushout|face.*horn" AlgebraicTopology`: found only generic horn, inner-anodyne closure, and low-dimensional pushout results; no matching finite filtration.
- `msearch.py ... leanfinder "standard simplex initial face final edge finite inner horn filtration"`: returned `SSet.horn`, `SSet.face_le_horn`, and related primitives only.
- `rg` over `WeilConjectures`, project `lean/Sheaf`, and Mathlib AlgebraicTopology found no declaration named or stating this result. The existing `SSet.gapped_face_inner_horn_presentation` has a different gapped-face hypothesis and does not state this initial-face/final-edge filtration.

No new definition node or dependency repair was needed. No
`STATEMENT-DISPUTED` issue was found.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
