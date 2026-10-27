## Worker report

Delivered one new statement module,
`Sheaf.CategoryTheory.Triangulated.TExactTruncationTriangleComparison`, with theorem
`CategoryTheory.Triangulated.TStructure.texact_truncation_triangle_comparison`.
Its only proof is `sorry`. No definition, helper node, dependency repair, or statement
correction is needed. The source node is preserved in every field except `lean`.

Read the node and its four statement dependencies, their recorded declarations and
interfaces, BBD Proposition 1.3.3(i),(ii), printed pp. 29–30 (including the argument
that uniqueness includes the degree-one arrow), and the current blueprint's
`sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.md` and proof.
The blueprint's Frobenius-truncation clause uses exactly this formal t-structure result.

Hypothesis and notation correspondence:

| Node | Lean |
| --- | --- |
| Triangulated categories C and D | Independent `Type uC`, `Type uD` and `Category.{vC}`, `Category.{vD}` binders, with `Preadditive`, `HasZeroObject`, `HasShift … ℤ`, additive integer shifts, `Pretriangulated`, and `IsTriangulated` for each category. |
| Bounded t-structures | `tC : TStructure C`, `tD : TStructure D`, `_hC : tC.bounded = ⊤`, `_hD : tD.bounded = ⊤`. The boundedness hypotheses are retained even though the formal proof does not need them. |
| Exact F and its specified coherent shift comparison | `F : C ⥤ D`, `[F.CommShift ℤ]`, `[F.IsTriangulated]`. No alternative shift is chosen. `F.commShiftIso r` is the specified `s` in every degree. |
| Preserves both halves in every degree | `[F.IsTExact tC tD]`; its fields `isLE` and `isGE` quantify over every integer. |
| Arbitrary integer m and arbitrary K | `m : ℤ`, then `∀ K : C`; no degree or object is excluded. |
| U = τ≤m K, V = τ≥m+1 K | `(tC.truncLT (m + 1)).obj K`, `(tC.truncGE (m + 1)).obj K`. |
| Canonical distinguished triangle and its arrows | `(tC.triangleLTGE (m + 1)).obj K`, with `truncLTι`, `truncGEπ`, `truncGEδLT` at `m + 1`. `triangleLTGE_distinguished` supplies distinguishedness. |
| Normalized natural c⁻ and c⁺ | `(F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K` and `(F.eTruncGEIso tC tD (m + 1 : ℤ)).hom.app K`, the existing comparisons used by the recorded comparison dependency. Their counit/unit normalization is that dependency's first clause (lower cutoff specialized to m + 1). |

Conclusion correspondence:

| Node clause | Lean |
| --- | --- |
| The specified triple is an isomorphism of entire triangles | `∃ e : tC.triangleLTGE (m + 1) ⋙ F.mapTriangle ≅ F ⋙ tD.triangleLTGE (m + 1)` and its three component equations: `hom₁ = c⁻`, `hom₂ = 𝟙 (F.obj K)`, `hom₃ = c⁺`. A triangle isomorphism includes all three commutative squares. |
| The source triangle has last arrow s F(δ) | The existing `F.mapTriangle.obj` has `mor₃ := F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁`, exactly this arrow in Lean's diagrammatic composition order. Exactness makes this image distinguished. |
| Unique isomorphism with identity middle component | For every K and every triangle isomorphism `β` with these source/target triangles, `β.hom.hom₂ = 𝟙 (F.obj K) → β = e.app K`. This is objectwise uniqueness over the identity, not merely uniqueness among natural families. |
| Explicit last comparison square | `c⁺ ≫ δ_D = F.map δ_C ≫ (F.commShiftIso 1).hom.app U ≫ c⁻⟦1⟧'`. It has exactly the specified `s`, with no sign or independently selected boundary. |
| For every v, its truncation triple is a triangle morphism | The existing `tC.triangleLTGE (m + 1)` is a triangle-valued functor; its `map v` has components `(truncLT.map v, v, truncGE.map v)` by `Triangle.functorMk`. Thus all three squares are encoded by the existing definition. The theorem explicitly states its last square in the final conjunct. |
| Explicit boundary naturality | `truncGE.map v ≫ δ_L = δ_K ≫ (truncLT.map v)⟦1⟧'` for every `(K L : C) (v : K ⟶ L)`. |
| Comparison triples natural as triangle isomorphisms | The witness e is a natural isomorphism between triangle-valued functors, so its naturality is equality of entire triangle morphisms. It implies the required equation for every v, including the boundary square. |
| All equations in underlying triangulated categories | Every displayed boundary equation is in C or D, using their original shifts. The packaging of the comparison naturality is in `Triangle D`, whose morphisms are the corresponding underlying triples and their three square equations. |

Dependency declarations used and imported:

- `def-weil-triangulated-category` is a Mathlib leaf: `CategoryTheory.Pretriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Triangulated`, and `Functor.IsTriangulated`,
  `Functor.mapTriangle` in `Mathlib.CategoryTheory.Triangulated.Functor`.
- `def-weil-t-structure` is a Mathlib leaf: `CategoryTheory.Triangulated.TStructure`
  and `.bounded` in `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`;
  `.truncLT`, `.truncGE`, `.truncGEδLT`, `.triangleLTGE` in
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`.
- `lem-weil-heart-short-exact-triangles`: directly import its recorded module
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`, which publicly
  imports `…TStructure.ShortExact`. The proof plan uses the recorded
  `.triangle_hom_ext_of_isLE_of_isGE`, `.exists_iso_triangleLEGE`,
  `.truncLEAdjunction`, and `.truncGEAdjunction` from the latter module.
- `lem-pod-texact-truncation-comparison`: directly import its recorded module
  `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison` and use the exact
  canonical `Functor.eTruncLTIso`, `Functor.eTruncGEIso`, and `Functor.IsTExact`
  interfaces in its statement. Its recorded theorem `.texact_truncation_comparison`
  supplies normalization, uniqueness, and naturality for the proof plan.

The two explicit public imports cover all four statement/proof dependencies; no additional
proof-only module is needed. The declaration docstring gives all four DAG proof steps,
including both cancellation arguments, the TR3 argument, and the shift-naturality argument.

Edge cases checked before writing:

- K = 0, v = 0, the zero category, or the exact zero functor: both outer comparisons
  remain isomorphisms of zero objects; no nonzero-object or faithful-functor hypothesis
  is present. Identity middle components on zero objects are valid identities.
- K in the upper half: V is zero; the last square vanishes, and uniqueness reduces
  to upper adjunction. K in the lower half: U is zero, with the dual conclusion.
- F the identity, or v an identity: the normalized comparisons and naturality reduce
  to identities; no separately selected triangle comparison can change the last arrow.
- Arbitrary positive, negative, and zero m: both outer truncations use the same
  integer m + 1, hence the correct adjacent halves. For an object concentrated in
  degree m the upper term survives; for one concentrated in degree m + 1 the lower
  term survives. There is no accidental use of τ≥m instead of τ≥m+1.
- The four object/morphism universes are independent, and `autoImplicit false` rejects
  any unbound variable. No smallness assumption or extra universe equality is imposed.

Searches for an exact existing statement:

- `msearch.py … leanfinder` query: “An exact t exact functor preserves the canonical
  truncation triangle via its normalized comparisons naturally including the shifted
  connecting map”. Eight hits: homological functor exactness/long-exact-sequence
  declarations and `TStructure.truncGEδLT`. None includes normalized comparison
  components, objectwise uniqueness, and naturality of triangle isomorphisms.
- `msearch.py … loogle` query:
  `CategoryTheory.Triangulated.TStructure.triangleLTGE, CategoryTheory.Functor.mapTriangle`.
  Zero hits.
- `msearch.py … grep` query:
  `eTruncGEδLT_comm|triangleLTGE|eTrunc.*[Tt]riangle`, under
  `CategoryTheory/Triangulated`. Seventeen hits, giving the existing truncation triangle
  functor, distinguishedness, extended triangles, and the LE/GE versus LT/GE transport.
  These supply infrastructure, not the whole statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `eTruncGEδLT_comm|triangle_hom_ext_of_isLE_of_isGE|exists_iso_triangleLEGE` found the
  exact upstream boundary equation and uniqueness infrastructure, whose full source
  signatures and documentation were read. `Functor.eTruncGEδLT_comm` alone states
  only the comparison boundary square, not the full node.
- `rg` in both project trees and `dag/lean_names_upstream.json` for
  `texact_truncation_triangle_comparison|TExactTruncationTriangleComparison|trunc.*triangle.*comparison`
  found no declaration of the proposed name or exact statement. A direct search for
  the item's blueprint id found no existing module.

Validation: `scompile.py Q35 lem-pod-texact-truncation-triangle-comparison` compiled the
sandbox and library forms cleanly (9.2 s and 3.7 s). The only postponed declaration is
the theorem named above. No statement dispute or source fault was found.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
