module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Induction principle for separated quasi-compact opens

Source: Stacks Project, Cohomology of Schemes, Lemma 08DR (coherent-lemma-induction-principle),
proof, first induction for separated quasi-compact opens
(blueprint: lem-sc-invert-s-cohomology-separated-induction).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A property holding on affine opens and stable under gluing a quasi-compact open with an
affine open holds on every separated quasi-compact open. Source: Stacks Project, Cohomology of
Schemes, Lemma 08DR (coherent-lemma-induction-principle), proof, first induction for separated
quasi-compact opens (blueprint: lem-sc-invert-s-cohomology-separated-induction).

Proof: choose a finite affine cover of `W` and induct on its cardinality; the empty open is
affine. Adjoin the last affine `V` to the union `U` of the preceding charts. Each chart's
intersection with `V` is affine by separatedness of `W`, so `U` and `U ∩ V` are separated
quasi-compact opens with shorter affine covers and satisfy `P` by induction; `V` satisfies `P`
as an affine open. The gluing hypothesis gives `P (U ∪ V)`. -/
theorem separated_quasiCompact_open_induction (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (W : X.Opens) (hW_qc : IsCompact (W : Set X)) (hW_sep : W.toScheme.IsSeparated) : P W := by
  sorry

end AlgebraicGeometry
