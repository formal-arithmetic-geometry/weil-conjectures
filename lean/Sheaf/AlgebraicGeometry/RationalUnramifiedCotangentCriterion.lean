import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Rational-point cotangent criterion for unramified morphisms

Source: `literature/stacks-project/varieties.tex`, lemma-injective-tangent-spaces-unramified,
together with the local characterization by vanishing relative differentials
(blueprint: lem-sc-rational-unramified-cotangent-criterion).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be a morphism locally of finite type between schemes over a field `k`
(`hf : f ≫ pY = pX`), and let `x` and `y = f x` be closed points with residue fields equal
to `k` (`hκx`, `hκy`: the structure maps `k → κ(x)`, `k → κ(y)` are bijective). Then `f` is
unramified at `x` (some open `U ∋ x` with `U.ι ≫ f` locally of finite type with open-immersion
diagonal, def-weil-unramified-morphism) if and only if the map
`m_y/m_y² → m_x/m_x²` induced by the local ring map `f.stalkMap x` (Mathlib's
`Ideal.mapCotangent`) is surjective.

Source: literature/stacks-project/varieties.tex, lemma-injective-tangent-spaces-unramified
(blueprint: lem-sc-rational-unramified-cotangent-criterion).
Proof: choose affine opens `Spec B ∋ x` over `Spec R ∋ y` with `R → B` of finite type, and
let `A → C` be the induced local map of local rings; then `Ω_{C/A} = (Ω_{B/R})_q`. Since
`Ω_{B/R}` is finite, `f` is unramified at `x` iff `Ω_{C/A} = 0` (localize at some `g ∉ q`
and use the affine criterion for unramified ring maps). As `κ(y) = κ(x) = k`, the
Jacobi–Zariski sequence identifies `Ω_{C/A} ⊗ κ(x)` with the cokernel of
`m_y/m_y² → m_x/m_x²`; by Nakayama `Ω_{C/A} = 0` iff this cokernel vanishes. -/
theorem rational_unramified_iff_cotangent_surjective
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ pY = pX) (x : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    (hκx : Function.Bijective (pX.residueFieldMap x).hom)
    (hκy : Function.Bijective (pY.residueFieldMap (f x)).hom) :
    (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧
        IsOpenImmersion (pullback.diagonal (U.ι ≫ f))) ↔
      Function.Surjective
        (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (f.stalkMap x).hom.toIntAlgHom
          (Ideal.map_le_iff_le_comap.mp
            (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)) :
          IsLocalRing.CotangentSpace (Y.presheaf.stalk (f x)) →ₗ[ℤ]
            IsLocalRing.CotangentSpace (X.presheaf.stalk x)) := by
  sorry

end AlgebraicGeometry
