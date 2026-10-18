module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-! The following maps are the scheme morphisms induced by linear forms and linear
maps on the standard affine coordinates. -/

/-- The global section associated with a linear form on `k^m`.

Source: Varshavsky, *Lefschetz--Verdier trace formula*, §3.2.4
(blueprint: lem-trf-constant-family-defect-finite-projection). -/
noncomputable def affineLinearSection (k : Type u) [Field k] (m : ℕ)
    (a : (Fin m → k) →ₗ[k] k) :
    Γ(𝔸(ULift.{u} (Fin m); Spec (.of k)), ⊤) :=
  ∑ i : Fin m,
    ((Scheme.ΓSpecIso (.of k)).inv ≫
        (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k)).appTop)
      (a (Pi.single i 1)) *
      AffineSpace.coord (Spec (.of k)) (ULift.up i)

/-- The affine map induced by a linear form on the coordinates.

Source: Varshavsky, *Lefschetz--Verdier trace formula*, §3.2.4
(blueprint: lem-trf-constant-family-defect-finite-projection). -/
noncomputable def affineLinearScalarMap (k : Type u) [Field k] (m : ℕ)
    (a : (Fin m → k) →ₗ[k] k) :
    𝔸(ULift.{u} (Fin m); Spec (.of k)) ⟶
      𝔸(PUnit.{u + 1}; Spec (.of k)) :=
  AffineSpace.homOfVector
    (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k))
    (fun _ ↦ affineLinearSection k m a)

/-- The affine map induced by a linear map on the transverse coordinates.

Source: Varshavsky, *Lefschetz--Verdier trace formula*, §3.2.4
(blueprint: lem-trf-constant-family-defect-finite-projection). -/
noncomputable def affineLinearRestMap (k : Type u) [Field k] (m : ℕ)
    (p : (Fin m → k) →ₗ[k] (Fin (m - 1) → k)) :
    𝔸(ULift.{u} (Fin m); Spec (.of k)) ⟶
      𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) :=
  AffineSpace.homOfVector
    (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k))
    (fun j ↦ affineLinearSection k m
      ((LinearMap.proj (R := k) j.down : (Fin (m - 1) → k) →ₗ[k] k).comp p))

/-- A linear projection finite on a proper reduced closed subscheme of affine space.

Source: Varshavsky, *Lefschetz--Verdier trace formula*, §3.2.4
(blueprint: lem-trf-constant-family-defect-finite-projection).

The proof chooses a nonzero equation of the proper closed subscheme and a direction on
which its top homogeneous part is nonzero (using
`lem-trf-infinite-field-top-form-direction`).  In coordinates adapted to that line the
equation is monic, which gives finiteness by polynomial division.  Homogenizing the
monic equation shows that the scheme-theoretic image closure misses the infinity
section.  The two pullback components below force the displayed coordinate isomorphism
to be the one induced by the stated linear equivalence, over `Spec k`.
-/
theorem exists_linearProjection_finite_closure_avoids_infinity
    (k : Type u) [Field k] [Infinite k] (m : ℕ) (hm : 1 ≤ m)
    (Y : Scheme.{u})
    (i : Y ⟶ 𝔸(ULift.{u} (Fin m); Spec (.of k)))
    [IsClosedImmersion i] [IsReduced Y]
    (hproper : ¬ Function.Surjective i.base) :
    ∃ (l : Submodule k (Fin m → k)), Module.finrank k l = 1 ∧
      ∃ (φ : (Fin m → k) ≃ₗ[k] k × (Fin (m - 1) → k)),
        LinearMap.ker ((LinearMap.snd k k (Fin (m - 1) → k)).comp φ.toLinearMap) = l ∧
        ∃ (e : 𝔸(ULift.{u} (Fin m); Spec (.of k)) ≅
            Limits.pullback
              (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k))
              (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k))),
          e.hom ≫ Limits.pullback.snd
              (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k))
              (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k)) =
            affineLinearRestMap k m
              ((LinearMap.snd k k (Fin (m - 1) → k)).comp φ.toLinearMap) ∧
          e.hom ≫ Limits.pullback.fst
              (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k))
              (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k)) =
            affineLinearScalarMap k m
              ((LinearMap.fst k k (Fin (m - 1) → k)).comp φ.toLinearMap) ∧
          e.hom ≫
              Limits.pullback.fst
                (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k))
                (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k)) ≫
              (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) =
            𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k) ∧
          IsFinite
            (i ≫ affineLinearRestMap k m
              ((LinearMap.snd k k (Fin (m - 1) → k)).comp φ.toLinearMap)) ∧
          Disjoint
            (Set.range
              (i ≫ e.hom ≫
                Limits.pullback.map
                  (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k))
                  (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k))
                  (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
                  (𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k))
                  (ProjectiveLine.affineChart (Spec (.of k))) (𝟙 _)
                  (𝟙 _) (by simp) (by simp)).imageι.base)
            (Set.range
              (Limits.pullback.lift
                ((𝔸(ULift.{u} (Fin (m - 1)); Spec (.of k)) ↘ Spec (.of k)) ≫
                  ProjectiveLine.infinity (Spec (.of k)))
                (𝟙 _)
                (by simp [ProjectiveLine.infinity_over])).base) := by
  sorry

end AlgebraicGeometry
