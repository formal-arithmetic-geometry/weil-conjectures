module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.GroupTheory.PGroup

import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Sheaf.FieldTheory.OpenSubgroupFixedField

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace AlgebraicGeometry.IsConnectedCurve
/-- Core filtration and generic cover; annihilator supplied separately.
Proof: identify the finite primary stalk with its discrete Galois module,
apply the Sylow filtration after a coprime open-subgroup restriction, and
transport the resulting chain through the finite normalization model. The
fixed field supplies the displayed finite etale generic map and its degree.
(blueprint: lem-sc-generic-primary-coarse-filtration-core) -/
theorem exists_generic_primary_coarse_filtration_core
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (D : Scheme.{u}) (π : D ⟶ C), IsFinite π ∧
      IsConnectedCurve (π ≫ f) ∧ Smooth (π ≫ f) ∧ IsAffine D ∧
      ∃ hIntegral : IsIntegral D,
      letI : IsIntegral D := hIntegral;
      ∃ (n : ℕ) (F : ℕ → Sheaf (Spec D.functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        IsZero (F 0) ∧
        (∀ (a : ℕ), a < n →
          ∃ (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (d : ℕ),
            S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧
              Nonempty (S.X₂ ≅ F (a + 1)) ∧
              Nonempty (S.X₃ ≅ Nat.rec (0 : _)
                (fun _ A ↦ A ⊞ (Spec D.functionField).constantZMod ℓ) d)) ∧
        ∃ (q : Spec D.functionField ⟶ Spec C.functionField),
          q ≫ C.fromSpecFunctionField = D.fromSpecFunctionField ≫ π ∧
          Etale q ∧
          ∃ (d : ℕ), q.IsFiniteLocallyFreeOfDegree d ∧ d.Coprime ℓ ∧
          Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1} q).obj M ≅ F n) := by
  sorry

end AlgebraicGeometry.IsConnectedCurve
