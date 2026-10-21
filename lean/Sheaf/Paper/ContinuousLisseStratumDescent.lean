module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import all Sheaf.Paper.ContinuousLissePullbackSystem
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem continuousLisse_lattice_on_stratum
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] (D : PullbackSystemCore Λ₀ Λ₁ φ)
    {X U V W : Scheme.{u}} [TopologicalSpace.NoetherianSpace W]
    (p : U ⟶ X) (j : W ⟶ X) (r : V ⟶ U) (q : V ⟶ W)
    [IsFinite q] [Etale q] [Surjective q] (w : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X))
    (hP : LocallyFree (condensedRingObj (Λ₁) X) P)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Λ₀) U))
    (hM : LocallyFree (condensedRingObj (Λ₀) U) M)
    (e : (Mod.extendScalars (coefficientMap (φ) U)).obj M ≅
      (CondensedRing.upperStar (Λ₁) p).obj P)
    (hdescent : ∀ (P' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ₁ W)), LocallyFree (condensedRingObj Λ₁ W) P' →
      ∀ (M' : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj Λ₀ V)), LocallyFree (condensedRingObj Λ₀ V) M' →
      Nonempty ((Mod.extendScalars (coefficientMap φ V)).obj M' ≅
        (CondensedRing.upperStar Λ₁ q).obj P') →
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₀ W),
        LocallyFree (condensedRingObj Λ₀ W) N ∧
        Nonempty ((Mod.extendScalars (coefficientMap φ W)).obj N ≅ P')) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj (Λ₀) W),
      ProEtale.IsConstructibleModuleObject (condensedRingObj (Λ₀) W) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (φ) W)).obj N ≅
        (CondensedRing.upperStar (Λ₁) j).obj P) := by
  obtain ⟨P', hP', ⟨iP⟩⟩ : ∃ P' : Mod _
      (condensedRingObj (Λ₁) W),
      LocallyFree _ P' ∧ Nonempty
        (P' ≅ (D.rational j).obj P) :=
    ⟨_, D.rationalFree j hP, ⟨Iso.refl _⟩⟩
  obtain ⟨M', hM', ⟨iM⟩⟩ : ∃ M' : Mod _
      (condensedRingObj (Λ₀) V),
      LocallyFree _ M' ∧ Nonempty
        (M' ≅ (D.integral r).obj M) :=
    ⟨_, D.integralFree r hM, ⟨Iso.refl _⟩⟩
  have e' : (Mod.extendScalars (coefficientMap (φ) _)).obj M' ≅
      (D.rational q).obj P' :=
    pullbackSystem_scalarSquareIso _ _ _ D p j r q w P M P' M' iP iM e
  obtain ⟨N, hN, eN⟩ := hdescent P' hP' M' hM' ⟨e' ≪≫ (D.rationalIso q).app P'⟩
  exact ⟨N, locallyFree_constructible hN, ⟨eN.some ≪≫ iP ≪≫ (D.rationalIso j).app P⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
