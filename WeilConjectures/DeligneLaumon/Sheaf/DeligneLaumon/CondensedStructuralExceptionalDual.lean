/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Compactification.Defs
import all WeilConjectures.AlgebraicGeometry.Adic.AdicDenseOpenImmersionFiniteness
import WeilConjectures.AlgebraicGeometry.StructuralExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom


/-!
# Constructible condensed exceptional dual of the structural coefficient unit

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.19, Proposition 6.8.14 and
Remark 6.8.15 (blueprint: lem-per-condensed-structural-exceptional-dual).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory MonObj Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace Sheaf.DeligneLaumon

open scoped CategoryTheory.Functor

/-- Arbitrary-field open-immersion finiteness used by constructible dévissage. -/
private theorem open_push_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) := by
  have hint (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] (M : CondensedRing.integralConstructible ℓ E Z) :
      boundedConstructible (condensedRingObj (CondensedRing.integralCoeff ℓ E) Y)
        ((CondensedRing.lowerStar (CondensedRing.integralCoeff ℓ E) p).rightDerivedFunctor.obj
          M.obj) := by
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
    exact CondensedRing.open_integral_of_iso ℓ (ULift.{u} E) _
      (CondensedRing.integerNormedIso ℓ E) t p M.obj M.property
  have hp := CondensedRing.open_qbar_of_finite ℓ t p
    (fun E M ↦ CondensedRing.open_continuous_of_integral ℓ E t p
      (hint E) M.obj M.property) K hK
  exact hp


/--
For a separated finite-type scheme over a field in which `ℓ` is invertible, every
compactification of the structure morphism has its actual derived lower shriek restricting to
bounded constructible complexes and this restriction has a constructible right adjoint.  The
exceptional dualizing object is the image of the coefficient unit under that right adjoint, and
relative derived internal Hom into it is constructible for every constructible complex.  This is
only a statement on the constructible subcategories; no right adjoint on ambient derived
categories is asserted.

Proof plan recorded by the source.  First, the structure morphism is separated and finite type,
so every displayed compactification supplies its open and proper legs and the actual functor is
`Rp_*D(j_!)`.  Second, the constructible exceptional-adjoint theorem gives the restriction and
its right adjoint on the constructible full subcategories.  Third, applying that adjoint to the
constructible coefficient unit defines the exceptional dualizing object.  Fourth, the closed
relative derived tensor--internal-Hom structure and constructible dévissage give constructibility
of `RHom` first on coefficient sheaves and then for every bounded constructible complex.  Finally,
only invertibility of `ℓ` in the field and the finite-subextension construction of `Qbar_ℓ` are
used; no positive-characteristic or finite cohomological-dimension hypothesis, and no ambient
right adjoint, is asserted.

Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.19, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-per-condensed-structural-exceptional-dual).
-/
theorem condensedStructuralExceptionalDual
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Invertible (ℓ : k)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ∃ (U : AlgebraicGeometry.ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))),
      Nonempty (U.obj ≅ MonoidalCategoryStruct.tensorUnit _) ∧
      ∀ (c : Compactification X.hom),
        ∃ (F : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) ⥤
            AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))
          (G : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))) ⥤
            AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)),
          Nonempty (F ⋙ (boundedConstructible
            (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))).ι ≅
            (boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι ⋙
              rightDerivedLowerShriekOfCompactification
                (Profinite.padicAlgClRingObj ℓ) c) ∧
          Nonempty (F ⊣ G) ∧
          ∀ K : AlgebraicGeometry.ProEtale.BoundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left),
            boundedConstructible
              (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
              (
                ((AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
                    (Profinite.padicAlgClRingObj ℓ) (X := X.left)).obj
                  (Opposite.op K.obj)).obj
                (G.obj U).obj) := by
  have : Fact (ringChar k ≠ ℓ) := ⟨by
    intro h
    have hz : (ℓ : k) = 0 := by
      rw [← h]
      exact CharP.cast_eq_zero k (ringChar k)
    exact (isUnit_of_invertible (ℓ : k)).ne_zero hz⟩
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  obtain ⟨F, G, hF, hG⟩ := constructibleStructuralExceptionalAdjoint ℓ k
    (X := X.left) (Y := Spec (.of k)) X.hom
  let U : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))) :=
    ⟨MonoidalCategoryStruct.tensorUnit _, boundedConstructible_tensorUnit _ _⟩
  refine ⟨U, ⟨Iso.refl _⟩, fun c ↦ ⟨F, G, hF c, hG, ?_⟩⟩
  intro K
  exact boundedConstructible_ihom_of_over
    (tensorHypotheses_padicAlgClRingObj ℓ).lisseHypotheses X
    (fun A B _ _ _ _ _ _ j _ L hL ↦ by
      have : IsNoetherian A.left := isNoetherian_of_locallyOfFiniteType A.hom
      have : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
      exact open_push_constructible ℓ B.hom j.left L hL)
    K.property (G.obj U).property

end Sheaf.DeligneLaumon
