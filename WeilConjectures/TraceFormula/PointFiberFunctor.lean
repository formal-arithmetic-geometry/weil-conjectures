/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
public import WeilConjectures.CategoryTheory.DerivedCategory.FieldDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.ShiftSumFullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.CategoricalTraceExact
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-!
# The point category, evaluated

Let `k` be a separably closed field and `s = Spec k`. The unit `ℚ̲̄_ℓ,s` of the abelian category
`Mod_{ℚ̲̄_ℓ,s}` of `ℚ̲̄_ℓ`-modules on `s_proét` is projective
(`AlgebraicGeometry.ProEtale.projective_regular_of_isSepClosed`), with endomorphism ring `ℚ̄_ℓ`.
Hence its global sections `Γ = Hom(ℚ̲̄_ℓ,s, -) : Mod_{ℚ̲̄_ℓ,s} ⥤ Mod_{ℚ̄_ℓ}`
(`ProEtale.CondensedRing.pointSections`) are exact, and induce a triangulated functor
`Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ⥤ D(ℚ̄_ℓ)` (`ProEtale.CondensedRing.pointFiberFunctor`).

Every object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` is bounded with finite free cohomology sheaves
(`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`), so it is a shifted sum of finite free
objects (`DerivedCategory.isShiftSum_of_isGE_of_isLE`), the truncation triangles splitting because
the unit is projective. On shifts of the unit, `Fib_s` is bijective on morphisms: both sides
vanish in nonzero degrees by projectivity, and in degree zero they are `ℚ̄_ℓ`. Hence `Fib_s` is
fully faithful (`DerivedCategory.homBijective_of_isShiftSum`), and its essential image is the
bounded complexes with finite-dimensional cohomology
(`ProEtale.CondensedRing.exists_fiberFunctor_point`, blueprint
`def-weil-finite-coefficient-point`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- The abelian category of `ℚ̲̄_ℓ`-module objects on the pro-étale site of the point
`s = Spec k`, the ambient category of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧`. -/
abbrev PointMod : Type _ :=
  Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left)

variable [IsSepClosed k]

/-- For `k` separably closed, the unit of `Mod_{ℚ̲̄_ℓ,s}` is projective. -/
instance projective_tensorUnit_pointMod : Projective (𝟙_ (PointMod ℓ k)) :=
  projective_regular_of_isSepClosed (k := k) _

/-- The scalars `ℚ̄_ℓ` acting on the unit of `Mod_{ℚ̲̄_ℓ,s}`: a scalar `a` acts by the
multiplication by the constant global section `a`. -/
noncomputable def pointUnitEndRingHom : PadicAlgCl ℓ →+* End (𝟙_ (PointMod ℓ k)) :=
  (Mod.regularEndRingHom.comp (MonObj.Γ.mapFunctor (upperStarFromPoint (point k).left))).comp
    (Profinite.PadicAlgCl.constRingHom ℓ)

/-- For `k` separably closed, the endomorphisms of the unit of `Mod_{ℚ̲̄_ℓ,s}` are the scalars
`ℚ̄_ℓ`. -/
theorem bijective_pointUnitEndRingHom : Function.Bijective (pointUnitEndRingHom ℓ k) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  have := isEquivalence_upperStarFromPointMod (Ω := k) Λ
  have hE := (upperStarFromPoint (Spec (.of k))).bijective_regularEndRingHom_comp_mapFunctor Λ
    (Functor.FullyFaithful.ofFullyFaithful (upperStarFromPointMod Λ (Spec (.of k))))
  have : Nontrivial (MonObj.Γ Λ) := ⟨⟨1, 0, fun h ↦ Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
    (by rw [← map_one Mod.regularEndRingHom, h, map_zero])⟩⟩
  have hc : Function.Bijective (Profinite.PadicAlgCl.constRingHom.{u} ℓ) :=
    ⟨(Profinite.PadicAlgCl.constRingHom ℓ).injective,
      Profinite.PadicAlgCl.constRingHom_surjective ℓ⟩
  exact hE.comp hc

/-- The scalars `ℚ̄_ℓ` acting on the unit of `Mod_{ℚ̲̄_ℓ,s}`, as a ring homomorphism to the
opposite of its endomorphism ring, from the universe `u + 1` copy of `ℚ̄_ℓ`. -/
noncomputable def pointScalarsOp :
    ULift.{u + 1} (PadicAlgCl ℓ) →+* (End (𝟙_ (PointMod ℓ k)))ᵐᵒᵖ :=
  ((pointUnitEndRingHom ℓ k).toOpposite fun x y ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]).comp
      ULift.ringEquiv.toRingHom

/-- The global sections `Γ = Hom(ℚ̲̄_ℓ,s, -) : Mod_{ℚ̲̄_ℓ,s} ⥤ Mod_{ℚ̄_ℓ}` over the point. -/
noncomputable def pointSections :
    PointMod ℓ k ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) :=
  preadditiveCoyonedaObj (𝟙_ (PointMod ℓ k)) ⋙ ModuleCat.restrictScalars (pointScalarsOp ℓ k)

instance : (pointSections ℓ k).Additive := by
  unfold pointSections
  infer_instance

instance : PreservesFiniteLimits (pointSections ℓ k) := by
  unfold pointSections
  infer_instance

instance : PreservesFiniteColimits (pointSections ℓ k) := by
  unfold pointSections
  infer_instance

/-- The identity of the unit, as a global section of the unit. -/
noncomputable def pointSectionsUnit : (pointSections ℓ k).obj (𝟙_ (PointMod ℓ k)) :=
  𝟙 (𝟙_ (PointMod ℓ k))

omit [IsSepClosed k] in
/-- The scalar `a` acts on the global sections of the unit by the endomorphism `a` of the unit. -/
lemma smul_pointSectionsUnit (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    a • pointSectionsUnit ℓ k = pointUnitEndRingHom ℓ k a.down :=
  Category.comp_id _

/-- The global sections of the unit of `Mod_{ℚ̲̄_ℓ,s}` are `ℚ̄_ℓ`. -/
noncomputable def pointSectionsUnitIso :
    ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)) ≅ (pointSections ℓ k).obj (𝟙_ (PointMod ℓ k)) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (pointSectionsUnit ℓ k)) (by
    have h : ⇑(LinearMap.toSpanSingleton (ULift.{u + 1} (PadicAlgCl ℓ)) _
        (pointSectionsUnit ℓ k)) = (fun a ↦ pointUnitEndRingHom ℓ k a) ∘ ULift.down := by
      ext1 a
      exact smul_pointSectionsUnit ℓ k a
    rw [h]
    exact (bijective_pointUnitEndRingHom ℓ k).comp Equiv.ulift.bijective)).toModuleIso

/-- The global sections functor is bijective on the endomorphisms of the unit: every
endomorphism of the `ℚ̄_ℓ`-vector space `Γ(ℚ̲̄_ℓ,s) = ℚ̄_ℓ` is the composition with an endomorphism
of the unit. -/
lemma bijective_pointSections_map_unit :
    Function.Bijective (fun φ : 𝟙_ (PointMod ℓ k) ⟶ 𝟙_ (PointMod ℓ k) ↦
      (pointSections ℓ k).map φ) := by
  refine ⟨fun φ ψ h ↦ ?_, fun T ↦ ⟨T.hom (pointSectionsUnit ℓ k), ?_⟩⟩
  · have := congrArg (fun T ↦ T.hom (pointSectionsUnit ℓ k)) h
    change 𝟙 _ ≫ φ = 𝟙 _ ≫ ψ at this
    simpa using this
  · ext x
    obtain ⟨a, rfl⟩ := (bijective_pointUnitEndRingHom ℓ k).2 x
    rw [← smul_pointSectionsUnit ℓ k (ULift.up a), map_smul, map_smul]
    congr 1

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The base point `Spec k` is a noetherian topological space. -/
instance noetherianSpace_point : TopologicalSpace.NoetherianSpace (point k).left :=
  inferInstanceAs (TopologicalSpace.NoetherianSpace (Spec (.of k)))

/-- **The point category, evaluated**: the functor `Fib_s : Dᵇc(s)⟦ℚ̲̄_ℓ⟧ ⥤ D(ℚ̄_ℓ)` induced by the
exact global sections functor over the point. -/
noncomputable def pointFiberFunctor :
    Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  (boundedConstructible _).ι ⋙ (pointSections ℓ k).mapDerivedCategory

noncomputable instance : (pointFiberFunctor ℓ k).CommShift ℤ := by
  unfold pointFiberFunctor
  infer_instance

instance : (pointFiberFunctor ℓ k).Additive := by
  unfold pointFiberFunctor
  infer_instance

/-- `Fib_s` sends the unit `ℚ̲̄_ℓ,s` to `ℚ̄_ℓ[0]`. -/
noncomputable def pointFiberFunctorUnitIso :
    (pointFiberFunctor ℓ k).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  ((pointSections ℓ k).mapDerivedCategorySingleFunctor 0).app (𝟙_ (PointMod ℓ k)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pointSectionsUnitIso ℓ k).symm

end AlgebraicGeometry.ProEtale.CondensedRing
