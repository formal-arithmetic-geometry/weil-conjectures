/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointFiniteFreeModels
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Constructibility on a finite disjoint union of geometric points -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

private instance boundaryCompact : CompactSpace (condensedPointBoundary k I) :=
  (finite_coproduct_lfp_qcqs (fun _ : I ↦ (point k).left) (point k).left
    (fun _ ↦ 𝟙 _)).1 (fun _ ↦ inferInstance)

private instance boundaryQuasiSeparated : QuasiSeparatedSpace (condensedPointBoundary k I) :=
  (finite_coproduct_lfp_qcqs (fun _ : I ↦ (point k).left) (point k).left
    (fun _ ↦ 𝟙 _)).2.1 (fun _ ↦ inferInstance)

private def pointCoverData {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x) :
    Scheme.Cover.{u} Scheme.proetalePrecoverage X := by
  classical
  let e : ULift.{u} (Fin (Nat.card I)) ≃ I :=
    Equiv.ulift.trans (Finite.equivFin I).symm
  let U₀ : Scheme.OpenCover.{u} X := Scheme.Cover.mkOfCovers
    (ULift.{u} (Fin (Nat.card I))) (fun _ ↦ Spec (.of k)) (fun i ↦ j (e i)) (by
      intro x
      obtain ⟨i, y, hy⟩ := hc x
      exact ⟨e.symm i, y, by simpa using hy⟩)
  exact
    { I₀ := ULift.{u} (Fin (Nat.card I))
      X := fun _ ↦ Spec (.of k)
      f := fun i ↦ j (e i)
      mem₀ := Scheme.zariskiPrecoverage_le_propQCPrecoverage _ U₀.mem₀ }

private theorem pointModelInverse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (hM : IsConstantModelConstructible Λ (Spec (.of k)) M) :
    ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
        Nonempty (M ≅ ((upperStarFromPoint (Spec (.of k))).mapMod Λ).obj P) := by
  obtain ⟨P, hP, eP⟩ := (point_constant_model_global_iff Λ k M).mp hM
  exact ⟨P, hP, eP.map Iso.symm⟩

omit [IsAlgClosed k] in
private theorem pointCoverData_X {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x) (i : ULift.{u} (Fin (Nat.card I))) :
    (pointCoverData k I j hc).X i = Spec (.of k) := rfl

omit [IsAlgClosed k] in
private theorem pointCoverData_f {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x) (i : ULift.{u} (Fin (Nat.card I))) :
    (eqToIso (pointCoverData_X k I j hc i)).hom ≫
      j ((Equiv.ulift.trans (Finite.equivFin I).symm) i) =
        (pointCoverData k I j hc).f i := by
  change (𝟙 (Spec (.of k))) ≫ j _ = j _
  exact Category.id_comp _

private theorem pointModelAlongFactor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (j : Spec (.of k) ⟶ X) (f : Y ⟶ X) (e : Y ≅ Spec (.of k))
    (hf : e.hom ≫ j = f)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ (Spec (.of k))
      ((CondensedRing.upperStar Λ j).obj M)) :
    ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
        Nonempty ((CondensedRing.upperStar Λ f).obj M ≅
          ((upperStarFromPoint Y).mapMod Λ).obj P) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := pointModelInverse k Λ _ hM
  refine ⟨P, hP, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun q ↦ (CondensedRing.upperStar Λ q).obj M) hf.symm) ≪≫
    (CondensedRing.upperStarComp Λ e.hom j).app M ≪≫
    (CondensedRing.upperStar Λ e.hom).mapIso eP ≪≫
    (CondensedRing.upperStarFromPointModComp Λ e.hom).app P

private theorem localModelIntro
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : ∀ i : U.I₀,
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ P ∧
          Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj M ≅
            ((upperStarFromPoint (U.X i)).mapMod Λ).obj P)) :
    HasFiniteConstantLocalModel Λ X M := ⟨U, hU⟩

omit [IsAlgClosed k] in
private theorem existsPointCover {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x) :
    ∃ (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (e : U.I₀ ≃ I)
      (s : ∀ i, U.X i ≅ Spec (.of k)), ∀ i, (s i).hom ≫ j (e i) = U.f i := by
  classical
  exact ⟨pointCoverData k I j hc, Equiv.ulift.trans (Finite.equivFin I).symm,
    (fun i ↦ eqToIso (pointCoverData_X k I j hc i)), pointCoverData_f k I j hc⟩

private theorem pointCoverLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ t : I, IsConstantModelConstructible Λ (Spec (.of k))
      ((CondensedRing.upperStar Λ (j t)).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, e, s, hs⟩ := existsPointCover k I j hc
  apply localModelIntro Λ U M
  intro i
  exact pointModelAlongFactor k Λ (j (e i)) (U.f i) (s i) (hs i) M (hM (e i))


private theorem pointCoverLocalModelFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (j : ∀ _ : I, Spec (.of k) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : ∀ x : X, ∃ i y, j i y = x)
    (R : ∀ _ : I,
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k))))
    (hR : ∀ i, R i = CondensedRing.upperStar Λ (j i))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i, IsConstantModelConstructible Λ (Spec (.of k)) ((R i).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  apply pointCoverLocalModel k I Λ j hc M
  intro i
  rw [← hR i]
  exact hM i

private theorem localModelOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem constructibleOfLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) : IsConstantModelConstructible Λ X M := by
  classical
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hqc]
  refine ⟨Scheme.Stratification.trivial X, fun _ ↦ ?_⟩
  exact localModelOfIso Λ ((upperStarId Λ X).app M).symm hM

private def restrictionSquareIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V U Y X : Scheme.{u}}
    (a : V ⟶ U) (b : U ⟶ X) (c : V ⟶ Y) (d : Y ⟶ X) (h : a ≫ b = c ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ b).obj M) ≅
      (CondensedRing.upperStar Λ c).obj ((CondensedRing.upperStar Λ d).obj M) :=
  ((CondensedRing.upperStarComp Λ a b).app M).symm ≪≫
    eqToIso (congrArg (fun q ↦ (CondensedRing.upperStar Λ q).obj M) h) ≪≫
    (CondensedRing.upperStarComp Λ c d).app M

private theorem constructiblePullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ f).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hX, if_pos hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  let T := S.pullback f
  refine ⟨T, fun i ↦ ?_⟩
  let q : T.domain i ⟶ S.domain i := pullback.fst (S.immersion i) f
  have comm : q ≫ S.immersion i = T.immersion i ≫ f := pullback.condition
  exact localModelOfIso Λ
    (restrictionSquareIso Λ (T.immersion i) f q (S.immersion i) comm.symm M).symm
    (pullback_finiteConstantLocalModel Λ q _ (hS i))

private theorem constructiblePullbackFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : F = CondensedRing.upperStar Λ f)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X (F.obj M) := by
  subst F
  exact constructiblePullback Λ f M hM

/-- Finite-constant-model constructibility on the boundary is componentwise.
Source: blueprint local boundary duality, Step 5, clopen constructible gluing.
Proof: pull back a constructible stratification and its finite constant models
along every coprojection. Conversely the coprojections form a pro-etale cover.
The global finite presented condensed model of each point restriction witnesses
a finite local model on that cover. The trivial stratification then gives
constructibility. Empty covers include the empty boundary.
(blueprint: lem-a1-condensed-boundary-constructibility) -/
theorem condensed_boundary_constructible_iff (M : CondensedBoundaryMod ℓ k I) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) M ↔
      ∀ t : I, IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ)
        (point k).left ((condensedBoundaryRestriction ℓ k I t).obj M) := by
  classical
  constructor
  · intro hM t
    exact constructiblePullbackFunctor (Profinite.padicAlgClRingObj.{u} ℓ)
      (X := (point k).left) (Y := condensedPointBoundary k I)
      (Sigma.ι (fun _ : I ↦ (point k).left) t)
      (condensedBoundaryRestriction ℓ k I t) rfl M hM
  · intro hM
    apply constructibleOfLocalModel (Profinite.padicAlgClRingObj.{u} ℓ) M
    exact pointCoverLocalModelFunctor k I (Profinite.padicAlgClRingObj.{u} ℓ)
      (X := condensedPointBoundary k I) (Sigma.ι (fun _ : I ↦ (point k).left))
      ((sigmaOpenCover (fun _ : I ↦ (point k).left)).exists_eq)
      (condensedBoundaryRestriction ℓ k I) (fun _ ↦ rfl) M hM

end AlgebraicGeometry.ProEtale.CondensedRing
