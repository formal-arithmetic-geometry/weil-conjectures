/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.TorIndependentKFlatResolutionTensor
import WeilConjectures.Algebra.Homology.FlatScalarExtensionHomologyAdjunct
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Tor-independent localized tensor comparison on left K-flat complexes

## References

* Stacks Project, More on Algebra, Section 06Y5 and Tag 06Y6
* Stacks Project, Tag 08IB, the Tor-independent affine calculation
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- Tor independence of A and B over R suffices for the canonical localized
comparison on any A-K-flat complex. Only flatness of the final E-algebra is needed,
where E = A tensor over R B. The cohomology model may be any model with its recorded
universal counit and comparison equations; this asserts invertibility of its specified
map, not the existence of an unrelated isomorphism. -/
theorem localizedComparison_isIso_of_torIndependent_kFlat
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (hD : Module.Flat (A ⊗[R] B) D)
    (M : BaseDerivedTensorCohomologyModel R A B Q D) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by
  classical
  have (N : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  let X := (((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q)
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
  let P := Λ.resolutionFunctor.obj X
  let s := Λ.resolutionNatTrans.app X
  have hs : QuasiIso s := inferInstance
  have hP := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le X
  have hPa : ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic := by
    intro L hL
    have ht := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
      ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
      ((HomotopyCategory.quotient _ _).obj L)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 ht.2
  have hp := scalarExtensionCounit_isIso_of_kFlat (algebraMap R B) P hPa
    M.derived M.counit M.universal
  have ht := scalarExtension_quasiIso_of_torIndependent_kFlat hTor Q hK P hP s hs
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  have : IsIso (DerivedCategory.Q.map
      (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ht
  have hc : IsIso (M.counit.app ((HomotopyCategory.quotient _ _).obj X)) := by
    have hsource : IsIso ((DerivedCategory.Qh ⋙ M.derived).map
        ((HomotopyCategory.quotient _ _).map s)) := by
      have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map s)) :=
        (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) s).2 inferInstance
      dsimp only [Functor.comp_map]
      infer_instance
    have htarget : IsIso
        (((extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh).map ((HomotopyCategory.quotient _ _).map s)) := by
      dsimp only [Functor.comp_map, Functor.mapHomotopyCategory_map]
      exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _)
        (((extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map s)).2
        inferInstance
    have hn := M.counit.naturality ((HomotopyCategory.quotient _ _).map s)
    dsimp only [Functor.id_obj] at hn
    have hi : IsIso ((DerivedCategory.Qh ⋙ M.derived).map
        ((HomotopyCategory.quotient _ _).map s) ≫
          M.counit.app ((HomotopyCategory.quotient _ _).obj X)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.Qh ⋙ M.derived).map ((HomotopyCategory.quotient _ _).map s)) _
  have hcomparison : ∀ i : ℤ, IsIso (M.comparison i) := by
    intro i
    let F := restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let C := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    have hi : IsIso (F.map (M.comparison i) ≫ ((C.sc i).mapHomologyIso F).inv) := by
      rw [M.comparison_eq i]
      infer_instance
    have : IsIso (F.map (M.comparison i)) := (isIso_comp_right_iff _ _).mp hi
    exact isIso_of_reflects_iso (M.comparison i) F
  intro i
  have := hcomparison i
  let adj := extendRestrictScalarsAdj (algebraMap (A ⊗[R] B) D)
  let t := HomologicalComplex.homologyMap M.ordinaryToLocalized i ≫
    (((((extendScalars ((algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q).sc i
      ).mapHomologyIso (restrictScalars (algebraMap (A ⊗[R] B) D))).hom
  have ht : IsIso ((adj.homEquiv _ _).symm t) :=
    flatScalarExtensionHomologyAdjunct_isIso
      (algebraMap A (A ⊗[R] B)) (algebraMap (A ⊗[R] B) D) rfl hD Q
      M.ordinaryToLocalized M.ordinaryToLocalized_tmul i
  have hloc : M.localizedComparison i =
      (extendScalars (algebraMap (A ⊗[R] B) D)).map (M.comparison i) ≫
        (adj.homEquiv _ _).symm t := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    dsimp only [HomologicalComplex.homology] at *
    rw [Equiv.apply_symm_apply]
    change adj.unit.app _ ≫ _ = _
    exact M.localized_eq i
  rw [hloc]
  infer_instance

end ModuleCat
