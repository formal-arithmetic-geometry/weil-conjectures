/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.WeilSheaf.DerivedHom
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Native Hom and source quasi-isomorphisms

Source: Stacks Tag 0A95, specialized to the native coefficient modules and Weil structure.
The proof uses a flat separator and the signed source-cone comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
namespace NativeAux
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
open Mod
/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm


private noncomputable def tensorComponent (M N : Mod C R) :
    (Mod.tensorLeft N).obj M ≅ M ⊗ N :=
  HasColimit.isoOfNatIso
    (diagramIsoParallelPair ((Mod.tensorLeftDiagram R N).flip.obj M)) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitRelativeTensorCofork M N)

omit [MonoidalPreadditive C] in
private noncomputable def tensorIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun M ↦ tensorComponent M N) (by
    intro M M' f
    apply Mod.tensorLeft_obj_hom_ext
    simp only [Mod.comp_hom', Mod.tensorπ_map_assoc]
    rw [tensorComponent_π, ← Category.assoc, tensorComponent_π]
    exact (Mod.tensorObjπ_whiskerRight f).symm)

private lemma uncurry_add {P M N : Mod C R} (a b : P ⟶ (Mod.ihom M).obj N) :
    Mod.uncurryHom (a + b) = Mod.uncurryHom a + Mod.uncurryHom b := by
  simp only [Mod.uncurryHom, Mod.add_hom, MonoidalPreadditive.add_whiskerRight,
    Preadditive.add_comp]

private noncomputable def transposeAdd (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ (M ⟶ (Mod.ihom P).obj N) :=
  { Mod.transposeEquiv with
    map_add' := by
      intro a b
      apply Mod.uncurryHom_injective
      change Mod.uncurryHom (Mod.transpose (a + b)) =
        Mod.uncurryHom (Mod.transpose a + Mod.transpose b)
      rw [uncurry_add, Mod.uncurryHom_transpose, Mod.uncurryHom_transpose,
        Mod.uncurryHom_transpose, uncurry_add, Preadditive.comp_add] }

private noncomputable def homEquiv (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ ((Mod.tensorLeft P).obj M ⟶ N) :=
  (transposeAdd P M N).trans ((Mod.ihomAdjunction P).homAddEquiv M N).symm

private instance : (H (R := R)).Additive :=
  ⟨fun {_M _N} a b ↦ Mod.ihomMap_add a.unop b.unop⟩

private instance (M : (Mod C R)ᵒᵖ) : ((H (R := R)).obj M).Additive :=
  inferInstanceAs (Mod.ihom M.unop).Additive

end NativeAux


namespace NativeTransport
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasCountableProducts C] [HasCountableProducts D]
  (U : C ⥤ D) [U.Additive]
  [∀ n : ℤ, PreservesLimitsOfShape (Discrete (CochainComplex.HomComplex.Triplet n)) U]
  (HC : Cᵒᵖ ⥤ C ⥤ C) [HC.Additive] [∀ M, (HC.obj M).Additive]
  (HD : Dᵒᵖ ⥤ D ⥤ D) [HD.Additive] [∀ M, (HD.obj M).Additive]
  (e : ∀ M N, U.obj ((HC.obj (op M)).obj N) ≅ (HD.obj (op (U.obj M))).obj (U.obj N))
  (er : ∀ M N N' (f : N ⟶ N'), U.map ((HC.obj (op M)).map f) ≫ (e M N').hom =
    (e M N).hom ≫ (HD.obj (op (U.obj M))).map (U.map f))
  (el : ∀ M M' N (f : M' ⟶ M), U.map ((HC.map f.op).app N) ≫ (e M' N).hom =
    (e M N).hom ≫ (HD.map (U.map f).op).app (U.obj N))
set_option quotPrecheck false
local notation "Uc" => U.mapHomologicalComplex (.up ℤ)
include er el in
end NativeTransport


namespace NativeAux
open AlgebraicGeometry CategoryTheory.Endofunctor
attribute [local instance] Sheaf.symmetricCategory
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
set_option quotPrecheck false
local notation "U" => IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
local notation "Uc" => (U).mapHomologicalComplex (.up ℤ)
local notation "HW" => ProEtaleWeilSheaf.ihomBifunctor k₀ l X
local notation "HO" => H (C := Sheaf
  (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (WeilCoefficients l))
  (R := ProEtale.adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

end NativeAux

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.ProEtaleWeilSheaf
