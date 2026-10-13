/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Transport of a finite-free local model along a scheme morphism
Source: Stacks Project, Tags 06YD, 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-finite-free-residue-model-pullback). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem pullback_Q_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := Y.sheaf) P) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback g)
  have h : F = Modules.tensorPullback g := CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
  subst F
  have : (Modules.tensorPullback g).Additive := hFadd
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
  let η := (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)
  exact ⟨(derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso
      (((Modules.tensorPullback g).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app P)⟩

private theorem openRestriction_iso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) (E : schemeDerivedCategory X) :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    Nonempty (R.mapDerivedCategory.obj E ≅ (derivedPullback U.ι).obj E) := by
  classical
  dsimp only
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
  let G := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := X.sheaf) G
  have : QuasiIso s := hs
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  obtain ⟨cmp⟩ := pullback_Q_iso U.ι P hP
  have : (Modules.pullback U.ι).Additive := Modules.instAdditivePullback U.ι
  let η := Modules.overFunctorEquiv U ≪≫ Modules.restrictFunctorIsoPullback U.ι
  exact ⟨R.mapDerivedCategory.mapIso eP.symm ≪≫ R.mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex η (.up ℤ)).app P) ≪≫
    cmp.symm ≪≫ (derivedPullback U.ι).mapIso eP⟩

private theorem free_flat (X : Scheme.{u}) (n : ℕ) :
    SheafOfModules.IsFlat (SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n))) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed X.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  exact (ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)).2


/-- A bounded-above free model on an open site pulls back locally with the same term ranks.
Source: Stacks Project, Tags 06YD and 06YJ, termwise flat pullback;
Tag 0D5S, derived composition; Tag 08DW, open restriction.
(blueprint: lem-sc-finite-free-residue-model-pullback).

Proof: Take U to be the inverse image of V in T. The point condition puts t
in U. Factor U.toScheme -> S through V.toScheme. Transport K from the site
over V to the module category on V.toScheme by the open-site equivalence.
This exact equivalence preserves free terms and zero objects. Every free
term is flat, so the bounded-above flat-complex counit computes its derived
pullback termwise. Tensor pullback preserves free sheaves of a fixed rank
and zero terms, hence the upper bound and the function n of term ranks.
Compose the counit with the given representing isomorphism and derived
composition to obtain the displayed representing isomorphism. The argument
uses neither Tor amplitude nor any cohomology rank hypothesis. The inverse
image can be empty, but then there is no point t satisfying the condition;
zero ranks yield zero free terms and are preserved by the same functors. -/
theorem finiteFreeResidueModel_pullback
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ V : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (E : schemeDerivedCategory S) (V : S.Opens)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V)) ℤ)
    (n : ℤ → ℕ)
    (hbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i))
    (hrank : ∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over V) (ULift.{u} (Fin (n i)))))
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K))
    (T : Scheme.{u}) (h : T ⟶ S) (t : T) (ht : h t ∈ V) :
    ∃ U : T.Opens, t ∈ U ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (P.X i)) ∧
        (∀ i : ℤ, Nonempty (P.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin (n i))))) ∧
        Nonempty ((derivedPullback U.ι).obj ((derivedPullback h).obj E) ≅
          DerivedCategory.Q.obj P) := by
  classical
  let U := h ⁻¹ᵁ V
  let f := h.resLE V U le_rfl
  let A : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Modules.overEquiv V).functor
  let RY := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) V
  let P0 := (A.mapHomologicalComplex (.up ℤ)).obj K
  let F : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.pullback f
  have : F.Additive := Modules.instAdditivePullback f
  let P := (F.mapHomologicalComplex (.up ℤ)).obj P0
  have hP0rank (i : ℤ) : Nonempty (P0.X i ≅ SheafOfModules.free
      (R := moduleRings V.toScheme.toRingedSpace) (ULift.{u} (Fin (n i)))) :=
    ⟨A.mapIso (hrank i).some ≪≫
      (SheafOfModules.mapFreeIso A (ULift.{u} (Fin (n i)))
        (Modules.overEquivFunctorObjUnitIso V)).symm⟩
  obtain ⟨c, hc⟩ := hbounded
  have hP0bound : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (P0.X i) :=
    ⟨c, fun i hi ↦ A.map_isZero (hc i hi)⟩
  have hP0flat : ∀ i : ℤ, SheafOfModules.IsFlat (P0.X i) := by
    intro i
    let := SheafOfModules.monoidalCategory V.toScheme.sheaf
    exact (exactFunctor _ _).prop_of_iso
      ((MonoidalCategory.curriedTensor _).flip.mapIso (hP0rank i).some.symm)
      (free_flat V.toScheme (n i))
  obtain ⟨q⟩ := pullback_Q_iso f P0
    (CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      V.toScheme.toRingedSpace P0 hP0bound hP0flat)
  obtain ⟨θ⟩ := derivedPullback_openRestriction_iso_universes h U V le_rfl
  obtain ⟨eOpen⟩ := openRestriction_iso T U ((derivedPullback h).obj E)
  let e0 : (RY ⋙ A).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P0 :=
    ((Functor.mapDerivedCategoryCompIso RY A).app E) ≪≫
      A.mapDerivedCategory.mapIso hmodel.some ≪≫ A.mapDerivedCategoryFactors.app K
  let eP : (derivedPullback U.ι).obj ((derivedPullback h).obj E) ≅
      DerivedCategory.Q.obj P :=
    eOpen.symm ≪≫ θ.app E ≪≫ (derivedPullback f).mapIso e0 ≪≫ q
  refine ⟨U, ht, P, ⟨c, fun i hi ↦ F.map_isZero (A.map_isZero (hc i hi))⟩, ?_, ⟨eP⟩⟩
  intro i
  exact ⟨F.mapIso (hP0rank i).some ≪≫ Modules.pullbackFreeIso f (ULift.{u} (Fin (n i)))⟩

end AlgebraicGeometry.Scheme
