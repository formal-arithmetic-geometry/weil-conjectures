/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Derived square for a finite free chart model -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ (_ : (Modules.tensorPullback g).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        (Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback g)
  have h : E = Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hE (fun _ _ f ↦ hEmap f)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openPullbackIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        (Modules.overEquiv U).functor
    Nonempty (derivedPullback U.ι ≅ R.mapDerivedCategory) := by
  dsimp only
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    (Modules.overEquiv U).functor
  obtain ⟨a, ε, hL, _⟩ := tensorCounit U.ι
  have := hL
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction U.ι
  let θ : Modules.tensorPullback U.ι ≅ R :=
    adj.leftAdjointUniq (Modules.restrictAdjunction U.ι) ≪≫
      (Modules.overFunctorEquiv U).symm
  have : R.Additive := by dsimp [R]; infer_instance
  have : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let θh : (Modules.tensorPullback U.ι).mapHomotopyCategory (.up ℤ) ≅
      R.mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  let δ := Functor.isoWhiskerRight θh
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let α := R.mapDerivedCategoryFactorsh ≪≫ δ.symm
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    R.mapDerivedCategory α
  exact ⟨Functor.leftDerivedUnique R.mapDerivedCategory (derivedPullback U.ι)
    ε α.hom (HomotopyCategory.quasiIso _ (.up ℤ))⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open MonoidalCategory in
private theorem finiteFree_flat (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hf : ∃ n : ℕ, Nonempty (M ≅ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin n)))) :
    SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨n, ⟨e⟩⟩ := hf
  have hunit : SheafOfModules.IsFlat (SheafOfModules.unit
      (moduleRings Y.toRingedSpace)) :=
    (ObjectProperty.flat_of_tensorIso
      (MonoidalCategory.leftUnitor (𝟙_ (SheafOfModules.{u}
        (moduleRings Y.toRingedSpace))))).2
  have hfree := SheafOfModules.isFlat_coproduct Y.sheaf
    (fun _ : ULift.{u} (Fin n) ↦ SheafOfModules.unit (moduleRings Y.toRingedSpace))
    (fun _ ↦ hunit)
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hfree

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Nested exact restriction and localization comparisons need more elaboration steps.
/-- Compare the restricted derived square with its explicit termwise tensor model.
Source: Stacks Project, Tags 06YD, 06YJ and 0D5S.
Proof: Finite free terms are flat, so bounded-above A and B are K-flat (06YD).
The single left-derived counit for tensor pullback on the inverse-image open is
invertible on both complexes (06YJ), and naturality gives their derived square.
Compose the given square with the natural derived composition comparisons
along the cartesian open square (0D5S). Exact restriction identifies derived pullback along
an open immersion with restriction. Transport the resulting square through the
exact inverse of the module-site equivalence, whose termwise functor factors through
Q. This gives the displayed square in the derived category of the localized site.
The standard localization used here is canonically equivalent to any chosen one;
no choice of an arbitrary resolution is involved. Empty opens, zero ranks and zero
complexes use the same counit and exact equivalences.
(blueprint: lem-sc-bottom-free-chain-derived-square). -/
theorem bottomFreeChain_derived_square
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (X Z : schemeDerivedCategory T) (f : X ⟶ Z)
    (W : T.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ)
    (hAbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i))
    (hBbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i))
    (hAfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hBfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (α : A ⟶ B)
    (eA : (derivedPullback W.ι).obj X ≅ DerivedCategory.Q.obj A)
    (eB : (derivedPullback W.ι).obj Z ≅ DerivedCategory.Q.obj B)
    (hsquare : (derivedPullback W.ι).map f ≫ eB.hom =
      eA.hom ≫ DerivedCategory.Q.map α)
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    let V := g ⁻¹ᵁ W
    let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
      (Modules.overEquiv V).inverse
    ∀ hF : F.Additive,
      letI := hF
      letI := HasDerivedCategory.standard
        (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V))
      let R := SheafOfModules.overFunctor.{u} (moduleRings T'.toRingedSpace) V
      let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A
      let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
      let β := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α
      ∃ (eP : R.mapDerivedCategory.obj ((derivedPullback g).obj X) ≅
          DerivedCategory.Q.obj P)
        (eQ : R.mapDerivedCategory.obj ((derivedPullback g).obj Z) ≅
          DerivedCategory.Q.obj Q),
        R.mapDerivedCategory.map ((derivedPullback g).map f) ≫ eQ.hom =
          eP.hom ≫ DerivedCategory.Q.map β := by
  classical
  dsimp only
  intro hF
  let := hF
  let V := g ⁻¹ᵁ W
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V))
  let R := SheafOfModules.overFunctor.{u} (moduleRings T'.toRingedSpace) V
  let E : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V) :=
    (Modules.overEquiv V).inverse
  let h := g.resLE W V (le_refl V)
  let H : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.tensorPullback h
  let F := H ⋙ E
  have : E.Additive := by dsimp [E]; infer_instance
  have : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  have : PreservesFiniteColimits E := by dsimp [E]; infer_instance
  have : R.Additive := by dsimp [R]; infer_instance
  obtain ⟨hH, ε, hL, hK⟩ := tensorCounit h
  let := hH
  have hKA := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    W.toScheme.toRingedSpace A hAbounded (fun i ↦ finiteFree_flat _ _ (hAfree i))
  have hKB := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    W.toScheme.toRingedSpace B hBbounded (fun i ↦ finiteFree_flat _ _ (hBfree i))
  have hεA := hK A hKA
  have hεB := hK B hKB
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) (.up ℤ)
  let η : DerivedCategory.Q ⋙ derivedPullback h ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback h) ≫
      Functor.whiskerLeft q ε ≫
      Functor.whiskerRight (H.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  let ψ : DerivedCategory.Q ⋙ (derivedPullback h ⋙ E.mapDerivedCategory) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight η E.mapDerivedCategory ≫
      Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ))
        E.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl F) (.up ℤ)).hom DerivedCategory.Q
  have hψA : IsIso (ψ.app A) := by
    dsimp only [ψ, η, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have hψB : IsIso (ψ.app B) := by
    dsimp only [ψ, η, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨ψ, hψA, hψB⟩ :
      ∃ ψ : DerivedCategory.Q ⋙ (derivedPullback h ⋙ E.mapDerivedCategory) ⟶
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
        IsIso (ψ.app A) ∧ IsIso (ψ.app B) := ⟨ψ, hψA, hψB⟩
  obtain ⟨oV⟩ := openPullbackIso T' V
  let e : SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V) ≌
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.overEquiv V
  let eD := e.mapDerivedCategory
  have oV' : derivedPullback V.ι ≅ R.mapDerivedCategory ⋙ eD.functor :=
    oV ≪≫ Functor.mapDerivedCategoryCompIso R e.functor
  have rV : R.mapDerivedCategory ≅ derivedPullback V.ι ⋙ E.mapDerivedCategory :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft R.mapDerivedCategory eD.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight oV'.symm E.mapDerivedCategory
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition.{u, w}
  have d : derivedPullback g ⋙ R.mapDerivedCategory ≅
      derivedPullback W.ι ⋙ (derivedPullback h ⋙ E.mapDerivedCategory) :=
    Functor.isoWhiskerLeft (derivedPullback g) rV ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (c V.ι g ≪≫
          eqToIso (congrArg (fun k ↦ derivedPullback k)
            (Hom.resLE_comp_ι g (le_refl V)).symm) ≪≫
          (c h W.ι).symm) E.mapDerivedCategory ≪≫
      Functor.associator _ _ _
  let L := derivedPullback h ⋙ E.mapDerivedCategory
  refine ⟨d.app X ≪≫ L.mapIso eA ≪≫ asIso (ψ.app A),
    d.app Z ≪≫ L.mapIso eB ≪≫ asIso (ψ.app B), ?_⟩
  change (derivedPullback g ⋙ R.mapDerivedCategory).map f ≫
      (d.hom.app Z ≫ L.map eB.hom ≫ ψ.app B) =
    (d.hom.app X ≫ L.map eA.hom ≫ ψ.app A) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map α)
  rw [← Category.assoc, d.hom.naturality]
  simp only [Category.assoc]
  change d.hom.app X ≫ L.map ((derivedPullback W.ι).map f) ≫
      L.map eB.hom ≫ ψ.app B = _
  have hn : L.map (DerivedCategory.Q.map α) ≫ ψ.app B =
      ψ.app A ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map α) :=
    ψ.naturality α
  calc
    _ = d.hom.app X ≫ L.map ((derivedPullback W.ι).map f ≫ eB.hom) ≫ ψ.app B := by
      rw [L.map_comp ((derivedPullback W.ι).map f) eB.hom]
      simp only [Category.assoc]
    _ = d.hom.app X ≫ L.map (eA.hom ≫ DerivedCategory.Q.map α) ≫ ψ.app B := by
      rw [hsquare]
    _ = d.hom.app X ≫ (L.map eA.hom ≫ L.map (DerivedCategory.Q.map α)) ≫
        ψ.app B :=
      congrArg (fun k ↦ d.hom.app X ≫ k ≫ ψ.app B)
        (L.map_comp eA.hom (DerivedCategory.Q.map α))
    _ = d.hom.app X ≫ L.map eA.hom ≫ (L.map (DerivedCategory.Q.map α) ≫
        ψ.app B) := by simp only [Category.assoc]
    _ = d.hom.app X ≫ L.map eA.hom ≫ (ψ.app A ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map α)) :=
      congrArg (fun k ↦ d.hom.app X ≫ L.map eA.hom ≫ k) hn
    _ = _ := by rfl



end AlgebraicGeometry.Scheme
