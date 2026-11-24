/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Maps on module cohomology induced by scheme maps

## Implementation details

Nonnegative complexes are encoded by Mathlib's natural-number indexed complexes.
The choices in the resolution construction are bundled below, and their existence is
proved using injective resolutions and the global-sections quasi-isomorphism theorem.
The map itself is the induced horizontal map followed by the inverse of the
induced vertical map, transported through the standard resolution comparisons.

## References

* [Stacks, Cohomology of Sheaves, Tags 01F7, 01F8, 01FA, 01FB, 01EZ]
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

/-- Every natural-indexed cochain complex admits a quasi-isomorphism into a complex of
injectives (Stacks, Derived Categories, Tag 013K). -/
private theorem nat_complex_injective_resolution
    {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
    (A : CochainComplex C ℕ) :
    ∃ (B : CochainComplex C ℕ) (i : A ⟶ B),
      (∀ n : ℕ, Injective (B.X n)) ∧ QuasiIso i := by
  let e := ComplexShape.embeddingUpNat
  obtain ⟨L, i, hi, hL, hL0⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (A.extend e) 0
  have : QuasiIso i := hi
  have : L.IsStrictlySupported e := by
    constructor
    intro n hn
    apply CochainComplex.isZero_of_isStrictlyGE L 0 n (by
      by_contra h
      have hn0 : 0 ≤ n := by omega
      exact hn n.toNat (by simpa [e] using Int.toNat_of_nonneg hn0))
  let E := e.extendFunctor C
  let B := L.truncGE' e
  let j : A ⟶ B := E.preimage (i ≫ HomologicalComplex.πTruncGE L e)
  have hj : QuasiIso (HomologicalComplex.extendMap j e) := by
    change QuasiIso (E.map j)
    dsimp [j]
    rw [E.map_preimage]
    infer_instance
  refine ⟨B, j, ?_, (HomologicalComplex.quasiIso_extendMap_iff j e).1 hj⟩
  intro n
  have : Injective ((L.restriction e).X n) := hL (e.f n)
  have : IsIso ((L.restrictionToTruncGE' e).f n) := by infer_instance
  exact Injective.of_iso (asIso ((L.restrictionToTruncGE' e).f n)) inferInstance

/-- An augmentation map into a termwise injective complex extends along the injective
resolution `J` (Stacks, Derived Categories, Tag 013P). -/
private theorem lift_to_nat_injectives
    {C : Type*} [Category* C] [Abelian C] {G : C}
    (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n)) (γ : G ⟶ K.X 0)
    (hγ : γ ≫ K.d 0 1 = 0) :
    ∃ β : J.cocomplex ⟶ K, J.ι.f 0 ≫ β.f 0 = γ := by
  let : ∀ n : ℕ, Injective (K.X n) := hK
  let g₀ : J.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru γ (J.ι.f 0)
  have hg₀ : J.ι.f 0 ≫ g₀ = γ := Injective.comp_factorThru _ _
  let g₁ := J.exact₀.descToInjective (g₀ ≫ K.d 0 1) (by
    rw [← Category.assoc, hg₀, hγ])
  have hg₁ : J.cocomplex.d 0 1 ≫ g₁ = g₀ ≫ K.d 0 1 :=
    J.exact₀.comp_descToInjective _ _
  let β := CochainComplex.mkHom J.cocomplex K g₀ g₁ hg₁.symm
    (fun n ⟨g, g', w⟩ ↦
      ⟨(J.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2)) (by
          rw [← Category.assoc, ← w, Category.assoc, K.d_comp_d, comp_zero]),
        ((J.exact_succ n).comp_descToInjective _ _).symm⟩)
  exact ⟨β, hg₀⟩

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport of the integer-indexed sections theorem through extension by zero
(Stacks, Cohomology of Sheaves, Tags 01FB and 01EZ). -/
private theorem nat_quasiIso_globalSections_pushforward_injectives
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : CochainComplex X.Modules ℕ) (K : CochainComplex Y.Modules ℕ)
    (hA : ∀ n : ℕ, Injective (A.X n))
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ K)
    (hl : QuasiIso l) :
    QuasiIso (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map l) := by
  let e := ComplexShape.embeddingUpNat
  let : ∀ n : ℕ, Injective (A.X n) := hA
  let : ∀ n : ℕ, Injective (K.X n) := hK
  have : QuasiIso l := hl
  let l' := (A.mapExtendIso e (pushforward h)).hom ≫ HomologicalComplex.extendMap l e
  have hl' : QuasiIso l' := by dsimp [l']; infer_instance
  obtain ⟨_, hΓ⟩ := quasiIso_globalSections_pushforward_injectives h
    (A.extend e) (K.extend e) (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn) l' hl'
  let Γ := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}
  have : Γ.Additive := inferInstanceAs
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙ forget₂ _ AddCommGrpCat.{u}).Additive
  have : Γ.PreservesZeroMorphisms := inferInstance
  have hΓ' : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map l') := hΓ
  have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap l e)) := by
    have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (A.mapExtendIso e (pushforward h)).hom ≫
          (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap l e)) := by
      rw [← Functor.map_comp]
      exact hΓ'
    exact quasiIso_of_comp_left
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (A.mapExtendIso e (pushforward h)).hom) _
  let P := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A
  have hext : QuasiIso (HomologicalComplex.extendMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map l) e) := by
    apply quasiIso_of_arrow_mk_iso
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap l e))
    exact Arrow.isoMk (P.mapExtendIso e Γ) (K.mapExtendIso e Γ)
      ((e.mapExtendFunctorNatIso Γ).hom.naturality l).symm
  exact (HomologicalComplex.quasiIso_extendMap_iff _ e).1 hext

/-- The canonical comparison of global sections, pinned to restriction along
`h⁻¹(Y) = X`, as an isomorphism of complexes (Stacks, Tag 01FB). -/
private def pushforward_sections_iso {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : CochainComplex X.Modules ℕ) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ≅
    ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A) := by
  refine (HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (presheaf (A.X n)).mapIso
      (eqToIso (by simp) : op (h ⁻¹ᵁ (⊤ : Y.Opens)) ≅ op (⊤ : X.Opens))) ?_).symm
  intro n m _
  change (presheaf (A.X n)).map _ ≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (A.d n m)).app _ =
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (A.d n m)).app _ ≫
      (presheaf (A.X m)).map _
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (A.d n m)).naturality _

/-- Choices for the construction of the cohomology map of an `h`-map. The comparison `a`
is the identity on sections, using `h⁻¹(Y) = X` (Stacks, Tag 01FB). -/
structure ModuleCohomologyFMapData {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : G ⟶ (pushforward h).obj F) where
  I : InjectiveResolution F
  J : InjectiveResolution G
  K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ
  injective : ∀ n : ℕ, Injective (K.X n)
  lambda : ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ K
  quasiIso : QuasiIso lambda
  β : J.cocomplex ⟶ K
  compatible : J.ι.f 0 ≫ β.f 0 = φ ≫ (pushforward h).map (I.ι.f 0) ≫ lambda.f 0
  a : ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  sections : ∀ n : ℕ, a.inv.f n = (Scheme.Modules.presheaf (I.cocomplex.X n)).map
    (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op
  invertible : ∀ p : ℕ, IsIso ((HomologicalComplex.homologyFunctor
    AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map (a.hom ≫
      ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map lambda))

/-- The resolution choices needed for the construction of the cohomology map exist
(Stacks, Tags 01FB and 01EZ). -/
theorem moduleCohomologyFMapData_nonempty {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (F : SheafOfModules.{u} X.ringCatSheaf)
    (φ : G ⟶ (pushforward h).obj F) : Nonempty (ModuleCohomologyFMapData h G F φ) := by
  have : EnoughInjectives X.Modules := inferInstance
  have : EnoughInjectives Y.Modules := inferInstance
  let I := injectiveResolution F
  let J := injectiveResolution G
  let P := pushforward h
  have : P.Additive := inferInstanceAs (pushforward h).Additive
  obtain ⟨K, l, hK, hl⟩ := nat_complex_injective_resolution
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  let γ := φ ≫ P.map (I.ι.f 0) ≫ l.f 0
  have hγ : γ ≫ K.d 0 1 = 0 := by
    dsimp [γ]
    rw [Category.assoc, Category.assoc, l.comm]
    change φ ≫ P.map (I.ι.f 0) ≫ P.map (I.cocomplex.d 0 1) ≫ l.f 1 = 0
    rw [← Functor.map_comp_assoc, I.ι_f_zero_comp_complex_d, Functor.map_zero]
    simp
  obtain ⟨β, hβ⟩ := lift_to_nat_injectives J K hK γ hγ
  let a := pushforward_sections_iso h I.cocomplex
  have : QuasiIso (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map l) :=
    nat_quasiIso_globalSections_pushforward_injectives h I.cocomplex K
      (fun n ↦ inferInstance) hK l hl
  refine ⟨{
    I := I
    J := J
    K := K
    injective := hK
    lambda := l
    quasiIso := hl
    β := β
    compatible := hβ
    a := a
    sections := ?_
    invertible := ?_ }⟩
  · intro n
    rfl
  · intro p
    have : IsIso a.hom := inferInstance
    have : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map
          (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
            forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map l)) := by
      change IsIso (HomologicalComplex.homologyMap _ p)
      infer_instance
    rw [Functor.map_comp]
    infer_instance

/-- The map of cohomology groups computed from a system of choices `D`:
H(Γβ) followed by H(μ) inverse, with `μ = a ≫ Γ(Y, λ)`, transported through the
resolution comparisons `isoRightDerivedObj` and the forgetful homology comparisons
(Stacks, Tags 01FA and 01FB). -/
def ModuleCohomologyFMapData.map {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :=
  (forget₂ _ AddCommGrpCat.{u}).map
      (D.J.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Y.toRingedSpace) p).hom ≫
    (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) ≫
    inv (I := D.invertible p) ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) p).map (D.a.hom ≫
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
            D.lambda)) ≫
    (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).hom ≫
    (forget₂ _ AddCommGrpCat.{u}).map
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).inv

/-- The map of cohomology groups of an `h`-map: H(Γβ) followed by H(μ) inverse, for a
system of choices whose existence is `moduleCohomologyFMapData_nonempty`
(Stacks, Tags 01FA and 01FB). -/
def moduleCohomologyFMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :=
  (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)).map p

/-- Pullback on module cohomology is the map of the tensor-pullback adjunction unit
(Stacks, Tag 01F7). -/
def moduleCohomologyPullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap h
    ((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app G) p

/-- Restriction on module cohomology is the map of the restriction-adjunction unit.
Its components are precisely restriction from V to V ∩ U (Stacks, Tags 01F7 and 00A1). -/
def moduleCohomologyRestriction {Y : Scheme.{u}} (U : Y.Opens)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p

/-- The edge map is the cohomology map of the identity on the direct image
(Stacks, Tag 01F7). -/
def moduleCohomologyEdgeMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    (F : SheafOfModules.{u} X.ringCatSheaf) (p : ℕ) :=
  moduleCohomologyFMap h (𝟙 ((pushforward h).obj F)) p

end AlgebraicGeometry.Scheme.Modules
