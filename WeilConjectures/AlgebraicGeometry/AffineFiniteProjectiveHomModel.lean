/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import WeilConjectures.Algebra.Homology.ModuleHomPrecompHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
import Mathlib.Data.Int.Interval
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
/-! # Finite-free preparation of the affine module Hom complex
Source: Stacks Project, Tags 064U and 0A6H, proof of clause (3)(a).
(blueprint: lem-sc-affine-finite-projective-hom-model).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CochainComplex
private noncomputable def modelMap {R : Type u} [CommRing R]
    {P P' N N' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P' ⟶ P) (b : N ⟶ N') :
    moduleHomComplex P N ⟶ moduleHomComplex P' N' where
  f n := ModuleCat.ofHom
    { toFun := fun f ↦ ((HomComplex.Cochain.ofHom a).comp f (zero_add n)).comp
        (HomComplex.Cochain.ofHom b) (add_zero n)
      map_add' := fun f g ↦ by simp
      map_smul' := fun r f ↦ by simp }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (HomComplex.δ_comp_ofHom _ b m).trans
      (congrArg (fun z ↦ z.comp (HomComplex.Cochain.ofHom b) (add_zero m))
        (HomComplex.δ_ofHom_comp a f m))
private lemma modelMap_id_apply {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    {N N' : CochainComplex (ModuleCat.{u} R) ℤ} (b : N ⟶ N') (n : ℤ)
    (f : (moduleHomComplex P N).X n) :
    (modelMap (𝟙 P) b).f n f = f.comp (HomComplex.Cochain.ofHom b) (add_zero n) := by
  change ((HomComplex.Cochain.ofHom (𝟙 P)).comp f (zero_add n)).comp
    (HomComplex.Cochain.ofHom b) (add_zero n) = _
  rw [HomComplex.Cochain.id_comp]
private lemma modelMap_quasiIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    {N N' : CochainComplex (ModuleCat.{u} R) ℤ} (b : N ⟶ N') [QuasiIso b] :
    QuasiIso (modelMap (𝟙 P) b) := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U]
  let f := (U.mapHomologicalComplex (.up ℤ)).map (modelMap (𝟙 P) b)
  refine ⟨fun n ↦ ?_⟩
  rw [quasiIsoAt_iff]
  let D := HomComplex.leftHomologyData P N n
  let D' := HomComplex.leftHomologyData P N' n
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f) D D' := default
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  have hk (z : HomComplex.Cocycle P N n) :
      γ.φK z = z.postcomp b := by
    apply HomComplex.Cocycle.ext
    have h := ConcreteCategory.congr_hom γ.commi z
    change (γ.φK z).val = (modelMap (𝟙 P) b).f n z.val at h
    exact h.trans (modelMap_id_apply P b n z.val)
  have hh (z : HomComplex.Cocycle P N n) :
      γ.φH (HomComplex.CohomologyClass.mk z) =
        HomComplex.CohomologyClass.mk (z.postcomp b) := by
    have h := ConcreteCategory.congr_hom γ.commπ z
    change γ.φH (HomComplex.CohomologyClass.mk z) =
      HomComplex.CohomologyClass.mk (γ.φK z) at h
    exact h.trans (congrArg HomComplex.CohomologyClass.mk (hk z))
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let e := HomComplex.CohomologyClass.homAddEquiv (K := P) (L := N) (n := n)
  let e' := HomComplex.CohomologyClass.homAddEquiv (K := P) (L := N') (n := n)
  have he (z : HomComplex.CohomologyClass P N n) :
      e' (γ.φH z) = e z ≫
        H.map ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b) := by
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [hh]
    change H.map (HomComplex.Cocycle.equivHomShift.symm (z.postcomp b)) = _
    rw [HomComplex.Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
    rfl
  have hbij : Function.Bijective (fun g : H.obj P ⟶ H.obj (N⟦n⟧) ↦
      g ≫ H.map ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b)) := by
    have : IsIso (DerivedCategory.Qh.map (H.map
        ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))) := by
      apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).2
      infer_instance
    have h₁ := IsKProjective.Qh_map_bijective P (H.obj (N⟦n⟧))
    have h₂ := IsKProjective.Qh_map_bijective P (H.obj (N'⟦n⟧))
    have h₃ : Function.Bijective
        (fun g : DerivedCategory.Qh.obj (H.obj P) ⟶
            DerivedCategory.Qh.obj (H.obj (N⟦n⟧)) ↦
          g ≫ DerivedCategory.Qh.map (H.map
            ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))) := by
      refine (Function.bijective_iff_has_inverse).2
        ⟨fun g ↦ g ≫ inv (DerivedCategory.Qh.map (H.map
          ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).map b))),
          ?_, ?_⟩
      · intro g; simp
      · intro g; simp
    apply (Function.Bijective.of_comp_iff' h₂ _).mp
    have eq : (DerivedCategory.Qh.map ∘ fun g : H.obj P ⟶ H.obj (N⟦n⟧) ↦
        g ≫ H.map ((CategoryTheory.shiftFunctor _ n).map b)) =
        (fun g ↦ g ≫ DerivedCategory.Qh.map
          (H.map ((CategoryTheory.shiftFunctor _ n).map b))) ∘ DerivedCategory.Qh.map := by
      funext g
      exact DerivedCategory.Qh.map_comp _ _
    rw [eq]
    exact h₃.comp h₁
  apply (Function.Bijective.of_comp_iff' e'.bijective _).mp
  change Function.Bijective (fun z : HomComplex.CohomologyClass P N n ↦ e' (γ.φH z))
  have eq : (fun z : HomComplex.CohomologyClass P N n ↦ e' (γ.φH z)) =
      (fun g ↦ g ≫ H.map ((CategoryTheory.shiftFunctor _ n).map b)) ∘ e := funext he
  rw [eq]
  exact hbij.comp e.bijective
private lemma modelPrecomp_quasiIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {P F : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKProjective] [F.IsKProjective]
    (f : F ⟶ P) [QuasiIso f] (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (moduleHomPrecomp N f) := by
  classical
  obtain ⟨e, rfl⟩ := (IsKProjective.quasiIso_iff f).1 inferInstance
  let e' : HomotopyEquiv (moduleHomComplex P N) (moduleHomComplex F N) :=
    { hom := moduleHomPrecomp N e.hom
      inv := moduleHomPrecomp N e.inv
      homotopyHomInvId := by
        let h := (moduleHomPrecomp_preserves_homotopies N e.homotopyInvHomId).choose
        simpa only [(moduleHomPrecomp_id_comp (P := F) (R := P) (L := F) N).1,
          (moduleHomPrecomp_id_comp N).2] using h
      homotopyInvHomId := by
        let h := (moduleHomPrecomp_preserves_homotopies N e.homotopyHomInvId).choose
        simpa only [(moduleHomPrecomp_id_comp (P := F) (R := P) (L := F) N).1,
          (moduleHomPrecomp_id_comp N).2] using h }
  exact homotopyEquivalences_le_quasiIso _ _ _
    e'.homotopyEquivalences_hom
private theorem moduleHomModelDerivedIso (R : Type u) [CommRing R]
    (P F L : CochainComplex (ModuleCat.{u} R) ℤ) (b a : ℤ)
    (hP : P.IsStrictlyLE b) (hF : F.IsStrictlyLE b) (hL : L.IsGE a)
    (hp : ∀ i, Module.Projective R (P.X i))
    (hf : ∀ i, Module.Projective R (F.X i))
    (f : F ⟶ P) (h : QuasiIso f) :
    ∃ g : moduleHomComplex P L ⟶ moduleHomComplex F (L.truncGE a), QuasiIso g := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
    HasDerivedCategory.standard (ModuleCat.{u} R)
  have : P.IsStrictlyLE b := hP
  have : F.IsStrictlyLE b := hF
  have : L.IsGE a := hL
  have : ∀ i, Projective (P.X i) := fun i ↦ by
    have := hp i
    infer_instance
  have : ∀ i, Projective (F.X i) := fun i ↦ by
    have := hf i
    infer_instance
  have : P.IsKProjective := isKProjective_of_projective P b
  have : F.IsKProjective := isKProjective_of_projective F b
  have : QuasiIso f := h
  let g₁ := moduleHomPrecomp L f
  let g₂ := modelMap (𝟙 F) (L.πTruncGE a)
  have : QuasiIso g₁ := modelPrecomp_quasiIso f L
  have : QuasiIso g₂ := modelMap_quasiIso F (L.πTruncGE a)
  exact ⟨g₁ ≫ g₂, quasiIso_comp _ _⟩
end CochainComplex
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory
attribute [local irreducible] homComplexFunctor homComplex homComplexπ homComplexIsLimit
private instance modelSheafify (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
private instance modelSheafifyOver (X : Scheme.{u}) (U : X.Opens) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := inferInstance
private instance modelLocallyBijective (X : Scheme.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
private instance modelLocallyBijectiveOver (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance
private noncomputable def finiteSupportProductIso
    {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
    (Z : C) (A : ℤ → C) (π : ∀ p, Z ⟶ A p) (hπ : IsLimit (Fan.mk Z π))
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (A p)) :
    (⨁ fun i : ULift.{u} {p : ℤ // p ∈ s} ↦ A i.down.val) ≅ Z := by
  classical
  let I := ULift.{u} {p : ℤ // p ∈ s}
  let B : I → C := fun p ↦ A p.down.val
  let V := ⨁ B
  let ρ (p : ℤ) : V ⟶ A p :=
    if h : p ∈ s then biproduct.π B ⟨⟨p, h⟩⟩ else 0
  have hρ : IsLimit (Fan.mk V ρ) := by
    refine Fan.IsLimit.mk _ (fun f ↦ biproduct.lift fun i : I ↦ f.proj i.down.val)
      ?_ ?_
    · intro f p
      by_cases h : p ∈ s
      · simp [ρ, h]
      · exact (hz p h).eq_of_tgt _ _
    · intro f m hm
      apply biproduct.hom_ext
      intro i
      simpa [ρ, i.down.property] using hm i.down.val
  exact hρ.conePointUniqueUpToIso hπ
private theorem finiteSupportProductQuasicoherent
    (X : Scheme.{u}) (Z : SheafOfModules.{u} X.ringCatSheaf)
    (A : ℤ → SheafOfModules.{u} X.ringCatSheaf)
    (π : ∀ p, Z ⟶ A p) (hπ : IsLimit (Fan.mk Z π))
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (A p))
    (hq : ∀ p, SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (A p)) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) Z := by
  classical
  let : HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let I := ULift.{u} {p : ℤ // p ∈ s}
  let B : I → SheafOfModules.{u} X.ringCatSheaf := fun p ↦ A p.down.val
  have (i : I) : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (B i) := hq _
  have hv : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (⨁ B) :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (biproduct.isoCoproduct B).symm (Scheme.Modules.isQuasicoherent_sigma B)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (finiteSupportProductIso Z A π hπ s hz) hv
private theorem boundedFiniteFreeHomQuasicoherent
    (X : Scheme.{u}) (E G : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (b a : ℤ)
    [E.IsStrictlyLE b] [G.IsStrictlyGE a]
    (he : ∀ i : ℤ, ∃ r : ℕ, Nonempty
      (E.X i ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))))
    (hg : ∀ i, SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (G.X i)) (n : ℤ) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((homComplex (R := X.sheaf) E G).X n) := by
  classical
  let : HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let A (p : ℤ) := SheafOfModules.homObj (R := X.sheaf) (E.X p) (G.X (p + n))
  apply finiteSupportProductQuasicoherent X _ A
    (fun p ↦ homComplexπ E G n p (p + n) rfl) (homComplexIsLimit E G n)
    (Finset.Icc (a - n) b)
  · intro p hp
    have hp' : ¬ (a - n ≤ p ∧ p ≤ b) := by simpa using hp
    by_cases h : b < p
    · exact (((SheafOfModules.homFunctor X.sheaf).flip.obj (G.X (p + n))).map_isZero
        ((E.isZero_of_isStrictlyLE b p h).op))
    · have hz := G.isZero_of_isStrictlyGE a (p + n) (by omega)
      rw [IsZero.iff_id_eq_zero,
        ← SheafOfModules.homObjMap_id (R := X.sheaf) (M := E.X p) (N := G.X (p + n)),
        hz.eq_of_tgt (𝟙 _) 0]
      apply SheafOfModules.hom_ext
      ext U φ
      rfl
  · intro p
    obtain ⟨r, ⟨e⟩⟩ := he p
    let I := ULift.{u} (Fin r)
    let f : A p ≅ ⨁ fun _ : I ↦ G.X (p + n) :=
      ((SheafOfModules.homFunctor X.sheaf).flip.obj (G.X (p + n))).mapIso e.symm.op ≪≫
        SheafOfModules.homObjFreeIso (G.X (p + n)) I
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (G.X (p + n)) := hg _
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso f.symm
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (biproduct.isoCoproduct (fun _ : I ↦ G.X (p + n))).symm
        (Scheme.Modules.isQuasicoherent_sigma _))
set_option backward.isDefEq.respectTransparency true
private noncomputable def topHomToHom (X : Scheme.{u})
    (M N : (SheafOfModules.{u} X.ringCatSheaf))
    (φ : (SheafOfModules.homObj (R := X.sheaf) M N).val.obj (op ⊤)) : M ⟶ N :=
  ⟨{ app V := φ.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))
     naturality {V W} f := by
       exact φ.naturality (Over.homMk f.unop :
         Over.mk (homOfLE (le_top : W.unop ≤ ⊤)) ⟶
           Over.mk (homOfLE (le_top : V.unop ≤ ⊤))).op }⟩
private lemma topHomToHom_naturality (X : Scheme.{u})
    {M M' N N' : (SheafOfModules.{u} X.ringCatSheaf)} (f : M' ⟶ M) (g : N ⟶ N')
    (φ : (SheafOfModules.homObj (R := X.sheaf) M N).val.obj (op ⊤)) :
    topHomToHom X M' N' ((SheafOfModules.homObjMap f g).val.app (op ⊤) φ) =
      f ≫ topHomToHom X M N φ ≫ g := rfl
private noncomputable def topHomEquiv (X : Scheme.{u})
    (M N : (SheafOfModules.{u} X.ringCatSheaf)) :
    (SheafOfModules.homObj (R := X.sheaf) M N).val.obj (op ⊤) ≃ (M ⟶ N) where
  toFun := topHomToHom X M N
  invFun f := (PresheafOfModules.restrictOver X.sheaf.obj ⊤).map f.val
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro W
    rfl
  right_inv f := rfl
-- Bundled global-section modules require transport across the Spec ring presentation.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def affineHomTopLinear (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) :
    (moduleSpecΓFunctor (R := .of R)).obj
      (SheafOfModules.homObj (R := (Spec (CommRingCat.of R)).sheaf)
      (tilde M) (tilde N)) →ₗ[R] (M ⟶ N) where
  toFun φ := (tilde.isoTop (R := .of R) M).hom ≫
    (moduleSpecΓFunctor (R := .of R)).map
      (topHomToHom (Spec (CommRingCat.of R)) (tilde M) (tilde N) φ) ≫
      (tilde.isoTop (R := .of R) N).inv
  map_add' φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (tilde.isoTop (R := .of R) N).inv.hom
      ((φ + ψ).app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of R)).Opens))))
        ((tilde.isoTop (R := .of R) M).hom m)) = _
    exact (tilde.isoTop (R := .of R) N).inv.hom.map_add _ _
  map_smul' r φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (tilde.isoTop (R := .of R) N).inv.hom
      ((r • φ).app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of R)).Opens))))
        ((tilde.isoTop (R := .of R) M).hom m)) =
      r • (tilde.isoTop (R := .of R) N).inv.hom
        (φ.app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of R)).Opens))))
          ((tilde.isoTop (R := .of R) M).hom m))
    exact (tilde.isoTop (R := .of R) N).inv.hom.map_smul r _
private theorem homCoordinates_bijective {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) (S : D ⥤ C) (η : 𝟭 C ≅ T ⋙ S) (ff : T.FullyFaithful)
    (M N : C) : Function.Bijective
      (fun f : T.obj M ⟶ T.obj N ↦ η.hom.app M ≫ S.map f ≫ η.inv.app N) := by
  have he (f : T.obj M ⟶ T.obj N) :
      η.hom.app M ≫ S.map f ≫ η.inv.app N = ff.preimage f := by
    have h := η.hom.naturality (ff.preimage f)
    dsimp only [Functor.id_map, Functor.comp_map] at h
    rw [ff.map_preimage] at h
    have h' := congrArg (fun k ↦ k ≫ η.inv.app N) h
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h'.symm
  have eq : (fun f : T.obj M ⟶ T.obj N ↦ η.hom.app M ≫ S.map f ≫ η.inv.app N) =
      ff.preimage := funext he
  rw [eq]
  exact ff.homEquiv.symm.bijective
private lemma homCoordinates_naturality {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) (S : D ⥤ C) (η : 𝟭 C ≅ T ⋙ S)
    {M M' N N' : C} (f : M' ⟶ M) (g : N ⟶ N') (φ : T.obj M ⟶ T.obj N) :
    η.hom.app M' ≫ S.map (T.map f ≫ φ ≫ T.map g) ≫ η.inv.app N' =
      f ≫ (η.hom.app M ≫ S.map φ ≫ η.inv.app N) ≫ g := by
  have hf := η.hom.naturality f
  have hg := η.inv.naturality g
  dsimp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [S.map_comp, S.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← hf]
  simp only [Category.assoc]
  rw [hg]
private theorem affineHomTopLinear_bijective (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) : Function.Bijective (affineHomTopLinear R M N) := by
  exact (homCoordinates_bijective (tilde.functor (.of R)) (moduleSpecΓFunctor (R := .of R))
    (tilde.toTildeΓNatIso (R := .of R)) (tilde.fullyFaithfulFunctor (R := .of R)) M N).comp
      (topHomEquiv (Spec (CommRingCat.of R)) (tilde M) (tilde N)).bijective
private lemma moduleHomDifferential_v {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ)
    (h : p + (n + 1) = q) (x : (CochainComplex.moduleHomComplex P L).X n) :
    (((CochainComplex.moduleHomComplex P L).d n (n + 1)) x).v p q h =
      x.v p (p + n) rfl ≫ L.d (p + n) q +
        (n + 1).negOnePow • (P.d p (p + 1) ≫ x.v (p + 1) q (by omega)) := by
  exact CochainComplex.HomComplex.δ_v n (n + 1) rfl x p q h
    (p + n) (p + 1) (by omega) rfl
private noncomputable def cochainProjection {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p : ℤ) :
    (CochainComplex.moduleHomComplex P L).X n ⟶ ModuleCat.of R (P.X p ⟶ L.X (p + n)) :=
  ModuleCat.ofHom
    { toFun φ := φ.v p (p + n) rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
private noncomputable def cochainComponent {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + n = q) :
    (CochainComplex.moduleHomComplex P L).X n ⟶ ModuleCat.of R (P.X p ⟶ L.X q) :=
  ModuleCat.ofHom
    { toFun φ := φ.v p q h
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
private noncomputable def moduleHomMap {R : Type u} [CommRing R]
    {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N') :
    ModuleCat.of R (M ⟶ N) ⟶ ModuleCat.of R (M' ⟶ N') :=
  ModuleCat.ofHom
    { toFun φ := f ≫ φ ≫ g
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
private lemma moduleHomDifferential_component {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + (n + 1) = q) :
    (CochainComplex.moduleHomComplex P L).d n (n + 1) ≫
      cochainComponent P L (n + 1) p q h =
        cochainComponent P L n p (p + n) rfl ≫ moduleHomMap (𝟙 _) (L.d (p + n) q) -
          (n.negOnePow : ℤ) • (cochainComponent P L n (p + 1) q (by omega) ≫
            moduleHomMap (P.d p (p + 1)) (𝟙 _)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((CochainComplex.moduleHomComplex P L).d n (n + 1)) x).v p q h = _
  rw [moduleHomDifferential_v]
  simp only [
    cochainComponent, moduleHomMap,
    Int.negOnePow_succ, Units.val_neg, Units.smul_def, neg_smul, sub_eq_add_neg]
  rfl
private noncomputable def cochainIsLimit {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    IsLimit (Fan.mk ((CochainComplex.moduleHomComplex P L).X n)
      (cochainProjection P L n)) := by
  refine Fan.IsLimit.mk _ (fun s ↦ ModuleCat.ofHom
    { toFun x := CochainComplex.HomComplex.Cochain.mk fun p q h ↦
        (s.proj p x) ≫ (L.XIsoOfEq h).hom
      map_add' x y := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q h
        simp only [CochainComplex.HomComplex.Cochain.mk_v,
          CochainComplex.HomComplex.Cochain.add_v, map_add, Preadditive.add_comp]
      map_smul' r x := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q h
        simp only [CochainComplex.HomComplex.Cochain.mk_v,
          CochainComplex.HomComplex.Cochain.smul_v, map_smul, Linear.smul_comp,
          RingHom.id_apply] }) ?_ ?_
  · intro s p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (s.proj p x) ≫ (L.XIsoOfEq rfl).hom = s.proj p x
    simp
  · intro s m hm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q h
    subst q
    change ((m x).v p (p + n) rfl) = (s.proj p x) ≫ (L.XIsoOfEq rfl).hom
    have hh := ConcreteCategory.congr_hom (hm p) x
    change (m x).v p (p + n) rfl = s.proj p x at hh
    simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id] using hh
private noncomputable def affineHomTopIso (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) :
    (moduleSpecΓFunctor (R := .of R)).obj
      (SheafOfModules.homObj (R := (Spec (CommRingCat.of R)).sheaf) (tilde M) (tilde N)) ≅
      ModuleCat.of R (M ⟶ N) :=
  (LinearEquiv.ofBijective (affineHomTopLinear R M N)
    (affineHomTopLinear_bijective R M N)).toModuleIso
private lemma affineHomTopLinear_naturality (R : Type u) [CommRing R]
    {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N')
    (φ : (moduleSpecΓFunctor (R := .of R)).obj
      (SheafOfModules.homObj (R := (Spec (CommRingCat.of R)).sheaf) (tilde M) (tilde N))) :
    affineHomTopLinear R M' N'
      ((moduleSpecΓFunctor (R := .of R)).map
        (SheafOfModules.homObjMap (R := (Spec (CommRingCat.of R)).sheaf)
          (tilde.map (R := .of R) f) (tilde.map (R := .of R) g)) φ) =
      f ≫ affineHomTopLinear R M N φ ≫ g := by
  let T : ModuleCat.{u} R ⥤
      SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf := tilde.functor (.of R)
  let S := moduleSpecΓFunctor (R := .of R)
  have htop := topHomToHom_naturality (Spec (CommRingCat.of R)) (T.map f) (T.map g) φ
  change (tilde.isoTop (R := .of R) M').hom ≫ S.map _ ≫
    (tilde.isoTop (R := .of R) N').inv = _
  erw [htop]
  exact homCoordinates_naturality T S (tilde.toTildeΓNatIso (R := .of R)) f g
    (topHomToHom (Spec (CommRingCat.of R)) (tilde M) (tilde N) φ)
private lemma affineHomTopIso_naturality (R : Type u) [CommRing R]
    {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N')
    (φ : (moduleSpecΓFunctor (R := .of R)).obj
      (SheafOfModules.homObj (R := (Spec (CommRingCat.of R)).sheaf) (tilde M) (tilde N))) :
    (affineHomTopIso R M' N').hom
      ((moduleSpecΓFunctor (R := .of R)).map
        (SheafOfModules.homObjMap (R := (Spec (CommRingCat.of R)).sheaf)
          (tilde.map (R := .of R) f) (tilde.map (R := .of R) g)) φ) =
      f ≫ (affineHomTopIso R M N).hom φ ≫ g :=
  affineHomTopLinear_naturality R f g φ
attribute [local irreducible] affineHomTopIso
private noncomputable def productCoordinatesIso {C : Type*} [Category* C]
    {ι : Type*} (A B : ι → C) (Z W : C) (π : ∀ i, Z ⟶ A i) (ρ : ∀ i, W ⟶ B i)
    (hπ : IsLimit (Fan.mk Z π)) (hρ : IsLimit (Fan.mk W ρ))
    (e : ∀ i, A i ≅ B i) : Z ≅ W :=
  let α := Discrete.natIso (fun i ↦ e i.as)
  let h := (IsLimit.postcomposeHomEquiv α (Fan.mk Z π)).symm hπ
  h.conePointUniqueUpToIso hρ
private lemma productCoordinatesIso_π {C : Type*} [Category* C]
    {ι : Type*} (A B : ι → C) (Z W : C) (π : ∀ i, Z ⟶ A i) (ρ : ∀ i, W ⟶ B i)
    (hπ : IsLimit (Fan.mk Z π)) (hρ : IsLimit (Fan.mk W ρ))
    (e : ∀ i, A i ≅ B i) (i : ι) :
    (productCoordinatesIso A B Z W π ρ hπ hρ e).hom ≫ ρ i = π i ≫ (e i).hom := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)
attribute [local irreducible] productCoordinatesIso
section AbstractCoordinates
variable {R : Type u} [CommRing R]
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {𝓡 : Sheaf J CommRingCat.{u}}
    (T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))
    [T.PreservesZeroMorphisms]
    (S : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡) ⥤ ModuleCat.{u} R)
    [S.IsRightAdjoint]
    (θ : ∀ M N : ModuleCat.{u} R,
      S.obj (SheafOfModules.homObj (R := 𝓡) (T.obj M) (T.obj N)) ≅
        ModuleCat.of R (M ⟶ N))
    (hθ : ∀ {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N')
      (φ : S.obj (SheafOfModules.homObj (R := 𝓡) (T.obj M) (T.obj N))),
      (θ M' N').hom (S.map (SheafOfModules.homObjMap (R := 𝓡) (T.map f) (T.map g)) φ) =
        f ≫ (θ M N).hom φ ≫ g)
private noncomputable def affineHomCochainIsoData
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    { e : S.obj
      ((homComplex (R := 𝓡)
        ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L)).X n) ≅
      (CochainComplex.moduleHomComplex P L).X n //
      ∀ p, e.hom ≫ cochainProjection P L n p =
        S.map
          (homComplexπ
            ((T.mapHomologicalComplex (.up ℤ)).obj P)
            ((T.mapHomologicalComplex (.up ℤ)).obj L) n p (p + n) rfl) ≫
          (θ (P.X p) (L.X (p + n))).hom } := by
  let E := (T.mapHomologicalComplex (.up ℤ)).obj P
  let G := (T.mapHomologicalComplex (.up ℤ)).obj L
  let A (p : ℤ) := SheafOfModules.homObj (R := 𝓡)
    (E.X p) (G.X (p + n))
  let π (p : ℤ) := homComplexπ E G n p (p + n) rfl
  let hπ : IsLimit (Fan.mk _ (fun p ↦ S.map (π p))) :=
    isLimitFanMkObjOfIsLimit S A π (homComplexIsLimit E G n)
  let e := productCoordinatesIso (fun p ↦ S.obj (A p))
    (fun p ↦ ModuleCat.of R (P.X p ⟶ L.X (p + n))) _ _
    (fun p ↦ S.map (π p)) (cochainProjection P L n) hπ (cochainIsLimit P L n)
    (fun p ↦ θ (P.X p) (L.X (p + n)))
  exact ⟨e, fun p ↦ productCoordinatesIso_π _ _ _ _ _ _ _ _ _ p⟩
private noncomputable def affineHomCochainIso
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    S.obj
      ((homComplex (R := 𝓡)
        ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L)).X n) ≅
      (CochainComplex.moduleHomComplex P L).X n :=
  (affineHomCochainIsoData T S θ P L n).val
private lemma affineHomCochainIso_π
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p : ℤ) :
    let E := (T.mapHomologicalComplex (.up ℤ)).obj P
    let G := (T.mapHomologicalComplex (.up ℤ)).obj L
    (affineHomCochainIso T S θ P L n).hom ≫ cochainProjection P L n p =
      S.map (homComplexπ E G n p (p + n) rfl) ≫
        (θ (P.X p) (L.X (p + n))).hom := by
  exact (affineHomCochainIsoData T S θ P L n).property p
attribute [local irreducible] affineHomCochainIso
private lemma affineHomCochainIso_component
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + n = q) :
    (affineHomCochainIso T S θ P L n).hom ≫ cochainComponent P L n p q h =
      S.map (homComplexπ ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L) n p q h) ≫
          (θ (P.X p) (L.X q)).hom := by
  subst q
  exact affineHomCochainIso_π T S θ P L n p
omit [T.PreservesZeroMorphisms] [S.IsRightAdjoint] in
include hθ in
private lemma affineHomTop_naturality
    {M M' N N' : ModuleCat.{u} R} (f : M' ⟶ M) (g : N ⟶ N') :
    S.map (SheafOfModules.homObjMap (R := 𝓡) (T.map f) (T.map g)) ≫
      (θ M' N').hom = (θ M N).hom ≫ moduleHomMap f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact hθ f g φ
attribute [local irreducible] affineHomCochainIsoData
variable [S.Additive]
set_option backward.isDefEq.respectTransparency false in
include hθ in
private lemma affineHomCochainIso_comm
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) (h : n + 1 = m) :
    let E := (T.mapHomologicalComplex (.up ℤ)).obj P
    let G := (T.mapHomologicalComplex (.up ℤ)).obj L
    S.map ((homComplex E G).d n m) ≫
      (affineHomCochainIso T S θ P L m).hom =
        (affineHomCochainIso T S θ P L n).hom ≫
          (CochainComplex.moduleHomComplex P L).d n m := by
  subst m
  dsimp only
  let E := (T.mapHomologicalComplex (.up ℤ)).obj P
  let G := (T.mapHomologicalComplex (.up ℤ)).obj L
  apply (cochainIsLimit P L (n + 1)).hom_ext
  intro ⟨p⟩
  change (S.map ((homComplex E G).d n (n + 1)) ≫
      (affineHomCochainIso T S θ P L (n + 1)).hom) ≫
      cochainComponent P L (n + 1) p (p + (n + 1)) rfl =
    ((affineHomCochainIso T S θ P L n).hom ≫
      (CochainComplex.moduleHomComplex P L).d n (n + 1)) ≫
      cochainComponent P L (n + 1) p (p + (n + 1)) rfl
  erw [Category.assoc, affineHomCochainIso_component, ← Category.assoc,
    ← S.map_comp, homComplex_d_π E G n (n + 1) p (p + (n + 1))
      (p + n) (p + 1) rfl rfl rfl (by omega)]
  simp only [Units.smul_def]
  erw [S.map_sub, S.map_zsmul, S.map_comp, S.map_comp]
  erw [Preadditive.sub_comp, Preadditive.zsmul_comp]
  simp only [Category.assoc]
  erw [moduleHomDifferential_component]
  erw [Preadditive.comp_sub, Preadditive.comp_zsmul]
  dsimp only [E, G, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d]
  have h₁ := affineHomTop_naturality T S θ hθ (𝟙 (P.X p)) (L.d (p + n) (p + (n + 1)))
  have h₂ := affineHomTop_naturality T S θ hθ (P.d p (p + 1))
    (𝟙 (L.X (p + (n + 1))))
  simp only [Functor.map_id] at h₁ h₂
  erw [h₁, h₂]
  apply congrArg₂ (fun f g ↦ f - (n.negOnePow : ℤ) • g)
  · simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ moduleHomMap (𝟙 (P.X p)) (L.d (p + n) (p + (n + 1))))
      (affineHomCochainIso_component T S θ P L n p (p + n) rfl).symm
  · simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ moduleHomMap (P.d p (p + 1)) (𝟙 (L.X (p + (n + 1)))))
      (affineHomCochainIso_component T S θ P L n (p + 1) (p + (n + 1))
        (by omega)).symm
include hθ in
private noncomputable def affineHomGlobalComplexIso
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (S.mapHomologicalComplex (.up ℤ)).obj
      (homComplex (R := 𝓡)
        ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L)) ≅
      CochainComplex.moduleHomComplex P L :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := (S.mapHomologicalComplex (.up ℤ)).obj
      (homComplex (R := 𝓡)
        ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L)))
    (C₂ := CochainComplex.moduleHomComplex P L) (affineHomCochainIso T S θ P L)
    (fun n m h ↦ (affineHomCochainIso_comm T S θ hθ P L n m h).symm)
end AbstractCoordinates
private noncomputable def sheafComplexCounitIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms]
    (S : D ⥤ C) [S.PreservesZeroMorphisms] (η : S ⋙ T ⟶ 𝟭 D)
    (H : CochainComplex D ℤ) (K : CochainComplex C ℤ)
    (e : (S.mapHomologicalComplex (.up ℤ)).obj H ≅ K)
    (hi : ∀ i, IsIso (η.app (H.X i))) : H ≅ (T.mapHomologicalComplex (.up ℤ)).obj K := by
  let ε := NatTrans.mapHomologicalComplex η (.up ℤ)
  have (i : ℤ) : IsIso ((ε.app H).f i) := hi i
  have : IsIso (ε.app H) := HomologicalComplex.Hom.isIso_of_components _
  exact (asIso (ε.app H)).symm ≪≫ (T.mapHomologicalComplex (.up ℤ)).mapIso e
private theorem tildeFiniteFree (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] :
    ∃ r : ℕ, Nonempty ((@id (ModuleCat.{u} R ⥤ SheafOfModules.{u}
        (moduleRings (Spec (.of R)).toRingedSpace)) (tilde.functor (.of R))).obj M ≅
      SheafOfModules.free (R := moduleRings (Spec (.of R)).toRingedSpace)
        (ULift.{u} (Fin r))) := by
  let T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of R)).toRingedSpace) := tilde.functor (.of R)
  let B := Module.Free.chooseBasis R M
  let I := Module.Free.ChooseBasisIndex R M
  let : Fintype I := Fintype.ofFinite I
  let B' := B.reindex ((Fintype.equivFin I).trans Equiv.ulift.symm)
  exact ⟨Fintype.card I, ⟨T.mapIso B'.repr.toModuleIso ≪≫ tildeFinsupp _⟩⟩
private theorem affineFiniteFreeHomComparison (R : Type u) [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (b a : ℤ)
    (hP : P.IsStrictlyLE b) (hL : L.IsStrictlyGE a)
    (hfree : ∀ i, Module.Free R (P.X i))
    (hfinite : ∀ i, Module.Finite R (P.X i)) :
    let T : ModuleCat.{u} R ⥤
      SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf := tilde.functor (.of R)
    let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    Nonempty (homComplex (R := (Spec (CommRingCat.of R)).sheaf)
        ((T.mapHomologicalComplex (.up ℤ)).obj P)
        ((T.mapHomologicalComplex (.up ℤ)).obj L) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.moduleHomComplex P L)) := by
  classical
  let T : ModuleCat.{u} R ⥤
      SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf := tilde.functor (.of R)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let S : SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf ⥤
      ModuleCat.{u} R := moduleSpecΓFunctor (R := .of R)
  have adj : T ⊣ S := tilde.adjunction (R := .of R)
  let : S.IsRightAdjoint := adj.isRightAdjoint
  let : S.Additive := Functor.additive_of_preserves_binary_products S
  let E : CochainComplex (SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf) ℤ :=
    (T.mapHomologicalComplex (.up ℤ)).obj P
  let G : CochainComplex (SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf) ℤ :=
    (T.mapHomologicalComplex (.up ℤ)).obj L
  let H : CochainComplex (SheafOfModules.{u} (Spec (CommRingCat.of R)).ringCatSheaf) ℤ :=
    homComplex (R := (Spec (CommRingCat.of R)).sheaf) E G
  have : P.IsStrictlyLE b := hP
  have : L.IsStrictlyGE a := hL
  have : E.IsStrictlyLE b := inferInstance
  have : G.IsStrictlyGE a := inferInstance
  have he (i : ℤ) : ∃ r : ℕ, Nonempty
      (E.X i ≅ SheafOfModules.free (R := (Spec (CommRingCat.of R)).ringCatSheaf)
        (ULift.{u} (Fin r))) := by
    have := hfree i
    have := hfinite i
    exact tildeFiniteFree R (P.X i)
  have (i : ℤ) : SheafOfModules.IsQuasicoherent
      (R := (Spec (CommRingCat.of R)).ringCatSheaf) (H.X i) :=
    boundedFiniteFreeHomQuasicoherent (Spec (CommRingCat.of R)) E G b a he (fun j ↦ by
      change SheafOfModules.IsQuasicoherent
        (R := (Spec (CommRingCat.of R)).ringCatSheaf) (tilde (L.X j))
      infer_instance) i
  exact ⟨sheafComplexCounitIso T S (Scheme.Modules.fromTildeΓNatTrans (R := .of R)) H _
    (affineHomGlobalComplexIso T S (affineHomTopIso R)
      (fun f g φ ↦ affineHomTopIso_naturality R f g φ) P L)
    (fun i ↦ Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (H.X i))⟩
end CategoryTheory
namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
private theorem assembleAffineHomModel
    {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (𝓡 : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))]
    (T : ModuleCat.{u} R ⥤ SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))
    [T.PreservesZeroMorphisms] [T.PreservesHomology]
    (W : ℕ → (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡)))
    (hfreeT : ∀ M : ModuleCat.{u} R, Module.Free R M → Module.Finite R M →
      ∃ r : ℕ, Nonempty (T.obj M ≅ W r))
    (hcomparison : ∀ (F L : CochainComplex (ModuleCat.{u} R) ℤ) (b a : ℤ),
      F.IsStrictlyLE b → L.IsStrictlyGE a → (∀ i, Module.Free R (F.X i)) →
      (∀ i, Module.Finite R (F.X i)) →
      Nonempty (homComplex (R := 𝓡)
        ((T.mapHomologicalComplex (.up ℤ)).obj F)
        ((T.mapHomologicalComplex (.up ℤ)).obj L) ≅
          (T.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.moduleHomComplex F L)))
    (p l : CochainComplex (ModuleCat.{u} R) ℤ) (b a : ℤ)
    (hp : p.IsStrictlyLE b) (hl : l.IsGE a)
    (hfinite : ∀ i : ℤ, Module.Finite R (p.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (p.X i))
    (c : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ∀ n : ℤ, c.X n ≅ ModuleCat.of R (CochainComplex.HomComplex.Cochain p l n))
    (hc : ∀ n m : ℤ, c.d n m ≫ (e m).hom =
      (e n).hom ≫ ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom R p l n m)) :
    let Tc := T.mapHomologicalComplex (.up ℤ)
    ∃ (E G : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡)) ℤ) (f : E ⟶ Tc.obj p),
      QuasiIso f ∧ E.IsStrictlyLE b ∧ G.IsStrictlyGE a ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ W r)) ∧
      Nonempty ((DerivedCategory.Q (C := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).obj G ≅
        (DerivedCategory.Q (C := SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).obj (Tc.obj l)) ∧
      Nonempty ((DerivedCategory.Q (C := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).obj
        (homComplex (R := 𝓡) E G) ≅
        (DerivedCategory.Q (C := SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).obj (Tc.obj c)) := by
  classical
  let Tc := T.mapHomologicalComplex (.up ℤ)
  obtain ⟨F, hF, hterms, f, hf⟩ :=
    CochainComplex.exists_finiteFree_model_of_finite_projective R p b hp hfinite hprojective
  have : QuasiIso f := hf
  have : F.IsStrictlyLE b := hF
  have : l.IsGE a := hl
  let E : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡)) ℤ := Tc.obj F
  let G : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡)) ℤ :=
    Tc.obj (l.truncGE a)
  have hf' : QuasiIso (Tc.map f) := inferInstance
  have hE : E.IsStrictlyLE b := inferInstance
  have hG : G.IsStrictlyGE a := inferInstance
  refine ⟨E, G, Tc.map f, hf', hE, hG, ?_, ?_, ?_⟩
  · exact fun i ↦ hfreeT (F.X i) (hterms i).1 (hterms i).2
  · exact ⟨(asIso ((DerivedCategory.Q (C := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).map
      (Tc.map (l.πTruncGE a)))).symm⟩
  · obtain ⟨j⟩ := hcomparison F (l.truncGE a) b a
      hF inferInstance (fun i ↦ (hterms i).1) (fun i ↦ (hterms i).2)
    obtain ⟨g, hg⟩ := CochainComplex.moduleHomModelDerivedIso R p F l b a hp hF hl
      hprojective (fun i ↦ by
        have := (hterms i).1
        infer_instance) f hf
    have : QuasiIso g := hg
    let ec : c ≅ CochainComplex.moduleHomComplex p l :=
      HomologicalComplex.Hom.isoOfComponents e (fun n m _ ↦ (hc n m).symm)
    exact ⟨(DerivedCategory.Q (C := SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).mapIso j ≪≫
      (asIso ((DerivedCategory.Q (C := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).map (Tc.map g))).symm ≪≫
        (DerivedCategory.Q (C := SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝓡))).mapIso
              (Tc.mapIso ec.symm)⟩
/-- Prepare the ordinary module Hom complex for the finite-free sheaf Hom computation.
Source: Stacks Project, Tag 064U, proof of (3) implies (1); Tag 0A6H, clause (3)(a),
and Tag 08I5 (the Hom-complex calculation cited by Tag 0A6H).
(blueprint: lem-sc-affine-finite-projective-hom-model).
Proof:
1. Starting at the upper bound b, choose finite projective complements C^i so that
   F^b = p^b ⊕ C^b and F^(i-1) = p^(i-1) ⊕ C^i ⊕ C^(i-1) are finite free.
   Use d_p on p, identity on the repeated C^i, and zero on the last complement.
   Projection F → p has contractible kernel, giving a homotopy equivalence.
2. The good truncation l' = truncGE l a is strictly bounded below, and l → l'
   is a quasi-isomorphism because l has no cohomology below a. The bounded-above
   projective complex p is K-projective, so Hom(p,l) → Hom(p,l') is a
   quasi-isomorphism. This follows by applying Hom(p,-) to the acyclic cone:
   cocycles are maps to shifts of the cone and are nullhomotopic by K-projectivity.
   Precomposition with F → p is a homotopy equivalence on Hom complexes.
3. Set E = tilde(F), G = tilde(l'), and f = tilde(F → p). Additivity transports
   the homotopy equivalence, and exactness of tilde transports the truncation
   quasi-isomorphism; hence f is a quasi-isomorphism and Q(G) ≅ Q(tilde(l)).
4. For each degree n, only a-n ≤ i ≤ b contributes to Hom(F,l')^n. Finite-free
   Hom identifies Hom(tilde(F^i),tilde(l'^(i+n))) with the associated module Hom,
   and finite products commute with tilde. The formula d_l' h - (-1)^n h d_F
   makes these identifications a complex isomorphism. Combine it with step 2,
   exact termwise tilde, and the given e and hc to identify Q(Hom(E,G)) with
   Q(tilde(c)). No derived internal Hom computation is asserted here.
Edge cases: empty spectra and zero complexes satisfy the same product formulas;
rank-zero free terms are permitted. The coefficient representative l can be unbounded:
truncation occurs before replacing infinite Hom products by finite ones. -/
theorem affineFiniteProjectiveHomModel
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))]
    (p l : CochainComplex (ModuleCat.{u} R) ℤ)
    (b a : ℤ) (hp : p.IsStrictlyLE b) (hl : l.IsGE a)
    (hfinite : ∀ i : ℤ, Module.Finite R (p.X i))
    (hprojective : ∀ i : ℤ, Module.Projective R (p.X i))
    (c : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ∀ n : ℤ, c.X n ≅ ModuleCat.of R (CochainComplex.HomComplex.Cochain p l n))
    (hc : ∀ n m : ℤ, c.d n m ≫ (e m).hom =
      (e n).hom ≫ ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom R p l n m)) :
    let T := (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} R)
      (SheafOfModules.{u} (moduleRings (Spec (CommRingCat.of R)).toRingedSpace))
      _ _ _ _ (tilde.functor (CommRingCat.of R))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ))
    ∃ (E G : CochainComplex (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of R)).toRingedSpace)) ℤ)
      (f : E ⟶ T.obj p),
      QuasiIso f ∧ E.IsStrictlyLE b ∧ G.IsStrictlyGE a ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅
        SheafOfModules.free
          (R := moduleRings (Spec (CommRingCat.of R)).toRingedSpace)
          (ULift.{u} (Fin r)))) ∧
      Nonempty (DerivedCategory.Q.obj G ≅ DerivedCategory.Q.obj (T.obj l)) ∧
      Nonempty (DerivedCategory.Q.obj
        (homComplex (R := (Spec (CommRingCat.of R)).sheaf) E G) ≅
        DerivedCategory.Q.obj (T.obj c)) := by
  exact @assembleAffineHomModel R _ _ _ _ _ (Spec (.of R)).sheaf _ _ _
    (tilde.functor (.of R)) (affineBaseChangeTilde_preservesZero R)
    (tilde_preservesHomology R)
    (fun r ↦ SheafOfModules.free
      (R := moduleRings (Spec (.of R)).toRingedSpace) (ULift.{u} (Fin r)))
    (fun M hf hn ↦ @tildeFiniteFree R _ M hf hn)
    (affineFiniteFreeHomComparison R) p l b a hp hl hfinite hprojective c e hc

end CategoryTheory
