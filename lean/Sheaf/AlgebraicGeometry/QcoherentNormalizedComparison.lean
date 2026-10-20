/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

import WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.EtaleTensorDirectImageIdentification
import all WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import all WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsCokernelExact
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! # Normalized quasi-coherent comparison on a quasi-compact separated scheme

Source: Stacks Project, Tags 03P2, 03FD, 010S, 010T and 01FD.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Sheaf.H.equiv₀
  CategoryTheory.Abelian.Ext.mapExactFunctor
attribute [local irreducible] CategoryTheory.Functor.rightDerived
  CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp

attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace QcoherentNormalizedProof

-- The source's explicitly private proof helpers are available through `import all`.
-- Numeric components in their names are constructed here rather than parsed as fields.
local macro "nativeTensorNaturality" : term =>
  pure <| Lean.mkIdent <|
    (Lean.Name.num
      `_private.WeilConjectures.AlgebraicGeometry.EtaleTensorDirectImageIdentification 0) ++
        `AlgebraicGeometry.Scheme.Modules.etaleTensorOpenSectionIso_coeff_natural
local macro "nativeTensorUnitComp" : term =>
  pure <| Lean.mkIdent <|
    (Lean.Name.num `_private.WeilConjectures.AlgebraicGeometry.EtaleTensorSections 0) ++
      `AlgebraicGeometry.Scheme.Modules.sectionsUnit_comp
local macro "nativeOpenUnit" : term =>
  pure <| Lean.mkIdent <|
    (Lean.Name.num
      `_private.WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsCokernelExact 0) ++
        `AlgebraicGeometry.Scheme.Modules.openSection_unit


open CoherentEtale

private theorem overHasSheafify (X : Scheme.{u}) :
    ∀ U : X.Opens, HasWeakSheafify ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u} := fun _ ↦ inferInstance

private theorem overLocallyBijective (X : Scheme.{u}) :
    ∀ U : X.Opens, ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} := fun _ ↦ inferInstance

attribute [local instance 2000] overHasSheafify overLocallyBijective

private theorem addEquiv_mk₀
    {A : Type*} [Category A] [Abelian A] [HasExt A]
    {M N : A} (f : M ⟶ N) : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f :=
  Abelian.Ext.addEquiv₀.apply_symm_apply f

private theorem jointlyFaithful_restrict_cover {X : Scheme.{u}} (C : X.OpenCover) :
    JointlyFaithful (fun i ↦ restrictFunctor (C.f i)) := by
  apply JointlyReflectIsomorphisms.jointlyFaithful
  constructor
  intro P Q φ hφ
  apply isIso_of_isIso_pullback_map C.f
    (fun x ↦ by obtain ⟨y, hy⟩ := C.covers x; exact ⟨C.idx x, y, hy⟩) φ
  intro i
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (C.f i)) φ).mp (hφ i)

private theorem faithful_pullback_cover {X : Scheme.{u}} (C : X.OpenCover) :
    (pullback (Sigma.desc C.f)).Faithful := by
  constructor
  intro P Q φ ψ h
  apply (jointlyFaithful_restrict_cover C).map_injective
  intro i
  let e : restrictFunctor (C.f i) ≅
      pullback (Sigma.desc C.f) ⋙ pullback (Sigma.ι C.X i) :=
    restrictFunctorIsoPullback (C.f i) ≪≫
      pullbackCongr (Sigma.ι_desc C.f i).symm ≪≫
      (pullbackComp (Sigma.ι C.X i) (Sigma.desc C.f)).symm
  apply (cancel_epi (e.inv.app P)).mp
  apply (cancel_mono (e.hom.app Q)).mp
  rw [Category.assoc, Category.assoc, NatIso.naturality_1 e φ, NatIso.naturality_1 e ψ]
  exact congrArg ((pullback (Sigma.ι C.X i)).map) h

private theorem acyclic_embedding (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (i : F ⟶ G), Mono i ∧
      ∀ n : ℕ, IsZero ((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).obj G) := by
  classical
  let C := X.affineCover.finiteSubcover
  have hC (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C, Scheme.OpenCover.finiteSubcover]
    infer_instance
  have hf (i : C.I₀) : IsAffineHom (C.f i) := by
    constructor
    intro V hV
    apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (C.f i)).mp
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact (isAffineOpen_opensRange (C.f i)).inf hV
  have hj : IsAffineHom (Sigma.desc C.f) := isAffineHom_sigmaDesc C.f
  have : (pullback (Sigma.desc C.f)).Faithful := faithful_pullback_cover C
  let j := Sigma.desc C.f
  let A := (pullback j).obj F
  let : IsAffine (∐ C.X) := inferInstance
  let : IsAffineHom j := hj
  let : A.IsQuasicoherent := inferInstance
  refine ⟨(pushforward j).obj A, isQuasicoherent_pushforward_of_isAffineHom j A,
    (pullbackPushforwardAdjunction j).unit.app F, inferInstance, ?_⟩
  intro n
  have : Subsingleton (H A (n + 1)) := subsingleton_H_succ_of_isAffine A n
  obtain ⟨e, _⟩ := exists_moduleCohomology_source_comparison (∐ C.X) (n + 1)
  have : Subsingleton ((RingedSpace.moduleCohomology (∐ C.X).toRingedSpace
      (n + 1)).obj A) := (e A).toEquiv.injective.subsingleton
  have : IsIso (moduleCohomologyEdgeMap j A (n + 1)) :=
    ((affine_morphism_cohomology_edge j A).2 (n + 1)).1
  have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).obj
      ((pushforward j).obj A)) :=
    (ConcreteCategory.bijective_of_isIso (moduleCohomologyEdgeMap j A (n + 1))).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem tensor_section_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {F G : Y.Modules} (φ : F ⟶ G) [Mono φ] :
    Mono (((tensorPullback f).map φ).app ⊤) := by
  let : PreservesFiniteLimits (tensorPullback f) :=
    (AlgebraicGeometry.flat_module_pullback_exact_pushforward_injective f).1.1
  have : Mono ((tensorPullback f).map φ) := inferInstance
  have : Mono ((toPresheaf X).map ((tensorPullback f).map φ)) := inferInstance
  change Mono (((toPresheaf X).map ((tensorPullback f).map φ)).app (op ⊤))
  infer_instance

private theorem coefficient_mono (X : Scheme.{u})
    (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map (((tensorPullback U.hom).map φ).app ⊤))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) [Mono φ] : Mono (m F G φ) := by
  have h (U : X.Etaleᵒᵖ) : Mono ((m F G φ).hom.app U) := by
    rw [hm F G φ U.unop]
    let := tensor_section_mono U.unop.hom φ
    set_option backward.isDefEq.respectTransparency false in infer_instance
  let : ∀ U, Mono ((m F G φ).hom.app U) := h
  let : Mono (m F G φ).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mono_of_mono_map
    (show Mono (m F G φ).hom from inferInstance)

private theorem coefficient_map_sheafify (X : Scheme.{u}) (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map (((tensorPullback U.hom).map φ).app ⊤))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (etaleTensorSectionsFunctor X).map φ ≫ (etaleTensorSectionsFunctorObjIso G).hom =
      (etaleTensorSectionsFunctorObjIso F).hom ≫ m F G φ := by
  have h : Functor.whiskerRight (etaleTensorSectionsMap φ)
      AddCommGrpCat.uliftFunctor.{u + 1, u} = (m F G φ).hom := by
    apply NatTrans.ext
    funext U
    exact (hm F G φ U.unop).symm
  change (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (etaleTensorSectionsMap φ)
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≫ _ = _
  rw [h]
  exact (sheafificationNatIso X.smallEtaleTopology AddCommGrpCat.{u + 1}).inv.naturality
    (m F G φ)

private theorem shortExact_transport
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteColimits T]
    (S : ShortComplex A) (hS : S.ShortExact) {Y₁ Y₂ Y₃ : B}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) [Mono f]
    (e₁ : T.obj S.X₁ ≅ Y₁) (e₂ : T.obj S.X₂ ≅ Y₂) (e₃ : T.obj S.X₃ ≅ Y₃)
    (h₁ : T.map S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : T.map S.g ≫ e₃.hom = e₂.hom ≫ g) :
    ∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).ShortExact := by
  have hz : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).mp
    rw [← Category.assoc, ← h₁, Category.assoc, ← h₂,
      ← Category.assoc, ← T.map_comp, S.zero, T.map_zero, zero_comp, comp_zero]
  let e : S.map T ≅ ShortComplex.mk f g hz :=
    ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm
  let := hS.mono_f
  let := hS.epi_g
  have : Mono (T.map S.f ≫ e₂.hom) := by rw [h₁]; infer_instance
  have : Mono (T.map S.f) := mono_of_mono _ e₂.hom
  have hST : (S.map T).ShortExact := ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel T inferInstance inferInstance)
    (show Mono (T.map S.f) from inferInstance)
    (show Epi (T.map S.g) from inferInstance)
  exact ⟨hz, ShortComplex.shortExact_of_iso e hST⟩

private theorem coefficient_shortExact (X : Scheme.{u}) (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map (((tensorPullback U.hom).map φ).app ⊤))
    (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    ∃ hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0,
      (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact := by
  let T := etaleTensorSectionsFunctor X
  let : T.Additive := by
    dsimp [T, etaleTensorSectionsFunctor]
    infer_instance
  let : T.PreservesZeroMorphisms :=
    etaleTensorSectionsFunctor_preservesZeroMorphisms X
  let := preservesCokernels_etaleTensorSectionsFunctor X
  let : PreservesFiniteColimits T :=
    Functor.preservesFiniteColimits_of_preservesCokernels T
  have : Mono (m S.X₁ S.X₂ S.f) := by
    let := hS.mono_f
    exact coefficient_mono X m hm S.f
  exact shortExact_transport T S hS (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g)
    (etaleTensorSectionsFunctorObjIso S.X₁) (etaleTensorSectionsFunctorObjIso S.X₂)
    (etaleTensorSectionsFunctorObjIso S.X₃)
    (coefficient_map_sheafify X m hm S.X₁ S.X₂ S.f)
    (coefficient_map_sheafify X m hm S.X₂ S.X₃ S.g)


private theorem acyclic_groups (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ)
    (hz : IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G)) :
    Subsingleton (Source X G q) ∧ Subsingleton (Target X G q) := by
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G) :=
    ModuleCat.subsingleton_of_isZero hz
  let : Subsingleton (coherentModuleGroup X G q) :=
    ModuleCat.subsingleton_of_isZero hz
  refine ⟨(moduleAbelianCohomologyLarge X G q).symm.injective.subsingleton, ?_⟩
  let : Subsingleton (H G q) :=
    (moduleCohomologyExtResolutionEquiv X G q).symm.injective.subsingleton
  obtain ⟨_, _, c, _, _⟩ := etale_zariski_qcoh_comparison X
  let : Subsingleton (@Sheaf.H _ _ X.smallEtaleTopology
      (etaleTensorSectionsSheaf G) inferInstance (HasExt.standard _) q) :=
    (c G q).symm.injective.subsingleton
  obtain ⟨l, _⟩ := exists_etaleTensorSectionsSheaf_cohomology_ulift_natural X G q
  exact l.injective.subsingleton


private theorem effaces (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (m : Maps X)
    (hm : ∀ (F G : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map (((tensorPullback U.hom).map φ).app ⊤))
 : Effaces X m := by
  classical
  intro F hF n
  obtain ⟨G, hG, i, hi, hacyc⟩ := acyclic_embedding X F
  let := hG
  let : Mono i := hi
  let Q := cokernel i
  have hQ : Q.IsQuasicoherent := isQuasicoherent_cokernel i
  let := hQ
  let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.cokernelSequence i
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) hi
      (show Epi (cokernel.π i) from by
        set_option backward.isDefEq.respectTransparency false in infer_instance)
  have ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact :=
    hS.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  let : S.X₁.IsQuasicoherent := hF
  let : S.X₂.IsQuasicoherent := hG
  let : S.X₃.IsQuasicoherent := hQ
  obtain ⟨hz, he⟩ := coefficient_shortExact X m hm S hS
  obtain ⟨hza, hze⟩ := acyclic_groups X G (n + 1) (hacyc n)
  exact ⟨G, Q, hG, hQ, i, cokernel.π i, cokernel.condition i,
    hS, ha, hz, he, hza, hze⟩


private def comparison {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {S : A} {T : B} (b : Abelian.Ext T (P.obj S) 0)
    {M : A} {N : B} (a : P.obj M ⟶ N) (q : ℕ) :
    Abelian.Ext S M q →+ Abelian.Ext T N q :=
  { toFun := fun x ↦
      (b.comp (x.mapExactFunctor P) (zero_add q)).comp (Abelian.Ext.mk₀ a) (add_zero q)
    map_zero' := by
      rw [Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.comp_zero, Abelian.Ext.zero_comp]
    map_add' := by
      intro x y
      rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.comp_add, Abelian.Ext.add_comp] }


private theorem comparison_naturality
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {S M M' : A} {T N N' : B} (b : Abelian.Ext T (P.obj S) 0)
    (a : P.obj M ⟶ N) (a' : P.obj M' ⟶ N')
    (f : M ⟶ M') (g : N ⟶ N') (h : P.map f ≫ a' = a ≫ g)
    (q : ℕ) (x : Abelian.Ext S M q) :
    comparison P b a' q (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      (comparison P b a q x).comp (Abelian.Ext.mk₀ g) (add_zero q) := by
  change (b.comp ((x.comp (Abelian.Ext.mk₀ f) (add_zero q)).mapExactFunctor P)
    (zero_add q)).comp (Abelian.Ext.mk₀ a') (add_zero q) =
      ((b.comp (x.mapExactFunctor P) (zero_add q)).comp
        (Abelian.Ext.mk₀ a) (add_zero q)).comp (Abelian.Ext.mk₀ g) (add_zero q)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, h]

private theorem ext_boundary_square
    {B : Type*} [Category B] [Abelian B] [HasExt.{u + 1} B]
    {T O M₁ M₃ N₁ N₃ : B} (q : ℕ)
    (b : Abelian.Ext T O 0) (x : Abelian.Ext O M₃ q)
    (δ : Abelian.Ext M₃ M₁ 1) (δ' : Abelian.Ext N₃ N₁ 1)
    (f₁ : M₁ ⟶ N₁) (f₃ : M₃ ⟶ N₃)
    (h : δ.comp (Abelian.Ext.mk₀ f₁) (add_zero 1) =
      (Abelian.Ext.mk₀ f₃).comp δ' (zero_add 1)) :
    (b.comp (x.comp δ rfl) (zero_add (q + 1))).comp (Abelian.Ext.mk₀ f₁)
      (add_zero (q + 1)) =
    ((b.comp x (zero_add q)).comp (Abelian.Ext.mk₀ f₃) (add_zero q)).comp δ' rfl := by
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [h, ← Abelian.Ext.comp_assoc_of_second_deg_zero]
  exact (Abelian.Ext.comp_assoc b (x.comp (Abelian.Ext.mk₀ f₃) (add_zero q))
    δ' (zero_add q) rfl (by omega)).symm

private theorem comparison_boundary
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {O : A} {T : B} (b : Abelian.Ext T (P.obj O) 0)
    (S : ShortComplex A) (R : ShortComplex B)
    (hS : S.ShortExact) (hR : R.ShortExact) (a : S.map P ⟶ R)
    (q : ℕ) (x : Abelian.Ext O S.X₃ q) :
    comparison P b a.τ₁ (q + 1) (x.comp hS.extClass rfl) =
      (comparison P b a.τ₃ q x).comp hR.extClass rfl := by
  change (b.comp ((x.comp hS.extClass rfl).mapExactFunctor P)
    (zero_add (q + 1))).comp (Abelian.Ext.mk₀ a.τ₁) (add_zero (q + 1)) =
      ((b.comp (x.mapExactFunctor P) (zero_add q)).comp
        (Abelian.Ext.mk₀ a.τ₃) (add_zero q)).comp hR.extClass rfl
  have hmap := Abelian.Ext.mapExactFunctor_comp P x hS.extClass rfl
  have hclass := Abelian.Ext.mapExactFunctor_extClass P hS
  have hleft := hmap.trans (congrArg
    (fun y ↦ (x.mapExactFunctor P).comp y rfl) hclass)
  exact (congrArg (fun y ↦ (b.comp y (zero_add (q + 1))).comp
    (Abelian.Ext.mk₀ a.τ₁) (add_zero (q + 1))) hleft).trans
      (ext_boundary_square q b (x.mapExactFunctor P) (hS.map_of_exact P).extClass
        hR.extClass a.τ₁ a.τ₃ ((hS.map_of_exact P).extClass_naturality hR a))


private theorem comparison_mk₀
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {S M : A} {T N : B} (b : Abelian.Ext T (P.obj S) 0)
    (a : P.obj M ⟶ N) (f : S ⟶ M) :
    comparison P b a 0 (Abelian.Ext.mk₀ f) =
      b.comp (Abelian.Ext.mk₀ (P.map f ≫ a)) (add_zero 0) := by
  change (b.comp ((Abelian.Ext.mk₀ f).mapExactFunctor P) (zero_add 0)).comp
    (Abelian.Ext.mk₀ a) (add_zero 0) = _
  rw [Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

attribute [local irreducible] comparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_zero
    {A C : Type*} [Category A] [Abelian A] [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} A] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    (P : A ⥤ Sheaf J AddCommGrpCat.{u + 1})
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {S M : A} {N : Sheaf J AddCommGrpCat.{u + 1}} {T : C}
    (b : Sheaf.H (P.obj S) 0) (a : P.obj M ⟶ N) (hT : IsTerminal T)
    (x : Abelian.Ext S M 0) :
    Sheaf.H.equiv₀ N hT (comparison P b a 0 x) =
      (P.map (Abelian.Ext.addEquiv₀ x) ≫ a).hom.app (op T)
        (Sheaf.H.equiv₀ (P.obj S) hT b) := by
  rcases (Abelian.Ext.mk₀_bijective S M).2 x with ⟨f, rfl⟩
  rw [comparison_mk₀, addEquiv_mk₀]
  exact (congrArg (Sheaf.H.equiv₀ N hT)
    (Sheaf.H.map_apply (P.map f ≫ a) b).symm).trans
      (Sheaf.H.equiv₀_naturality hT (P.map f ≫ a) b).symm


private theorem lift_exact (X : Scheme.{u}) :
    (sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesHomology := by
  let J := Opens.grothendieckTopology X
  let L := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.Additive := inferInstance
  have : PreservesLimitsOfShape WalkingParallelPair L := by
    have : PreservesLimitsOfShape WalkingParallelPair
        (L ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) := by
      change PreservesLimitsOfShape WalkingParallelPair
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u})
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves L
      (sheafToPresheaf J AddCommGrpCat.{u + 1})
  have : L.PreservesEpimorphisms :=
    { preserves := by
        intro A B f hf
        have : Sheaf.IsLocallySurjective f :=
          (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).mpr hf
        have : Sheaf.IsLocallySurjective (L.map f) := by
          constructor
          intro U s
          have h := Presheaf.imageSieve_mem J f.hom s.down
          convert h using 1
          ext V g
          constructor
          · rintro ⟨t, ht⟩
            exact ⟨t.down, congrArg ULift.down ht⟩
          · rintro ⟨t, ht⟩
            exact ⟨ULift.up t, congrArg ULift.up ht⟩
        infer_instance }
  exact Functor.preservesHomology_of_preservesEpis_and_kernels L

set_option backward.isDefEq.respectTransparency false
private theorem etaleTensorOpenSectionIso_coeff_natural
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F G : X.Modules) (φ : F ⟶ G) (U : X.Opensᵒᵖ) :
    ((tensorPullback (i.obj U.unop).hom).map φ).app ⊤ ≫
        (etaleTensorOpenSectionIso X i hi G U).hom =
      (etaleTensorOpenSectionIso X i hi F U).hom ≫ φ.app U.unop := by
  exact nativeTensorNaturality X i hi F G φ U

private theorem tensor_unit_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (F : C.Modules) :
    tensorSectionsUnit b F ≫ tensorSectionsUnit a ((tensorPullback b).obj F) ≫
      ((tensorSectionsComp a b).hom.app F).app ⊤ = tensorSectionsUnit (a ≫ b) F := by
  exact nativeTensorUnitComp
    (fun f ↦ tensorPullback f)
    (fun f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b F

private theorem tensor_unit_transport {X : Scheme.{u}} (F : X.Modules)
    {A B : Over X} (h : A = B) :
    tensorSectionsUnit A.hom F ≫
      eqToHom (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤)) h) =
        tensorSectionsUnit B.hom F := by
  cases h
  simp

private theorem tensor_unit_restrict {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) :
    tensorSectionsUnit U.hom F ≫ etaleTensorSectionsRestriction F g =
      tensorSectionsUnit V.hom F := by
  unfold etaleTensorSectionsRestriction
  rw [reassoc_of% (tensor_unit_comp g.left U.hom F)]
  have ht : ∀ (a b : V.left ⟶ X) (e : a = b),
      tensorSectionsUnit a F ≫ (eqToHom
        (congrArg (fun f ↦ (tensorPullback f).obj F) e)).app ⊤ =
        tensorSectionsUnit b F := by
    intro a b e
    cases e
    simp
  exact ht _ _ g.w

private theorem etale_open_unit (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : X.Modules) (U : X.Opensᵒᵖ) :
    tensorSectionsUnit (i.obj U.unop).hom F ≫
      (etaleTensorOpenSectionIso X i hi F U).hom =
        F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op := by
  dsimp only [etaleTensorOpenSectionIso, Iso.trans_hom, eqToIso.hom]
  erw [← Category.assoc, tensor_unit_transport F
    (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi)]
  exact nativeOpenUnit U.unop F

private theorem transpose_natural
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {U V : C} {N N' : D}
    (a : U ⟶ R.obj N) (a' : V ⟶ R.obj N') (f : U ⟶ V) (g : N ⟶ N')
    (h : f ≫ a' = a ≫ R.map g) :
    L.map f ≫ (adj.homEquiv _ _).symm a' = (adj.homEquiv _ _).symm a ≫ g := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simpa only [Equiv.apply_symm_apply] using h

private theorem transpose_unit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {U V : C} {N : D} (a : V ⟶ R.obj N) (f : U ⟶ V) :
    adj.unit.app U ≫ R.map (L.map f ≫ (adj.homEquiv _ _).symm a) = f ≫ a := by
  rw [Functor.map_comp, ← Category.assoc, adj.unit_naturality f, Category.assoc]
  congr 1
  exact (adj.homEquiv_unit _ _ ((adj.homEquiv _ _).symm a)).symm.trans
    ((adj.homEquiv _ _).apply_symm_apply a)

private theorem transpose_evaluation
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (i : C ⥤ D) [i.IsContinuous J K]
    {L : Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf K AddCommGrpCat.{u + 1}}
    (adj : L ⊣ i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K)
    {U : C} {V : D} (e : i.obj U ≅ V)
    {S M : Sheaf J AddCommGrpCat.{u}} {N : Sheaf K AddCommGrpCat.{u + 1}}
    (f : S ⟶ M)
    (a : (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj M ⟶
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj N)
    (z : S.obj.obj (op U)) :
    let L₀ := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
    let g := L.map (L₀.map f) ≫ (adj.homEquiv _ _).symm a
    g.hom.app (op V)
      ((L.obj (L₀.obj S)).obj.map e.inv.op
        ((adj.unit.app (L₀.obj S)).hom.app (op U) (ULift.up z))) =
      N.obj.map e.inv.op (a.hom.app (op U) (ULift.up (f.hom.app (op U) z))) := by
  dsimp only
  let L₀ := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
  let g := L.map (L₀.map f) ≫ (adj.homEquiv _ _).symm a
  have hn := ConcreteCategory.congr_hom (g.hom.naturality e.inv.op)
    ((adj.unit.app (L₀.obj S)).hom.app (op U) (ULift.up z))
  simp only [ConcreteCategory.comp_apply] at hn
  have h := transpose_unit adj a (L₀.map f)
  have hh := congrArg (fun k : L₀.obj S ⟶
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj N ↦
        k.hom.app (op U)) h
  have hu := ConcreteCategory.congr_hom hh (ULift.up z)
  change g.hom.app (op (i.obj U))
      ((adj.unit.app (L₀.obj S)).hom.app (op U) (ULift.up z)) =
    a.hom.app (op U) (ULift.up (f.hom.app (op U) z)) at hu
  exact hn.trans (congrArg (N.obj.map e.inv.op) hu)

private theorem zero_evaluation
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{u}) (x : Sheaf.H F 0) :
    (Abelian.Ext.addEquiv₀ x).hom.app (op T)
      (Sheaf.H.equiv₀ ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hT (Abelian.Ext.mk₀ (𝟙 _))) =
      Sheaf.H.equiv₀ F hT x := by
  let S := (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let f : S ⟶ F := Abelian.Ext.addEquiv₀ x
  have hn := Sheaf.H.equiv₀_naturality hT f (Abelian.Ext.mk₀ (𝟙 S))
  have hh : Sheaf.H.map f 0 (Abelian.Ext.mk₀ (𝟙 S)) = x := by
    rw [Sheaf.H.map_apply, Abelian.Ext.mk₀_comp_mk₀, Category.id_comp]
    exact Abelian.Ext.mk₀_addEquiv₀_apply x
  rw [hh] at hn
  exact hn

@[irreducible] private def openRestrictionIso (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj F ≅
      (i.sheafPushforwardContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology X)
        X.smallEtaleTopology).obj (etaleTensorSectionsSheaf F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (etaleTensorOpenSectionIso X i hi F)
      (fun f ↦ etaleTensorOpenSectionIso_naturality X i hi F f)).symm

private theorem openRestrictionIso_hom_app (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (U : X.Opensᵒᵖ) :
    (openRestrictionIso X i hi F).hom.hom.app U =
      (etaleTensorOpenSectionIso X i hi F U).inv := by
  unfold openRestrictionIso
  rfl

private theorem openRestrictionIso_top (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (s : Γ(F, ⊤)) :
    (openRestrictionIso X i hi F).hom.hom.app (op ⊤) s =
      tensorSectionsUnit (i.obj ⊤).hom F s := by
  rw [openRestrictionIso_hom_app]
  apply (ConcreteCategory.bijective_of_isIso
    (etaleTensorOpenSectionIso X i hi F (op ⊤)).hom).injective
  erw [Iso.inv_hom_id_apply]
  have hu := ConcreteCategory.congr_hom (etale_open_unit X i hi F (op ⊤)) s
  have hid : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : X.Opens)) := rfl
  rw [hid] at hu
  change (etaleTensorOpenSectionIso X i hi F (op ⊤)).hom
    (tensorSectionsUnit (i.obj ⊤).hom F s) =
      (show X.Modules from F).presheaf.map (𝟙 (op ⊤)) s at hu
  rw [(show X.Modules from F).presheaf.map_id] at hu
  exact hu.symm

private structure SiteInverseImage (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology] where
  left : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  adj : left ⊣ i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) X.smallEtaleTopology

@[irreducible] private def siteInverseImage (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology] :
    SiteInverseImage X i :=
  { left := Functor.sheafPullbackConstruction.sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X) X.smallEtaleTopology
    adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous i
      AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X) X.smallEtaleTopology }

private theorem siteInverseImage_additive (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology] :
    (siteInverseImage X i).left.Additive := by
  have : (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X) X.smallEtaleTopology).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (siteInverseImage X i).adj.left_adjoint_additive

private theorem siteInverseImage_limits (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    [RepresentablyFlat i] : PreservesFiniteLimits (siteInverseImage X i).left := by
  unfold siteInverseImage
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have := preservesFiniteLimits_op_lan_of_flat (H := AddCommGrpCat.{u + 1}) i
  change PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X) X.smallEtaleTopology)
  infer_instance

@[irreducible] private def sourceHom (X : Scheme.{u}) (F : X.Modules)
    (x : Source X F 0) :
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
        (SheafOfModules.toSheaf X.ringCatSheaf).obj F :=
  @Abelian.Ext.addEquiv₀
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    inferInstance inferInstance (HasExt.standard _) _ _ x

attribute [local irreducible] targetZero

private theorem normalized_from_data (X : Scheme.{u}) (m : Maps X)
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (P : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (b : Sheaf.H.{u + 1, u + 1, u, u + 1}
      (P.obj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) 0)
    (d : ∀ (F : X.Modules) [F.IsQuasicoherent],
      P.obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ⟶ Coeff F)
    (natural_d : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G),
      P.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫ d G = d F ≫ m F G φ)
    (zero : ∀ (F : X.Modules) [F.IsQuasicoherent] (x : Source X F 0),
      (P.map (sourceHom X F x) ≫ d F).hom.app (op (⊤_ X.Etale))
        (Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} _ terminalIsTerminal b) =
          ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F (sourceZero X F x))) :
    ∃ c : Family X, IsNormalized X m c := by
  let c : Family X := fun F _ q ↦ comparison P b (d F) q
  refine ⟨c, ?_, ?_, ?_⟩
  · intro F G _ _ φ q x
    exact comparison_naturality P b (d F) (d G)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) (m F G φ) (natural_d F G φ) q x
  · intro F _ x
    have h := comparison_zero P b (d F) terminalIsTerminal x
    unfold targetZero
    change Sheaf.H.equiv₀ _ terminalIsTerminal (comparison P b (d F) 0 x) = _
    unfold sourceHom at *
    exact h.trans (zero F x)
  · intro V h₁ h₂ h₃ hV hz ha he q x
    let A := SheafOfModules.toSheaf X.ringCatSheaf
    let R := ShortComplex.mk (m V.X₁ V.X₂ V.f) (m V.X₂ V.X₃ V.g) hz
    let f : (V.map A).map P ⟶ R :=
      { τ₁ := d V.X₁
        τ₂ := d V.X₂
        τ₃ := d V.X₃
        comm₁₂ := (natural_d _ _ V.f).symm
        comm₂₃ := (natural_d _ _ V.g).symm }
    exact comparison_boundary P b (V.map A) R ha he f q x

private theorem map_inverse_square {C D : Type*} [Category C] [Category D]
    (V : C ⥤ D) {A B A' B' : C} (e : A ≅ A') (d : B ≅ B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ d.hom = e.hom ≫ g) :
    V.map g ≫ V.map d.inv = V.map e.inv ≫ V.map f := by
  rw [← V.map_comp, ← V.map_comp]
  congr 1
  apply (cancel_mono d.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (fun k ↦ e.inv ≫ k) h.symm

private theorem lifted_open_top (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)) :
    (((sheafCompose (Opens.grothendieckTopology X)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (openRestrictionIso X i hi F).hom).hom.app (op ⊤)) (ULift.up s) =
      ULift.up (tensorSectionsUnit (i.obj ⊤).hom F s) := by
  change ULift.up.{u + 1, u}
    ((openRestrictionIso X i hi F).hom.hom.app (op ⊤) s) = _
  exact congrArg (ULift.up.{u + 1, u}) (openRestrictionIso_top X i hi F s)

private theorem ulift_map_apply {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (x : A) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.map f) (ULift.up.{u + 1, u} x) =
      ULift.up.{u + 1, u} (f x) := rfl

attribute [local irreducible] tensorSectionsUnit etaleTensorSectionsRestriction

private theorem coeff_map {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U V : X.Etale} (g : U ⟶ V) :
    (Coeff F).obj.map g.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (etaleTensorSectionsRestriction F g) := rfl

private theorem lift_unit_apply {A B C : AddCommGrpCat.{u}}
    (r : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj B ⟶
      AddCommGrpCat.uliftFunctor.{u + 1, u}.obj C)
    (f : A ⟶ B) (g : A ⟶ C)
    (h : AddCommGrpCat.uliftFunctor.{u + 1, u}.map f ≫ r =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map g) (s : A) :
    r (ULift.up (f s)) = ULift.up (g s) := by
  have hh := ConcreteCategory.congr_hom h (ULift.up.{u + 1, u} s)
  change r ((AddCommGrpCat.uliftFunctor.{u + 1, u}.map f) (ULift.up s)) =
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.map g) (ULift.up s) at hh
  rw [ulift_map_apply, ulift_map_apply] at hh
  exact hh

private theorem coeff_unit_square {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U V : X.Etale} (g : U ⟶ V) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map (tensorSectionsUnit V.hom F) ≫
      (Coeff F).obj.map g.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (tensorSectionsUnit U.hom F) := by
  exact (congrArg
    (fun r ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      (tensorSectionsUnit V.hom F) ≫ r) (coeff_map F g)).trans
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _).symm.trans
      (congrArg AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (tensor_unit_restrict F g)))

private theorem transpose_zero
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (i : C ⥤ D) [i.IsContinuous J K]
    {L : Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf K AddCommGrpCat.{u + 1}}
    (adj : L ⊣ i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K)
    {U : C} {V : D} (e : i.obj U ≅ V)
    {S M : Sheaf J AddCommGrpCat.{u}} {N : Sheaf K AddCommGrpCat.{u + 1}}
    (f : S ⟶ M)
    (a : (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj M ⟶
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj N)
    (z : S.obj.obj (op U)) (s : M.obj.obj (op U))
    (v : N.obj.obj (op V))
    (hs : f.hom.app (op U) z = s)
    (hv : N.obj.map e.inv.op (a.hom.app (op U) (ULift.up s)) = v) :
    let L₀ := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
    let P := L₀ ⋙ L
    let t := (P.obj S).obj.map e.inv.op
      ((adj.unit.app (L₀.obj S)).hom.app (op U) (ULift.up z))
    (P.map f ≫ (adj.homEquiv _ _).symm a).hom.app (op V)
      t = v := by
  exact (transpose_evaluation i adj e f a z).trans
    ((congrArg (fun y ↦ N.obj.map e.inv.op (a.hom.app (op U) (ULift.up y))) hs).trans hv)

private theorem transpose_zero_lift
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (i : C ⥤ D) [i.IsContinuous J K]
    {L : Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf K AddCommGrpCat.{u + 1}}
    (adj : L ⊣ i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K)
    {U : C} {V : D} (e : i.obj U ≅ V)
    {S M : Sheaf J AddCommGrpCat.{u}} (N : Sheaf K AddCommGrpCat.{u})
    (f : S ⟶ M)
    (a : (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj M ⟶
      (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj
        ((sheafCompose K AddCommGrpCat.uliftFunctor.{u + 1, u}).obj N))
    (z : S.obj.obj (op U)) (s : M.obj.obj (op U))
    (fU : M.obj.obj (op U) ⟶ N.obj.obj (op (i.obj U)))
    (fV : M.obj.obj (op U) ⟶ N.obj.obj (op V))
    (hs : f.hom.app (op U) z = s)
    (ha : a.hom.app (op U) (ULift.up s) = ULift.up (fU s))
    (hr : AddCommGrpCat.uliftFunctor.{u + 1, u}.map fU ≫
        ((sheafCompose K AddCommGrpCat.uliftFunctor.{u + 1, u}).obj N).obj.map e.inv.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map fV) :
    let L₀ := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
    let P := L₀ ⋙ L
    let t := (P.obj S).obj.map e.inv.op
      ((adj.unit.app (L₀.obj S)).hom.app (op U) (ULift.up z))
    (P.map f ≫ (adj.homEquiv _ _).symm a).hom.app (op V)
      t =
      ULift.up (fV s) := by
  apply transpose_zero i adj e f a z s _ hs
  exact (congrArg (fun y ↦
    ((sheafCompose K AddCommGrpCat.uliftFunctor.{u + 1, u}).obj N).obj.map e.inv.op y)
      ha).trans (lift_unit_apply _ fU fV hr s)

private theorem apply_symm_under
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (f : B → C) (t : B) :
    f (e (e.symm t)) = f t := congrArg f (e.apply_symm_apply t)

attribute [local irreducible] Adjunction.homEquiv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 100000 in
-- Bound elaboration while keeping the large site constructions behind their interfaces.
private theorem normalized_exists (X : Scheme.{u}) (m : Maps X)
    (hm : ∀ (F G : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map (((tensorPullback U.hom).map φ).app ⊤)) :
    ∃ c : Family X, IsNormalized X m c := by
  classical
  obtain ⟨i, hi, _, hilim, ⟨hitop⟩, hicont, hiflat⟩ := zariski_to_etale_core X
  let := hilim
  let := hicont
  let := hiflat
  let J := Opens.grothendieckTopology X
  let : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u}) := HasExt.standard _
  let L₀ := sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}
  let D := siteInverseImage X i
  let L := D.left
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J X.smallEtaleTopology
  let adj := D.adj
  have : L.Additive := siteInverseImage_additive X i
  have : PreservesFiniteLimits L := siteInverseImage_limits X i
  have : PreservesFiniteColimits L := by
    have : L.IsLeftAdjoint := adj.isLeftAdjoint
    infer_instance
  have : L₀.Additive := inferInstance
  have : L₀.PreservesHomology := lift_exact X
  have : PreservesFiniteLimits L₀ := Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits L₀ := Functor.preservesFiniteColimits_of_preservesHomology _
  let P := L₀ ⋙ L
  have : P.Additive := inferInstance
  have : PreservesFiniteLimits P := inferInstance
  have : PreservesFiniteColimits P := inferInstance
  let A := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let a₀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] := openRestrictionIso X i hi F
  let a (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] :
      L₀.obj (A.obj F) ⟶ T.obj (Coeff F) :=
    L₀.map (a₀ F).hom
  have ha (F G : SheafOfModules.{u} X.ringCatSheaf)
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
      L₀.map (A.map φ) ≫ a G = a F ≫ T.map (m F G φ) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change AddCommGrpCat.uliftFunctor.{u + 1, u}.map (Hom.app φ U.unop) ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map ((a₀ G).hom.hom.app U) =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map ((a₀ F).hom.hom.app U) ≫
        (m F G φ).hom.app (op (i.obj U.unop))
    dsimp only [a₀]
    rw [openRestrictionIso_hom_app, openRestrictionIso_hom_app, hm F G φ]
    exact map_inverse_square AddCommGrpCat.uliftFunctor.{u + 1, u}
      (etaleTensorOpenSectionIso X i hi F U) (etaleTensorOpenSectionIso X i hi G U)
      (((tensorPullback (i.obj U.unop).hom).map φ).app ⊤) (Hom.app φ U.unop)
      (etaleTensorOpenSectionIso_coeff_natural X i hi F G φ U)
  let d (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] : P.obj (A.obj F) ⟶ Coeff F :=
    (adj.homEquiv _ _).symm (a F)
  have hd (F G : SheafOfModules.{u} X.ringCatSheaf)
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
      P.map (A.map φ) ≫ d G = d F ≫ m F G φ := by
    exact transpose_natural adj (a F) (a G) (L₀.map (A.map φ)) (m F G φ) (ha F G φ)
  let S := (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let z : S.obj.obj (op (⊤ : X.Opens)) :=
    @Sheaf.H.equiv₀.{u + 1, u, u, u} _ _ J inferInstance
      (HasExt.standard _) S _ isTerminalTop
      (Abelian.Ext.mk₀ (𝟙 S))
  let e : i.obj ⊤ ≅ ⊤_ X.Etale := hitop.uniqueUpToIso terminalIsTerminal
  let t : (P.obj S).obj.obj (op (⊤_ X.Etale)) :=
    (P.obj S).obj.map e.inv.op (((adj.unit.app (L₀.obj S)).hom.app (op ⊤)) (ULift.up z))
  let b : Sheaf.H.{u + 1, u + 1, u, u + 1} (P.obj S) 0 :=
    (Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} (P.obj S) terminalIsTerminal).symm t
  apply normalized_from_data X m P b d hd
  intro F _ x
  let f : S ⟶ A.obj F := sourceHom X F x
  have hfx : f.hom.app (op ⊤) z = sourceZero X F x := by
    unfold f sourceHom
    exact zero_evaluation J isTerminalTop (A.obj F) x
  have haunit : (a F).hom.app (op ⊤) (ULift.up (sourceZero X F x)) =
      ULift.up (tensorSectionsUnit (i.obj ⊤).hom F (sourceZero X F x)) := by
    exact lifted_open_top X i hi F (sourceZero X F x)
  exact (apply_symm_under
    (Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} (P.obj S) terminalIsTerminal)
    ((P.map f ≫ d F).hom.app (op (⊤_ X.Etale))) t).trans
      (transpose_zero_lift (J := J) (K := X.smallEtaleTopology) i (L := L)
        adj e (etaleTensorSectionsSheaf F) f (a F) z (sourceZero X F x)
        (tensorSectionsUnit (i.obj ⊤).hom F) (tensorSectionsUnit (⊤_ X.Etale).hom F)
        hfx haunit (coeff_unit_square F e.inv))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_large_natural (X : Scheme.{u}) (q : ℕ)
    (F G : SheafOfModules.{u} X.ringCatSheaf) (φ : F ⟶ G)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge X G q
      ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ x) =
      sourceMap X φ q (moduleAbelianCohomologyLarge X F q x) := by
  exact moduleAbelianCohomologyLarge_naturality X q F G φ x

private theorem cancel_trans
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (e : A ≃+ B) (d : B ≃+ C) : e.symm.trans (e.trans d) = d := by
  apply AddEquiv.ext
  intro x
  exact congrArg d (e.apply_symm_apply x)

end QcoherentNormalizedProof

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Existence of the normalized comparison on one quasi-compact separated scheme.
The comparison is specified as a morphism of delta functors, in addition to its
normalization on sections. The uniqueness clause determines every component.

Source: Stacks Project, Etale Cohomology, Tag 03P2, separated-case affine-cover
argument; Cohomology on Sites, Tag 03FD; Homology, Tags 010S and 010T.
(blueprint: lem-weil-pbc-qcoherent-normalized-comparison-exists)

Proof: Use the continuous, representably flat inclusion of Zariski opens into the
small etale site. Its abelian inverse image is exact. The tensor-section
identifications on open objects give a natural map from the inverse image of the
lifted underlying abelian sheaf to the lifted tensor-section sheaf, by adjunction.
Pull back Ext classes along this exact functor, precompose with the class of the
lifted integer generator, and postcompose with that natural map. Functoriality of
Ext gives coefficient naturality; naturality of short-exact extension classes
gives the connecting-map identity. Evaluating the adjunction unit at the terminal
object, and then transporting between the two terminal objects, gives precisely
the tensor-section unit in degree zero.

Choose a finite affine open cover and its disjoint union Y. The morphism Y to X
is affine because X is separated. Pullback to the cover is faithful, so the
adjunction unit embeds each quasi-coherent F into the quasi-coherent pushforward
of its pullback to Y. The affine cohomology edge and affine vanishing make this
pushforward acyclic. Its cokernel is quasi-coherent. Flat tensor pullback and
sheafification preserve the short exact sequence. The ordinary etale/Zariski
comparison and its coefficient lift transfer acyclicity to the etale side.
Thus the established dimension-shifting theorem proves bijectivity and uniqueness
of the normalized additive family. Transport it by the fixed module/abelian
comparison. Its resolution normalization identifies the image of an actual
section in degree zero. Its coefficient naturality, together with the compatibility
of Ext universe change with postcomposition, gives direct module naturality.
No nonempty, proper, smooth or field hypothesis is used; the argument includes the
empty scheme and zero modules. -/
theorem exists_unique_qcoherentNormalizedComparison
    (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X] :
    ∃! c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
        Sheaf.H (liftedCoherentEtaleSheaf F) q,
      IsNormalizedCoherentEtaleComparison X
          (fun F _ q ↦ (moduleAbelianCohomologyLarge X F q).symm.trans (c F q)) ∧
        (∀ (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤)),
          Sheaf.H.equiv₀ (liftedCoherentEtaleSheaf F) terminalIsTerminal
            (c F 0
              ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s)) =
            ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s)) ∧
        ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
          (φ : F ⟶ G) (q : ℕ)
          (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
          c G q ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ x) =
            Sheaf.H.map (coherentEtaleMap F G φ) q (c F q x) := by
  classical
  let m : CoherentEtale.Maps X := fun F G _ _ φ ↦ coherentEtaleMap F G φ
  have hm (F G : SheafOfModules.{u} X.ringCatSheaf)
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (U : X.Etale) :=
    congrArg AddCommGrpCat.uliftFunctor.{u + 1, u}.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 F G φ U)
  have heff := QcoherentNormalizedProof.effaces X m hm
  obtain ⟨a, ha⟩ := QcoherentNormalizedProof.normalized_exists X m hm
  have hb := CoherentEtale.normalized_bijective X m heff a ha
    (fun F _ ↦ CoherentEtale.normalized_zero_bijective X m a ha F)
  let e (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ) :=
    AddEquiv.ofBijective (a F q) (hb F q)
  let c (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ) :=
    (moduleAbelianCohomologyLarge X F q).trans (e F q)
  have hc : (fun (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ) ↦
      (moduleAbelianCohomologyLarge X F q).symm.trans (c F q)) = e := by
    funext F hF q
    exact QcoherentNormalizedProof.cancel_trans
      (moduleAbelianCohomologyLarge X F q) (e F q)
  refine ⟨c, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (congrArg (IsNormalizedCoherentEtaleComparison X) hc).mpr ha
  · intro F hF s
    have h := ha.2.1 F (moduleAbelianCohomologyLarge X F 0
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s))
    exact h.trans (congrArg
      (fun t ↦ ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F t))
      (moduleAbelianCohomologyLarge_zero X F s))
  · intro F G hF hG φ q x
    exact (congrArg (a G q)
      (QcoherentNormalizedProof.module_large_natural X q F G φ x)).trans
        (ha.1 F G φ q (moduleAbelianCohomologyLarge X F q x))
  · intro d hd
    have h := CoherentEtale.normalized_unique X m heff
      (fun F _ q ↦ ((moduleAbelianCohomologyLarge X F q).symm.trans
        (d F q)).toAddMonoidHom) a hd.1 ha
    funext F hF q
    apply AddEquiv.ext
    intro x
    have hv := congrArg (fun t : CoherentEtale.Family X ↦
      t F q (moduleAbelianCohomologyLarge X F q x)) h
    change d F q ((moduleAbelianCohomologyLarge X F q).symm
      (moduleAbelianCohomologyLarge X F q x)) = a F q
        (moduleAbelianCohomologyLarge X F q x) at hv
    change d F q x = a F q (moduleAbelianCohomologyLarge X F q x)
    exact (congrArg (d F q)
      ((moduleAbelianCohomologyLarge X F q).symm_apply_apply x)).symm.trans hv


end
end AlgebraicGeometry.Scheme.Modules
