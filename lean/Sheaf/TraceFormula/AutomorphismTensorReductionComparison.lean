/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import all Sheaf.Paper.CoefficientRingedSequenceSite
import all Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison

/-! # Automorphism tensor comparison for arbitrary strict quotient systems

This delivery records the current proof boundary for the two postponed comparison clauses.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3);
Stacks Project, Tags 03CZ, 03EK and 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).

Systems are the existing module sheaves on the vertical sequence site. Thus their
horizontal restriction maps are the actual quotient-linear transitions. Tensor
sheafification on this site is levelwise sheafification: covers are vertical.
The natural-number index n denotes the positive exponent n+1. Scheme and
coefficient universes are independent. No resolving-class condition is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.Limits.limit

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {S : Scheme.{t}} (g : S ⟶ S) [IsIso g]

/-- The site transport leaves the quotient index unchanged.
Source: Stacks 09A5 and blueprint rational-frobenius-integral-model (2)--(3)
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismSystemSite : ℕ × S.ProEt ⥤ ℕ × S.ProEt :=
  (𝟭 ℕ).prod (proEtaleIsoPostcompose g)

/-- The system site transport preserves the vertical sheaf condition.
Source: Stacks 09A5, 0941
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: on every vertical slice this is the recorded pro-etale site equivalence.
It preserves covers on that slice; the quotient index does not change. Applying
the sheaf condition slice by slice proves continuity on the sequence site. -/
@[instance] theorem trfAutomorphismSystemSite_continuous :
    (trfAutomorphismSystemSite g).IsContinuous
      (coefficientSequenceTopology (ProEt.topology S))
      (coefficientSequenceTopology (ProEt.topology S)) := by
  constructor
  intro G
  apply sequence_isSheaf_of_slices
  intro n
  have h := (Prod.sectR n S.ProEt).op_comp_isSheaf_of_types
    (ProEt.topology S) (coefficientSequenceTopology (ProEt.topology S)) G
  exact (proEtaleIsoPostcompose g).op_comp_isSheaf_of_isSheaf_type
    (ProEt.topology S) h

/-- The coefficient ring before transport of its action.
Source: Stacks 03CZ and blueprint rational-frobenius-integral-model (2)--(3)
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
abbrev trfAutomorphismRawRing :=
  ((trfAutomorphismSystemSite g).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)}
    (coefficientSequenceTopology (ProEt.topology S))
    (coefficientSequenceTopology (ProEt.topology S))).obj
      (coefficientSequenceCommRingSheaf l E S)

/-- The component is the recorded canonical constant-coefficient structure map.
Source: Stacks 09A5, 0H7J
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismCoefficientComponent (V : (ℕ × S.ProEt)ᵒᵖ) :
    (trfAutomorphismRawRing l E g).obj.obj V ⟶
      (coefficientSequenceCommRingSheaf l E S).obj.obj V :=
  CommRingCat.ofHom
    ((inverseImageFiniteCoefficientMap l E g V.unop.1).hom.app (op V.unop.2)).hom

/-- Vertical coefficient-component naturality at a fixed quotient level.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: apply naturality of the finite inverse-image coefficient isomorphism on the
pro-etale arrow f, then identify the fixed-index sequence-site restriction with
that pro-etale restriction and lift the equality through the commutative-ring
forgetful functor. -/
theorem trfAutomorphismCoefficientComponent_vertical
    (n : ℕ) {U V : S.ProEt} (f : U ⟶ V) :
    (trfAutomorphismRawRing l E g).obj.map
        (Prod.mkHom (𝟙 n) f).op ≫
      trfAutomorphismCoefficientComponent l E g (op (n, U)) =
    trfAutomorphismCoefficientComponent l E g (op (n, V)) ≫
      (coefficientSequenceCommRingSheaf l E S).obj.map
        (Prod.mkHom (𝟙 n) f).op := by
  change (coefficientSequenceCommRingSheaf l E S).obj.map
      (Prod.mkHom (𝟙 n) ((proEtaleIsoPostcompose g).map f)).op ≫ _ = _
  change ((coefficientSequenceCommRingSystem l E S).map (𝟙 (op n))).hom.app _ ≫
      ((coefficientSequenceCommRingSystem l E S).obj (op n)).obj.map
        ((proEtaleIsoPostcompose g).map f).op ≫ _ =
    _ ≫ (((coefficientSequenceCommRingSystem l E S).map (𝟙 (op n))).hom.app _ ≫
      ((coefficientSequenceCommRingSystem l E S).obj (op n)).obj.map f.op)
  erw [CategoryTheory.Functor.map_id]
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
  apply (forget₂ CommRingCat RingCat).map_injective
  exact (inverseImageFiniteCoefficientMap l E g n).hom.naturality f.op

private theorem trfSequence_forget_map {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (sheafCompose (ProEt.topology S) (forget₂ CommRingCat RingCat)).map
        ((coefficientSequenceCommRingSystem l E S).map f) =
      (integralCoefficientSheafSystem l E S).map f := by
  have h := map_opSequence
    (sheafCompose (ProEt.topology S) (forget₂ CommRingCat RingCat))
    (coefficientSequenceCommRingTransition l E S) (leOfHom f.unop)
  exact h

/-- Horizontal coefficient-component naturality for an arbitrary quotient arrow.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: identify both composites on constant sections with the quotient ring map,
using the normalized constant-section comparison and its naturality. Extend the
identity through sheafification and then use the sequence-site horizontal map.
Factor longer order arrows into adjacent quotient transitions. -/
theorem trfAutomorphismCoefficientComponent_horizontal
    (n m : ℕ) (h : n ≤ m) (U : S.ProEt) :
    (trfAutomorphismRawRing l E g).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U)).op ≫
      trfAutomorphismCoefficientComponent l E g (op (n, U)) =
    trfAutomorphismCoefficientComponent l E g (op (m, U)) ≫
      (coefficientSequenceCommRingSheaf l E S).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U)).op := by
  change (coefficientSequenceCommRingSheaf l E S).obj.map
      (Prod.mkHom (homOfLE h) ((proEtaleIsoPostcompose g).map (𝟙 U))).op ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  change (coefficientSequenceCommRingPresheaf l E S).map
      (Prod.mkHom (homOfLE h) (𝟙 ((proEtaleIsoPostcompose g).obj U))).op ≫ _ =
    _ ≫ (coefficientSequenceCommRingPresheaf l E S).map
      (Prod.mkHom (homOfLE h) (𝟙 U)).op
  erw [horizontal_map
    (coefficientSequenceCommRingSystem l E S ⋙ sheafToPresheaf _ CommRingCat)
    h (op ((proEtaleIsoPostcompose g).obj U)), horizontal_map
    (coefficientSequenceCommRingSystem l E S ⋙ sheafToPresheaf _ CommRingCat) h (op U)]
  apply (forget₂ CommRingCat RingCat).map_injective
  have hh := (coefficientDiagramMap l E g).naturality (homOfLE h).op
  have hh' := congrArg (fun k ↦ k.hom.app (op U)) hh
  simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at hh'
  simp only [CategoryTheory.Functor.map_comp]
  have ha := congrArg (fun k ↦ k.hom.app (op ((proEtaleIsoPostcompose g).obj U)))
    (trfSequence_forget_map l E (S := S) (homOfLE h).op)
  have hb := congrArg (fun k ↦ k.hom.app (op U))
    (trfSequence_forget_map l E (S := S) (homOfLE h).op)
  change (forget₂ CommRingCat RingCat).map
      (((coefficientSequenceCommRingSystem l E S).map (homOfLE h).op).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))) ≫
      (inverseImageFiniteCoefficientMap l E g n).hom.app (op U) =
    (inverseImageFiniteCoefficientMap l E g m).hom.app (op U) ≫
      (forget₂ CommRingCat RingCat).map
        (((coefficientSequenceCommRingSystem l E S).map (homOfLE h).op).hom.app (op U))
  change (forget₂ CommRingCat RingCat).map
      (((coefficientSequenceCommRingSystem l E S).map (homOfLE h).op).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))) = _ at ha
  change (forget₂ CommRingCat RingCat).map
      (((coefficientSequenceCommRingSystem l E S).map (homOfLE h).op).hom.app (op U)) = _ at hb
  erw [ha, hb]
  exact hh'

/-- These components commute with vertical restrictions and actual quotient maps.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: vertical naturality is naturality of the canonical constant-sheaf map.
For an adjacent horizontal arrow, both composites extend the same quotient map
on constant sections, giving rho c = c F(rho). General horizontal arrows are
composites of adjacent ones. Factor a general sequence-site arrow into its
vertical and horizontal parts and combine these identities. -/
theorem trfAutomorphismCoefficientComponent_naturality
    {V W : (ℕ × S.ProEt)ᵒᵖ} (f : V ⟶ W) :
    (trfAutomorphismRawRing l E g).obj.map f ≫
        trfAutomorphismCoefficientComponent l E g W =
      trfAutomorphismCoefficientComponent l E g V ≫
        (coefficientSequenceCommRingSheaf l E S).obj.map f := by
  rcases f with ⟨f₁, f₂⟩
  let h : (unop W).1 ≤ (unop V).1 := leOfHom f₁
  let a : (unop W) ⟶ ((unop W).1, (unop V).2) :=
    Prod.mkHom (𝟙 (unop W).1) f₂
  let b : ((unop W).1, (unop V).2) ⟶ (unop V) :=
    Prod.mkHom (homOfLE h) (𝟙 (unop V).2)
  have hf : (f₁, f₂) = a ≫ b := by
    apply Prod.ext
    · apply Subsingleton.elim
    · simp [a, b]
  have hfop : op (f₁, f₂) = b.op ≫ a.op := by
    rw [hf]
    exact op_comp
  change (trfAutomorphismRawRing l E g).obj.map (op (f₁, f₂)) ≫
      trfAutomorphismCoefficientComponent l E g W =
    trfAutomorphismCoefficientComponent l E g V ≫
      (coefficientSequenceCommRingSheaf l E S).obj.map (op (f₁, f₂))
  rw [hfop, Functor.map_comp]
  have hh := trfAutomorphismCoefficientComponent_horizontal l E g
    (unop W).1 (unop V).1 h (unop V).2
  have hva := trfAutomorphismCoefficientComponent_vertical l E g
    (unop W).1 f₂
  have hva' : (trfAutomorphismRawRing l E g).obj.map a.op ≫
      trfAutomorphismCoefficientComponent l E g W =
    trfAutomorphismCoefficientComponent l E g (op ((unop W).1, (unop V).2)) ≫
      (coefficientSequenceCommRingSheaf l E S).obj.map a.op := by
    simpa [a] using hva
  rw [Category.assoc, hva', ← Category.assoc, hh]
  rw [Category.assoc]
  congr 1
  rw [← Functor.map_comp]

/-- The actual system coefficient map, retaining the reduction squares.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismCoefficientMap :
    trfAutomorphismRawRing l E g ⟶ coefficientSequenceCommRingSheaf l E S where
  hom :=
    { app := trfAutomorphismCoefficientComponent l E g
      naturality := fun {_ _} f ↦ trfAutomorphismCoefficientComponent_naturality l E g f }

/-- The system coefficient map is invertible, component by component.
Source: Stacks 09A5 and blueprint rational-frobenius-integral-model (2)--(3)
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: each component is c_n, which is invertible by the recorded constant
coefficient comparison. Inverting its naturality equations gives a natural
inverse. The sectionwise inverse identities give the sheaf inverse identities. -/
@[instance] theorem trfAutomorphismCoefficientMap_isIso :
    IsIso (trfAutomorphismCoefficientMap l E g) := by
  have : ∀ V, IsIso ((trfAutomorphismCoefficientMap l E g).hom.app V) := by
    intro V
    have : IsIso ((forget₂ CommRingCat RingCat).map
        ((trfAutomorphismCoefficientMap l E g).hom.app V)) := by
      change IsIso ((inverseImageFiniteCoefficientMap l E g V.unop.1).hom.app
        (op V.unop.2))
      infer_instance
    exact isIso_of_reflects_iso _ (forget₂ CommRingCat RingCat)
  have h : IsIso (trfAutomorphismCoefficientMap l E g).hom :=
    NatIso.isIso_of_isIso_app (trfAutomorphismCoefficientMap l E g).hom
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (trfAutomorphismCoefficientMap l E g)
    (sheafToPresheaf _ CommRingCat) h inferInstance

/-- Continuous site transport with its original coefficient action, without an
identity restriction-of-scalars wrapper.
Source: Stacks 03CZ, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfRawModuleTransport
    {C D : Type t} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{v}) :
    SheafOfModules.{v} R ⥤
      SheafOfModules.{v} ((F.sheafPushforwardContinuous RingCat J K).obj R) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ F R.obj).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj
        ⟨M.val.presheaf, M.isSheaf⟩).property }
  map f := { val := (PresheafOfModules.pushforward₀ F R.obj).map f.val }

/-- Inverse image before transporting coefficients: its sections are M_n(gU).
Source: Stacks 09A5, 03CZ
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismRawModules : coefficientSequenceModules l E S ⥤
    ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (trfAutomorphismRawRing l E g)) :=
  trfRawModuleTransport (trfAutomorphismSystemSite g)
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E S))

/-- The system inverse image with action transported through c_n inverse.
Source: Stacks 09A5, 03CZ
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismSystemInverse :
    coefficientSequenceModules l E S ⥤ coefficientSequenceModules l E S :=
  trfAutomorphismRawModules l E g ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (inv (trfAutomorphismCoefficientMap l E g)))

/-- Identity and composition laws of the actual sheafified tensor maps.
Source: Stacks 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: before sheafification scalar extension acts on a map as identity tensor
that map. The sectionwise tensor functors preserve identities and composites.
The additive sheafification functor preserves these equations. -/
theorem trfAutomorphismTensor_laws :
    (∀ M : ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (trfAutomorphismRawRing l E g)),
      SheafOfModules.changeOfRingsHomOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (trfAutomorphismCoefficientMap l E g) M (𝟙 M) = 𝟙 _) ∧
    (∀ {M N P : ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (trfAutomorphismRawRing l E g))} (f : M ⟶ N) (h : N ⟶ P),
      SheafOfModules.changeOfRingsHomOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
          (trfAutomorphismCoefficientMap l E g) M (f ≫ h) =
        SheafOfModules.changeOfRingsHomOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
            (trfAutomorphismCoefficientMap l E g) M f ≫
          SheafOfModules.changeOfRingsHomOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
            (trfAutomorphismCoefficientMap l E g) N h) := by
  constructor
  · intro M
    exact SheafOfModules.scalarExtension_map_id (trfAutomorphismCoefficientMap l E g) M
  · intro M N P f h
    exact SheafOfModules.scalarExtension_map_comp (trfAutomorphismCoefficientMap l E g) f h

/-- Sheafified tensor extension along the actual system coefficient map.
Source: Stacks 03CZ, 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismTensorExtension :
    ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology S))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (trfAutomorphismRawRing l E g)) ⥤ coefficientSequenceModules l E S where
  obj := SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (trfAutomorphismCoefficientMap l E g)
  map := fun f ↦ SheafOfModules.changeOfRingsHomOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (trfAutomorphismCoefficientMap l E g) _ f
  map_id := (trfAutomorphismTensor_laws l E g).1
  map_comp := fun f h ↦ (trfAutomorphismTensor_laws l E g).2 f h

/-- The tensor-pullback functor on the actual strict systems.
Source: Stacks 03CZ, 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
abbrev trfAutomorphismSystemTensor :=
  trfAutomorphismRawModules l E g ⋙ trfAutomorphismTensorExtension l E g

private theorem trfChange_map_add
    {C : Type t} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    {R R' : Sheaf J CommRingCat.{v}} (α : R ⟶ R')
    {M N : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f h : M ⟶ N) :
    SheafOfModules.changeOfRingsHomOfUniverses α M (f + h) =
      SheafOfModules.changeOfRingsHomOfUniverses α M f +
        SheafOfModules.changeOfRingsHomOfUniverses α M h := by
  let A := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R'
  let a := PresheafOfModules.sheafification.{v} (𝟙 A.obj)
  have : a.Additive := Functor.additive_of_preserves_binary_products a
  change a.map _ = a.map _ + a.map _
  rw [← a.map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have : (ModuleCat.extendScalars (α.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (α.hom.app U).hom).left_adjoint_additive
  exact (ModuleCat.extendScalars (α.hom.app U).hom).map_add

/-- The two system functors are additive, hence act on ordinary unbounded complexes.
Source: Stacks 03CZ, 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: inverse image retains the component abelian groups and maps, while scalar
transport changes only the action. Tensor extension preserves sums of maps by
the tensor universal property and additive sheafification. -/
theorem trfAutomorphismSystem_additive :
    (trfAutomorphismSystemInverse l E g).Additive ∧
      (trfAutomorphismSystemTensor l E g).Additive := by
  constructor
  · constructor
    intro M N f h
    ext U x
    rfl
  · constructor
    intro M N f h
    exact trfChange_map_add (trfAutomorphismCoefficientMap l E g)
      ((trfAutomorphismRawModules l E g).map f)
      ((trfAutomorphismRawModules l E g).map h)

/-- Additive structure for termwise inverse image.
Source: Stacks 03CZ
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
instance trfAutomorphismSystemInverse_additive :
    (trfAutomorphismSystemInverse l E g).Additive :=
  (trfAutomorphismSystem_additive l E g).1

/-- Additive structure for termwise tensor pullback.
Source: Stacks 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
instance trfAutomorphismSystemTensor_additive :
    (trfAutomorphismSystemTensor l E g).Additive :=
  (trfAutomorphismSystem_additive l E g).2

/-- The image under sheafification of a local tensor x tensor a.
Source: Stacks 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismTensorSection (M : coefficientSequenceModules l E S)
    (n : ℕ) (U : S.ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)))
    (a : (integralCoefficientSheaf l E S n).obj.obj (op U)) :
    ((trfAutomorphismSystemTensor l E g).obj M).val.obj (op (n, U)) :=
  SheafOfModules.scalarExtensionRingIsoTmul.{t + 1, t, max u (t + 1), max u (t + 1)}
    (trfAutomorphismCoefficientMap l E g)
    ((trfAutomorphismRawModules l E g).obj M) (op (n, U)) x a

/-- The finite coefficient map with its commutative structure retained.
Source: Stacks 09A5, 0H7J
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismFiniteCoefficientMap (n : ℕ) :
    (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
        (integralCoefficientCommRingSheaf l E S n) ⟶
      integralCoefficientCommRingSheaf l E S n where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom
        ((inverseImageFiniteCoefficientMap l E g n).hom.app U).hom
      naturality := fun {_ _} f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((inverseImageFiniteCoefficientMap l E g n).hom.naturality f) }

/-- Finite inverse image before transporting the coefficient action.
Source: Stacks 09A5, 03CZ
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismFiniteRaw (n : ℕ) :
    normalizedDVRModules l E S n ⥤
      ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
              (integralCoefficientCommRingSheaf l E S n))) :=
  trfRawModuleTransport (proEtaleIsoPostcompose g) (integralCoefficientSheaf l E S n)

/-- The actual levelwise tensor object, using the recorded sheafification.
Source: Stacks 03CZ, 03EK
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismFiniteTensor (M : coefficientSequenceModules l E S) (n : ℕ) :
    normalizedDVRModules l E S n :=
  SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (trfAutomorphismFiniteCoefficientMap l E g n)
    ((trfAutomorphismFiniteRaw l E g n).obj
      ((coefficientSequenceEvaluation l E S n).obj M))

/-- System tensor sheafification evaluates to the actual finite tensor sheaf,
with its canonical normalization on every local tensor.
Source: Stacks 03EK, 0941
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).
Proof: the sequence topology has exactly the vertical sheaf condition. Restrict
the sectionwise scalar-extension presheaf to a slice n. Its values, restrictions
and pure tensors are precisely those of finite scalar extension along c_n.
The two sheafification universal properties give inverse maps extending the
identity on that presheaf. Uniqueness gives the displayed generator formula. -/
theorem trfAutomorphismTensorEvaluation :
    ∃ e : ∀ (M : coefficientSequenceModules l E S) (n : ℕ),
      (coefficientSequenceEvaluation l E S n).obj
          ((trfAutomorphismSystemTensor l E g).obj M) ≅
        trfAutomorphismFiniteTensor l E g M n,
      ∀ (M : coefficientSequenceModules l E S) (n : ℕ) (U : S.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)))
        (a : (integralCoefficientSheaf l E S n).obj.obj (op U)),
        (e M n).hom.val.app (op U)
            (coefficientEvaluationSection l E S
              ((trfAutomorphismSystemTensor l E g).obj M) n (op U)
                (trfAutomorphismTensorSection l E g M n U x a)) =
          SheafOfModules.scalarExtensionRingIsoTmul.{t + 1, t, max u (t + 1), max u (t + 1)}
            (trfAutomorphismFiniteCoefficientMap l E g n)
            ((trfAutomorphismFiniteRaw l E g n).obj
              ((coefficientSequenceEvaluation l E S n).obj M)) (op U)
              (coefficientEvaluationSection l E S M n
                (op ((proEtaleIsoPostcompose g).obj U)) x) a := by
  sorry
/-- The adjacent quotient arrow of the sequence site, with its endpoints explicit.
Source: Stacks 0941
(blueprint: lem-trf-automorphism-tensor-reduction-comparison). -/
def trfAutomorphismSystemStep (n : ℕ) (U : S.ProEt) :
    op (n + 1, U) ⟶ op (n, U) :=
  (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U)).op

private theorem trfSystemSite_step (n : ℕ) (U : S.ProEt) :
    (trfAutomorphismSystemSite g).map (trfAutomorphismSystemStep n U).unop =
      (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)).unop := by
  change Prod.mkHom (homOfLE (Nat.le_succ n))
      ((proEtaleIsoPostcompose g).map (𝟙 U)) =
    Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 _)
  rw [CategoryTheory.Functor.map_id]

private theorem trfCoefficient_step (n : ℕ) (U : S.ProEt) :
    (coefficientSequenceCommRingSheaf l E S).obj.map (trfAutomorphismSystemStep n U) =
      (coefficientSequenceCommRingTransition l E S n).hom.app (op U) := by
  change ((coefficientSequenceCommRingSystem l E S).map
      (homOfLE (Nat.le_succ n)).op).hom.app (op U) ≫
    ((coefficientSequenceCommRingSystem l E S).obj (op n)).obj.map (𝟙 (op U)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only [coefficientSequenceCommRingSystem]
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private theorem trfCoefficientTransition_apply (n : ℕ) (U : S.ProEt)
    (a : (integralCoefficientSheaf l E S (n + 1)).obj.obj (op U)) :
    (coefficientSequenceCommRingTransition l E S n).hom.app (op U) a =
      (integralCoefficientSheafTransition l E S n).hom.app (op U) a := rfl

private theorem trfRawCoefficient_step (n : ℕ) (U : S.ProEt) :
    (trfAutomorphismRawRing l E g).obj.map (trfAutomorphismSystemStep n U) =
      (coefficientSequenceCommRingTransition l E S n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) := by
  change (coefficientSequenceCommRingSheaf l E S).obj.map
    ((trfAutomorphismSystemSite g).map (trfAutomorphismSystemStep n U).unop).op = _
  rw [trfSystemSite_step]
  change (coefficientSequenceCommRingSheaf l E S).obj.map
    (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)) = _
  exact trfCoefficient_step l E n ((proEtaleIsoPostcompose g).obj U)

private theorem trfFiniteTransition (n : ℕ) :
    inverseImageFiniteCoefficientMap l E g (n + 1) ≫
        integralCoefficientSheafTransition l E S n =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
          (integralCoefficientSheafTransition l E S n) ≫
        inverseImageFiniteCoefficientMap l E g n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have h := (trfAutomorphismCoefficientComponent_naturality l E g
    (trfAutomorphismSystemStep n U.unop)).symm
  rw [trfRawCoefficient_step, trfCoefficient_step] at h
  exact congrArg ((forget₂ CommRingCat RingCat).map) h

private theorem trfModule_map_apply
    {C : Type t} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{v}}
    (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U) :
    M.map f x = M.presheaf.map f x := rfl

private theorem trfRawModule_step (M : coefficientSequenceModules l E S)
    (n : ℕ) (U : S.ProEt)
    (x : M.val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))) :
    ((trfAutomorphismRawModules l E g).obj M).val.presheaf.map
        (trfAutomorphismSystemStep n U) x =
      M.val.presheaf.map
        (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)) x := by
  change M.val.presheaf.map
    ((trfAutomorphismSystemSite g).map (trfAutomorphismSystemStep n U).unop).op x = _
  rw [trfSystemSite_step]
  rfl

private theorem trfInverseModule_step (M : coefficientSequenceModules l E S)
    (n : ℕ) (U : S.ProEt)
    (x : M.val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))) :
    ((trfAutomorphismSystemInverse l E g).obj M).val.map
        (trfAutomorphismSystemStep n U) x =
      M.val.presheaf.map
        (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)) x := by
  rw [trfModule_map_apply]
  exact trfRawModule_step l E g M n U x

private theorem trfTransport_exact
    {C D : Type t} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (F : C ⥤ D) [F.IsContinuous J K]
    [((F.sheafPushforwardContinuous AddCommGrpCat.{v} J K)).IsEquivalence]
    (R : Sheaf K RingCat.{v}) (R' : Sheaf J RingCat.{v})
    (α : R' ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) :
    PreservesFiniteLimits (trfRawModuleTransport F R ⋙ SheafOfModules.restrictScalars α) ∧
      PreservesFiniteColimits (trfRawModuleTransport F R ⋙ SheafOfModules.restrictScalars α) := by
  let G := trfRawModuleTransport F R ⋙ SheafOfModules.restrictScalars α
  let T := SheafOfModules.toSheaf.{v} R'
  let H := F.sheafPushforwardContinuous AddCommGrpCat.{v} J K
  let d : G ⋙ T ≅ SheafOfModules.toSheaf R ⋙ H :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
      (fun f ↦ by ext U x; rfl)
  have : PreservesFiniteLimits (G ⋙ T) := preservesFiniteLimits_of_natIso d.symm
  have : PreservesFiniteColimits (G ⋙ T) := preservesFiniteColimits_of_natIso d.symm
  have : ReflectsFiniteLimits T :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ T,
    preservesFiniteColimits_of_reflects_of_preserves _ T⟩

private theorem trfInverse_exact :
    PreservesFiniteLimits (trfAutomorphismSystemInverse l E g) ∧
      PreservesFiniteColimits (trfAutomorphismSystemInverse l E g) := by
  let J := coefficientSequenceTopology (ProEt.topology S)
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E S)
  let ep := proEtaleIsoPostcompose_equivalence g
  let es : S.ProEt ≌ S.ProEt := CategoryTheory.Equivalence.mk
    (proEtaleIsoPostcompose g) (proEtaleIsoPostcompose (inv g))
    ep.2.1.some.symm ep.2.2.1.some
  let eqv := (CategoryTheory.Equivalence.refl (C := ℕ)).prod es
  have : eqv.functor.IsContinuous J J := trfAutomorphismSystemSite_continuous g
  have : eqv.inverse.IsContinuous J J := trfAutomorphismSystemSite_continuous (inv g)
  let F := eqv.functor
  let G := eqv.inverse
  have := Functor.isContinuous_comp F G J J J
  have := Functor.isContinuous_comp G F J J J
  let H := F.sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)} J J
  let H' := G.sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)} J J
  let EH : Sheaf J AddCommGrpCat.{max u (t + 1)} ≌
      Sheaf J AddCommGrpCat.{max u (t + 1)} :=
    CategoryTheory.Equivalence.mk H H'
      ((Functor.sheafPushforwardContinuousComp G F _ J J J ≪≫
        Functor.sheafPushforwardContinuousId' eqv.counitIso _ J).symm)
      (Functor.sheafPushforwardContinuousComp F G _ J J J ≪≫
        Functor.sheafPushforwardContinuousId' eqv.unitIso.symm _ J)
  have : H.IsEquivalence := EH.isEquivalence_functor
  have : ((trfAutomorphismSystemSite g).sheafPushforwardContinuous
      AddCommGrpCat.{max u (t + 1)} J J).IsEquivalence := EH.isEquivalence_functor
  exact trfTransport_exact (trfAutomorphismSystemSite g) R R
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (inv (trfAutomorphismCoefficientMap l E g)))

private theorem trfCoefficient_inv_app (n : ℕ) (U : S.ProEt) :
    (forget₂ CommRingCat RingCat).map
        ((inv (trfAutomorphismCoefficientMap l E g)).hom.app (op (n, U))) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) := by
  apply (cancel_epi ((inverseImageFiniteCoefficientMap l E g n).hom.app (op U))).mp
  rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    IsIso.hom_inv_id]
  change (forget₂ CommRingCat RingCat).map
    ((trfAutomorphismCoefficientMap l E g).hom.app (op (n, U))) ≫ _ = 𝟙 _
  rw [← Functor.map_comp, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, IsIso.hom_inv_id]
  rfl

private theorem trfInverse_smul (M : coefficientSequenceModules l E S)
    (n : ℕ) (U : S.ProEt)
    (a : (integralCoefficientSheaf l E S n).obj.obj (op U))
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    a • (show ((trfAutomorphismSystemInverse l E g).obj M).val.obj (op (n, U)) from x) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) a • x := by
  change (forget₂ CommRingCat RingCat).map
    ((inv (trfAutomorphismCoefficientMap l E g)).hom.app (op (n, U))) a • x = _
  rw [trfCoefficient_inv_app]
  rfl

private theorem trfScalarSection_eq
    {C : Type t} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    {R R' : Sheaf J CommRingCat.{v}} (α : R ⟶ R')
    (M : SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (a : R'.obj.obj U) :
    SheafOfModules.scalarExtensionRingIsoTmul.{t, u, v, v} α M U x a =
      SheafOfModules.scalarExtensionSection α M U a x := rfl

private theorem trfTensorSection_naturality
    {C : Type t} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    {R R' : Sheaf J CommRingCat.{v}} (α : R ⟶ R')
    (M : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (a : R'.obj.obj U) :
    (SheafOfModules.changeOfRingsOfUniverses α M).val.presheaf.map f
        (SheafOfModules.scalarExtensionRingIsoTmul.{t, u, v, v} α M U x a) =
      SheafOfModules.scalarExtensionRingIsoTmul.{t, u, v, v} α M V
        (M.val.presheaf.map f x) (R'.obj.map f a) := by
  have h := SheafOfModules.scalarExtensionSection_naturality α M f a x
  simpa only [trfScalarSection_eq, trfModule_map_apply] using h

/-- Tensor-unit comparison on arbitrary ordinary unbounded strict system complexes,
including the actual quotient and completed coefficient squares and exactness.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3);
Stacks 03CZ, 03EK, 09A5
(blueprint: lem-trf-automorphism-tensor-reduction-comparison).

Proof, following all seven steps of the node:
1. Constant-coefficient naturality gives rho c = c F(rho). The completed map
is the recorded limit lift, so its projections give pi c_hat = c F(pi).
Invert these squares to compare the two transported scalar actions.
2. Apply lem-weil-sheaf-scalar-extension-ring-iso to c_n in every degree.
Its inverse sends x to the sheafified x tensor 1, and its forward map sends
x tensor a to c_n inverse(a) x. Naturality in each differential gives chain maps.
3. Inverse image of quotient-linearity, combined with the inverted reduction
square, makes F(v_n) quotient-linear for the transported B_n actions.
4. Conjugate F(v_n) by the two scalar-extension isomorphisms. Tensor balancing
gives exactly x tensor a to F(v_n)(x) tensor rho(a). This is a sheaf morphism;
no assertion that all tensor-sheaf sections are pure is used. On x tensor 1
the formula reduces to the displayed transition square.
5. The scalar-extension comparison is natural in module maps. Applying this
to differentials and system chain maps gives a natural isomorphism on the
ordinary unbounded complex category, including all transition compatibilities.
6. The completed projection square identifies the transported completed action
with the B_n action restricted through pi_n. Hence both comparison directions
and both transition maps remain linear over the completed ring.
7. The underlying inverse-image functor is exact by the recorded site
equivalence. Action transport changes no underlying abelian sheaf or map.
Module kernels and cokernels, then system kernels and cokernels, are computed
componentwise (lem-coef-semilinear-derived-sections). Thus G is exact. The
argument uses no flatness, cartesianness, boundedness or Tor-amplitude hypothesis. -/
theorem automorphismTensorReductionComparison
    (_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)) :
    PreservesFiniteLimits (trfAutomorphismSystemInverse l E g) ∧
    PreservesFiniteColimits (trfAutomorphismSystemInverse l E g) ∧
    (∀ n : ℕ,
      inverseImageFiniteCoefficientMap l E g (n + 1) ≫
          integralCoefficientSheafTransition l E S n =
        (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
            (integralCoefficientSheafTransition l E S n) ≫
          inverseImageFiniteCoefficientMap l E g n) ∧
    (∀ n : ℕ,
      inverseImageCompletedCoefficientMap l E g ≫
          limit.π (integralCoefficientSheafSystem l E S) (op n) =
        (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
            (limit.π (integralCoefficientSheafSystem l E S) (op n)) ≫
          inverseImageFiniteCoefficientMap l E g n) ∧
    ∃ j : (trfAutomorphismSystemInverse l E g).mapHomologicalComplex (.up ℤ) ≅
        (trfAutomorphismSystemTensor l E g).mapHomologicalComplex (.up ℤ),
      (∀ (M : CochainComplex (coefficientSequenceModules l E S) ℤ)
        (q : ℤ) (n : ℕ) (U : S.ProEt)
        (x : (M.X q).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((j.hom.app M).f q).val.app (op (n, U)) x =
          trfAutomorphismTensorSection l E g (M.X q) n U x 1) ∧
      (∀ (M : CochainComplex (coefficientSequenceModules l E S) ℤ)
        (q : ℤ) (n : ℕ) (U : S.ProEt)
        (x : (M.X q).val.obj (op (n, (proEtaleIsoPostcompose g).obj U)))
        (a : (integralCoefficientSheaf l E S n).obj.obj (op U)),
        ((j.inv.app M).f q).val.app (op (n, U))
            (trfAutomorphismTensorSection l E g (M.X q) n U x a) =
          (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) a • x) ∧
      (∀ (M : CochainComplex (coefficientSequenceModules l E S) ℤ)
        (q : ℤ) (n : ℕ) (U : S.ProEt)
        (x : (M.X q).val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U)))
        (a : (integralCoefficientSheaf l E S (n + 1)).obj.obj (op U)),
        (((trfAutomorphismSystemTensor l E g).obj (M.X q)).val.presheaf.map
            (trfAutomorphismSystemStep n U))
            (trfAutomorphismTensorSection l E g (M.X q) (n + 1) U x a) =
          trfAutomorphismTensorSection l E g (M.X q) n U
            ((M.X q).val.presheaf.map
              (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)) x)
            ((integralCoefficientSheafTransition l E S n).hom.app (op U) a)) ∧
      (∀ (M : CochainComplex (coefficientSequenceModules l E S) ℤ)
        (q : ℤ) (n : ℕ) (U : S.ProEt)
        (x : (M.X q).val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))),
        (((trfAutomorphismSystemTensor l E g).obj (M.X q)).val.presheaf.map
            (trfAutomorphismSystemStep n U))
            (((j.hom.app M).f q).val.app (op (n + 1, U)) x) =
          ((j.hom.app M).f q).val.app (op (n, U))
            ((M.X q).val.presheaf.map
              (trfAutomorphismSystemStep n ((proEtaleIsoPostcompose g).obj U)) x)) ∧
      (∀ (M : CochainComplex (coefficientSequenceModules l E S) ℤ)
        (q : ℤ) (n : ℕ) (U : S.ProEt)
        (b : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj (op U))
        (x : (M.X q).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((j.hom.app M).f q).val.app (op (n, U))
            ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U)
              ((limit.π (integralCoefficientSheafSystem l E S) (op n)).hom.app
                (op U) b) • x) =
          (limit.π (integralCoefficientSheafSystem l E S) (op n)).hom.app (op U) b •
            ((j.hom.app M).f q).val.app (op (n, U)) x) := by
  obtain ⟨θ, hθ, hη, hnat⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{t + 1, t, max u (t + 1),
      max u (t + 1)} (asIso (trfAutomorphismCoefficientMap l E g))
  let e : trfAutomorphismSystemTensor l E g ≅ trfAutomorphismSystemInverse l E g :=
    NatIso.ofComponents
      (fun M ↦ θ ((trfAutomorphismRawModules l E g).obj M))
      (fun f ↦ hnat _ _ ((trfAutomorphismRawModules l E g).map f))
  obtain ⟨hlim, hcolim⟩ := trfInverse_exact l E g
  refine ⟨hlim, hcolim, ?_, ?_, ?_⟩
  · intro n
    exact trfFiniteTransition l E g n
  · intro n
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π,
      inverseImageCompletedCoefficientComponent]
  · refine ⟨NatIso.mapHomologicalComplex e.symm (.up ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · intro M q n U x
      exact hη ((trfAutomorphismRawModules l E g).obj (M.X q)) (op (n, U)) x
    · intro M q n U x a
      have h := hθ ((trfAutomorphismRawModules l E g).obj (M.X q)) (op (n, U)) x a
      change _ = (inv (trfAutomorphismCoefficientMap l E g)).hom.app (op (n, U)) a • x at h
      rw [← trfCoefficient_inv_app l E g n U]
      exact h
    · intro M q n U x a
      have h := trfTensorSection_naturality (trfAutomorphismCoefficientMap l E g)
        ((trfAutomorphismRawModules l E g).obj (M.X q))
        (trfAutomorphismSystemStep n U) x a
      rw [trfCoefficient_step] at h
      erw [trfCoefficientTransition_apply l E n U a] at h
      rw [trfRawModule_step] at h
      exact h
    · intro M q n U x
      have h := PresheafOfModules.naturality_apply
        (e.inv.app (M.X q)).val (trfAutomorphismSystemStep n U) x
      rw [trfInverseModule_step, trfModule_map_apply] at h
      exact h.symm
    · intro M q n U b x
      have h := ((e.inv.app (M.X q)).val.app (op (n, U))).hom.map_smul
        ((limit.π (integralCoefficientSheafSystem l E S) (op n)).hom.app (op U) b) x
      rw [trfInverse_smul] at h
      exact h

end WeilConjectures
