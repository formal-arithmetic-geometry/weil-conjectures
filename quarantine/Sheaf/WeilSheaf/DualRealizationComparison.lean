/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetful
public import Sheaf.Paper.NativeWeilClosedForgetful
import Sheaf.WeilSheaf.OrdinaryClosedPresentation
import Sheaf.WeilSheaf.StructuralOmegaHomPairs

/-! # Native dualizing Hom and constructible coefficient realization

Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation and
exceptional counit paragraphs; native refinement, proof steps 1--6
(blueprint: lem-sf-weil-dual-realization-comparison).

The source is the derived category of abelian Weil sheaves. The ordinary section
presentation and the change of algebraic closure are the recorded ones. The
comparison below is specified as forgetful Hom, Hom(j,h), inverse realized Hom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u a b a₁ b₁ a₂ b₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeDualRealization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D)

/-- The ordinary presentation change, including the actual algebraic-closure transport.
Source: native exceptional comparison, closureMap and U
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def transport :=
  (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
    sectionDerived l (geometric D X).base.left (R.data (geometric D X)).realization

/-- Forgetting on the ambient native derived category, before imposing constructibility.
Source: native closed comparison and native exceptional comparison
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def forget := nativeForget D.k₀ l X.base.left ⋙ transport D l R X

/-- The actual structural arrow, as a morphism of models over Spec k0.
Source: blueprint, dualizing object of the structural morphism
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def structureArrow : X.base ⟶ (point D).base :=
  Over.homMk X.base.hom (by simp [point])

/-- Separatedness of the structural arrow is the model's separatedness.
Source: blueprint, structural morphism
(blueprint: lem-sf-weil-dual-realization-comparison). -/
instance structureArrowSeparated : IsSeparated (structureArrow D X).left := X.separated

/-- Local finite type of the structural arrow is the model's finite type.
Source: blueprint, structural morphism
(blueprint: lem-sf-weil-dual-realization-comparison). -/
instance structureArrowFiniteType : LocallyOfFiniteType (structureArrow D X).left :=
  X.finiteType

/-- Quasi-compactness of the structural arrow is part of finite type.
Source: blueprint, structural morphism
(blueprint: lem-sf-weil-dual-realization-comparison). -/
instance structureArrowQuasiCompact : QuasiCompact (structureArrow D X).left := X.quasiCompact

variable (G : W D l (point D) ⥤ W D l X)
  (adj : nativeShriek D l (structureArrow D X) ⊣ G)

/-- The native dualizing object for the specified right adjoint, with no choice of adjoint.
Source: blueprint, omega_X is exceptional inverse image of Omega^W
(blueprint: lem-sf-weil-dual-realization-comparison). -/
abbrev nativeOmega := G.obj (constant D l (point D))

/-- The ordinary dualizing object for the literal geometric structural morphism.
Source: blueprint, omega_Y is exceptional inverse image of Omega
(blueprint: lem-sf-weil-dual-realization-comparison). -/
abbrev coefficientOmega (S : StructuralSystem D l X)
    (c : Compactification (geometric D X).base.hom) :=
  (S.ring.operation c .closed).G.obj (geometricPointOmega D l R)

/-- The counit-normalized exceptional comparison from the recorded dependency.
Source: native_exceptional_forgetful, structural specialization
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def omegaComparison (P : Package D l R) (S : StructuralSystem D l X)
    (c : Compactification (geometric D X).base.hom) :
    (forget D l R X).obj (nativeOmega D l X G).obj ≅
      (rho D l R X).obj (coefficientOmega D l R X S c) :=
  P.actualSpecialization X (structureArrow D X) S c G adj

/-- The realized ordinary closed structure, retaining the realization's exact unit data.
Source: BS 6.8.15 (blueprint: lem-sf-weil-dual-realization-comparison). -/
def closed : CoefficientClosedStructure
    (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization) := by
  letI := (R.data (geometric D X)).units
  exact (R.data (geometric D X)).tensor.closed

/-- The fixed common-stage tensor, with the realization's residue-field unit instances.
Source: coefficient-passage tensor (blueprint: lem-sf-weil-dual-realization-comparison). -/
def coefficientTensor : C D l X × C D l X ⥤ C D l X := by
  letI := (R.data (geometric D X)).units
  exact commonStageDerivedTensor l (PadicAlgCl l) (geometric D X).base.left

/-- The specified symmetric strong tensorator of rho, with no new choice of tensor.
Source: BS 6.8.15 (blueprint: lem-sf-weil-dual-realization-comparison). -/
def tensorator :
    ((rho D l R X).prod (rho D l R X)) ⋙ (closed D l R X).tensor ≅
      coefficientTensor D l R X ⋙ rho D l R X := by
  letI := (R.data (geometric D X)).units
  exact (R.data (geometric D X)).tensor.tensor

/-- The fixed evaluation-transpose realized Hom comparison beta.
Source: BS 6.8.15 (blueprint: lem-sf-weil-dual-realization-comparison). -/
def beta (Q : (commonStageHomPairs l (PadicAlgCl l)
    (geometric D X).base.left).FullSubcategory) :
    (rho D l R X).obj
        ((commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left).obj Q) ⟶
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).obj
        (op ((rho D l R X).obj Q.obj.1.unop), (rho D l R X).obj Q.obj.2) := by
  letI := (R.data (geometric D X)).units
  exact homComparison l (geometric D X).base.left (R.data (geometric D X)).realization
    (R.data (geometric D X)).tensor Q

/-- The fixed coefficient-passage evaluation, before applying rho.
Source: coefficient-passage closed adjunction
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def coefficientEvaluation (Q : (commonStageHomPairs l (PadicAlgCl l)
    (geometric D X).base.left).FullSubcategory) :
    (coefficientTensor D l R X).obj
        ((commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left).obj Q,
          Q.obj.1.unop) ⟶ Q.obj.2 := by
  letI := (R.data (geometric D X)).units
  exact (podCommonClosed l (PadicAlgCl l) (geometric D X).base.left).evaluation Q

/-- Coefficient-passage Hom on the chosen inverse images of native objects.
Its arrows are the maps of the recorded common-stage internal Hom functor.
Source: proof steps 1 and 5 (blueprint: lem-sf-weil-dual-realization-comparison). -/
def coefficientHom (V : ForgetModel D l R X) (S : StructuralSystem D l X)
    (c : Compactification (geometric D X).base.hom)
    (permitted : ∀ K : W D l X,
      commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left
        (op (V.functor.obj K), coefficientOmega D l R X S c)) :
    (W D l X)ᵒᵖ ⥤ C D l X :=
  (commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left).lift
      (V.functor.op.prod' ((Functor.const _).obj (coefficientOmega D l R X S c)))
      (fun K ↦ permitted K.unop) ⋙
    commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left

variable (N : NativeClosedComparison D.k₀ l X.base.left)

/-- Canonical closed comparisons after changing closure and taking ordinary sections.
The Hom arrow is the transpose of the transported evaluation; it is not an
arbitrary isomorphism of the two Hom objects. Together with the recorded native
comparison this is the forgetful Hom comparison in the ordinary presentation.
Source: native closed comparison, transported along closureMap and sectionDerived
(blueprint: lem-sf-weil-dual-realization-comparison). -/
structure Presentation where
  tensor : N.ordinaryClosed.tensor ⋙ transport D l R X ≅
    (transport D l R X).prod (transport D l R X) ⋙
      (closed D l R X).tensor
  hom : N.homModels.ordinaryHom ⋙ transport D l R X ≅
    (transport D l R X).op.prod (transport D l R X) ⋙
      ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization
  hom_normalization : ∀ A B, (hom.app (op A, B)).hom =
    (closed D l R X).transpose _ _ _
      ((tensor.app (N.homModels.ordinaryHom.obj (op A, B), A)).inv ≫
        (transport D l R X).map (N.ordinaryClosed.evaluation A B))

/-- Forgetful tensor comparison, composed with the fixed presentation change.
Source: native closed comparison and its ordinary section presentation
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def Presentation.nativeTensor (T : Presentation D l R X N) :
    N.weilClosed.tensor ⋙ forget D l R X ≅
      (forget D l R X).prod (forget D l R X) ⋙
        (closed D l R X).tensor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight N.tensorComparison _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((nativeForget D.k₀ l X.base.left).prod
        (nativeForget D.k₀ l X.base.left)) T.tensor

/-- First arrow alpha: the actual native Hom comparison followed by presentation change.
The nativeModel isomorphism identifies the source with the upstream derivedHom.
Source: native comparison, proof step 3
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def Presentation.alpha (T : Presentation D l R X N) (K : W D l X) :
    (forget D l R X).obj
        ((ProEtaleWeilSheaf.derivedHom D.k₀ l X.base.left
          (nativeOmega D l X G).obj).obj (op K.obj)) ≅
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).obj
        (op ((U D l R X).obj K), (U D l R X).obj (nativeOmega D l X G)) :=
  (forget D l R X).mapIso
      ((N.homModels.nativeModel (nativeOmega D l X G).obj).app (op K.obj)).symm ≪≫
    (transport D l R X).mapIso
      (N.homComparison.app (op K.obj, (nativeOmega D l X G).obj)) ≪≫
    T.hom.app (op ((nativeForget D.k₀ l X.base.left).obj K.obj),
      (nativeForget D.k₀ l X.base.left).obj (nativeOmega D l X G).obj)

/-- H_X as an ambient native contravariant functor, retaining every derived arrow.
Source: blueprint, H_X K = native RHom(K,omega_X)
(blueprint: lem-sf-weil-dual-realization-comparison). -/
def nativeHom :=
  (ObjectProperty.ι (WeilComplex.objectProperty D.k₀ l X.base.left)).op ⋙
    ProEtaleWeilSheaf.derivedHom D.k₀ l X.base.left (nativeOmega D l X G).obj

/-- All conclusions with the fixed inverse realization model and exceptional counit,
for the given presentation change T. The comparison is pinned by the composite
through T.alpha, so it is not chosen together with its presentation.
Permitted Hom pairs assert precisely that the coefficient-passage internal Hom
exists constructibly; the target uses that actual Hom, never an unrelated duality.
Source: blueprint, dual realization comparison and proof steps 1--6
(blueprint: lem-sf-weil-dual-realization-comparison). -/
structure Comparison (P : Package D l R) (V : ForgetModel D l R X)
    (S : StructuralSystem D l X) (c : Compactification (geometric D X).base.hom)
    (T : Presentation D l R X N) where
  permitted : ∀ K : W D l X,
    commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left
      (op (V.functor.obj K), coefficientOmega D l R X S c)
  comparison : nativeHom D l X G ⋙ forget D l R X ≅
    coefficientHom D l R X V S c permitted ⋙ rho D l R X
  composite : ∀ K : W D l X,
    comparison.hom.app (op K) ≫
      beta D l R X
        ⟨(op (V.functor.obj K), coefficientOmega D l R X S c),
          permitted K⟩ =
    (T.alpha D l R X G N K).hom ≫
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
        (Prod.mkHom (V.realization.hom.app K).op
          (omegaComparison D l R X G adj P S c).hom)
  bounded : ∀ K : W D l X,
    boundedConstructible l (geometric D X).base.left (R.data (geometric D X)).realization
      ((forget D l R X).obj ((nativeHom D l X G).obj (op K)))
  evaluation : ∀ K : W D l X,
    (closed D l R X).tensor.map
        (Prod.mkHom (𝟙 _) (V.realization.hom.app K)) ≫
      (T.nativeTensor D l R X N).inv.app
        (N.homModels.weilHom.obj (op K.obj, (nativeOmega D l X G).obj), K.obj) ≫
      (forget D l R X).map (N.weilClosed.evaluation K.obj (nativeOmega D l X G).obj) ≫
      (omegaComparison D l R X G adj P S c).hom =
    (closed D l R X).tensor.map
        (Prod.mkHom
          ((forget D l R X).map
            ((N.homModels.nativeModel (nativeOmega D l X G).obj).app (op K.obj)).hom ≫
              comparison.hom.app (op K)) (𝟙 _)) ≫
      (tensorator D l R X).hom.app
        ((coefficientHom D l R X V S c permitted).obj (op K), V.functor.obj K) ≫
      (rho D l R X).map
        (coefficientEvaluation D l R X
          ⟨(op (V.functor.obj K), coefficientOmega D l R X S c),
            permitted K⟩)

private theorem eval_transpose
    {E : Type a} [Category.{b} E] {H : Eᵒᵖ × E ⥤ E}
    (Z : CoefficientClosedStructure H) (A B L : E)
    (f : Z.tensor.obj (L, A) ⟶ B) :
    Z.tensor.map (Prod.mkHom (Z.transpose L A B f) (𝟙 A)) ≫
      Z.evaluation A B = f := by
  let := Z.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id, Adjunction.homEquiv, Equiv.coe_fn_symm_mk,
    MonoidalCategory.tensorRight, Functor.flip, MonoidalCategory.curriedTensor,
    Functor.obj, Functor.map] using (Z.transpose L A B).symm_apply_apply f

private theorem eval_map
    {E : Type a} [Category.{b} E] {H : Eᵒᵖ × E ⥤ E}
    (Z : CoefficientClosedStructure H) {A A' B B' : E}
    (f : A' ⟶ A) (g : B ⟶ B') :
    Z.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 A')) ≫
        Z.evaluation A' B' =
      Z.tensor.map (Prod.mkHom (𝟙 _) f) ≫ Z.evaluation A B ≫ g := by
  let := Z.monoidal
  have h := Z.evaluation_naturality A A' B f
  have k := (Z.adjunction A').counit.naturality g
  simp only [MonoidalCategory.tensorRight, MonoidalCategory.tensorLeft, Functor.flip,
    MonoidalCategory.curriedTensor, Functor.comp_map, Functor.comp_obj,
    Prod.sectR_map, Functor.id_map] at h k
  have h' : Z.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 B))) (𝟙 A')) ≫
      Z.evaluation A' B = Z.tensor.map (Prod.mkHom (𝟙 _) f) ≫ Z.evaluation A B := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using h
  have k' : Z.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op A')) g)) (𝟙 A')) ≫
      Z.evaluation A' B' = Z.evaluation A' B ≫ g := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id] using k
  have e : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 B) ≫ Prod.mkHom (𝟙 (op A')) g := by simp
  rw [e, H.map_comp]
  rw [show Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 B)) ≫
      H.map (Prod.mkHom (𝟙 (op A')) g)) (𝟙 A') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 B))) (𝟙 A') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op A')) g)) (𝟙 A') by simp]
  rw [Functor.map_comp, Category.assoc, k', ← Category.assoc, h', Category.assoc]

private theorem eval_composite
    {E : Type a} [Category.{b} E] {H : Eᵒᵖ × E ⥤ E}
    (Z : CoefficientClosedStructure H) {A A' B B' V V' : E}
    (j : A' ⟶ A) (h : B ⟶ B')
    (v : V ⟶ H.obj (op A, B)) (c : V ⟶ V') (β : V' ⟶ H.obj (op A', B'))
    (e : Z.tensor.obj (V', A') ⟶ B')
    (hc : c ≫ β = v ≫ H.map (Prod.mkHom j.op h))
    (he : Z.tensor.map (Prod.mkHom β (𝟙 A')) ≫ Z.evaluation A' B' = e) :
    Z.tensor.map (Prod.mkHom (𝟙 V) j) ≫
        Z.tensor.map (Prod.mkHom v (𝟙 A)) ≫ Z.evaluation A B ≫ h =
      Z.tensor.map (Prod.mkHom c (𝟙 A')) ≫ e := by
  have hm : Prod.mkHom c (𝟙 A') ≫ Prod.mkHom β (𝟙 A') =
      Prod.mkHom (v ≫ H.map (Prod.mkHom j.op h)) (𝟙 A') := by
    ext
    · exact hc
    · simp
  have hm' : Prod.mkHom (v ≫ H.map (Prod.mkHom j.op h)) (𝟙 A') =
      Prod.mkHom v (𝟙 A') ≫
        Prod.mkHom (H.map (Prod.mkHom j.op h)) (𝟙 A') := by simp
  calc
    _ = Z.tensor.map (Prod.mkHom v (𝟙 A')) ≫
        Z.tensor.map (Prod.mkHom (𝟙 _) j) ≫ Z.evaluation A B ≫ h := by
      simp only [← Category.assoc, ← Z.tensor.map_comp]
      congr 2
      apply congrArg Z.tensor.map
      ext <;> simp
    _ = Z.tensor.map (Prod.mkHom v (𝟙 A')) ≫
        Z.tensor.map (Prod.mkHom (H.map (Prod.mkHom j.op h)) (𝟙 A')) ≫
          Z.evaluation A' B' := by rw [eval_map]
    _ = _ := by rw [← Category.assoc, ← Z.tensor.map_comp, ← hm', ← hm,
      Z.tensor.map_comp, Category.assoc, he]

private theorem alpha_naturality (T : Presentation D l R X N)
    {K L : (W D l X)ᵒᵖ} (f : K ⟶ L) :
    (forget D l R X).map ((nativeHom D l X G).map f) ≫
        (T.alpha D l R X G N L.unop).hom =
      (T.alpha D l R X G N K.unop).hom ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom ((U D l R X).map f.unop).op (𝟙 _)) := by
  let I := (ObjectProperty.ι (WeilComplex.objectProperty D.k₀ l X.base.left)).op
  let J := I ⋙ Prod.sectL _ (nativeOmega D l X G).obj
  let e₁ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft I (N.homModels.nativeModel (nativeOmega D l X G).obj).symm)
    (forget D l R X)
  let e₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft J N.homComparison) (transport D l R X)
  let e₃ := Functor.isoWhiskerLeft
    (J ⋙ (nativeForget D.k₀ l X.base.left).op.prod
      (nativeForget D.k₀ l X.base.left)) T.hom
  have hn := (e₁ ≪≫ e₂ ≪≫ e₃).hom.naturality f
  simpa only [I, J, e₁, e₂, e₃, Presentation.alpha, nativeHom, forget,
    Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.comp_obj, Functor.prod_map, Functor.prod_obj, Functor.op_map,
    Functor.op_obj, Prod.sectL, ObjectProperty.ι, U, WeilComplex.forget,
    nativeForget, transport, inducedFunctor, CategoryTheory.Functor.map_id,
    Quiver.Hom.unop_op,
    Quiver.Hom.op_unop, Category.assoc] using hn

private theorem tensor_transport_eval
    {C₀ : Type a} {C₁ : Type a₁} {C₂ : Type a₂}
    [Category.{b} C₀] [Category.{b₁} C₁] [Category.{b₂} C₂]
    (F : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂)
    (S₀ : C₀ × C₀ ⥤ C₀) (S₁ : C₁ × C₁ ⥤ C₁) (S₂ : C₂ × C₂ ⥤ C₂)
    (i : S₀ ⋙ F ≅ F.prod F ⋙ S₁) (t : S₁ ⋙ Q ≅ Q.prod Q ⋙ S₂)
    (A K L : C₀) (B : C₁) (V : C₂) (v : F.obj A ⟶ B)
    (e₀ : S₀.obj (A, K) ⟶ L) (e₁ : S₁.obj (B, F.obj K) ⟶ F.obj L)
    (h : Q.obj B ⟶ V) (e₂ : S₂.obj (V, Q.obj (F.obj K)) ⟶ Q.obj (F.obj L))
    (he : F.map e₀ = i.hom.app (A, K) ≫ S₁.map (Prod.mkHom v (𝟙 _)) ≫ e₁)
    (hn : S₂.map (Prod.mkHom h (𝟙 _)) ≫ e₂ = t.inv.app (B, F.obj K) ≫ Q.map e₁) :
    (t.inv.app (F.obj A, F.obj K) ≫ Q.map (i.inv.app (A, K))) ≫ Q.map (F.map e₀) =
      S₂.map (Prod.mkHom (Q.map v ≫ h) (𝟙 _)) ≫ e₂ := by
  have ht := t.inv.naturality (Prod.mkHom v (𝟙 (F.obj K)))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  simp only [Q.map_id] at ht
  rw [he]
  simp only [Q.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc, i.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  erw [Q.map_id]
  simp only [Category.id_comp]
  rw [← Category.assoc, ← ht, Category.assoc]
  have hm : Prod.mkHom (Q.map v ≫ h) (𝟙 (Q.obj (F.obj K))) =
      Prod.mkHom (Q.map v) (𝟙 _) ≫ Prod.mkHom h (𝟙 _) := by simp
  rw [hm, S₂.map_comp, Category.assoc, hn]

private theorem presentation_evaluation (T : Presentation D l R X N)
    (hN : N.Compatible) (K L : DerivedCategory (ProEtaleWeilSheaf D.k₀ l X.base.left)) :
    (T.nativeTensor D l R X N).inv.app (N.homModels.weilHom.obj (op K, L), K) ≫
        (forget D l R X).map (N.weilClosed.evaluation K L) =
      (closed D l R X).tensor.map
        (Prod.mkHom
          ((transport D l R X).map (N.homComparison.hom.app (op K, L)) ≫
            T.hom.hom.app
              (op ((nativeForget D.k₀ l X.base.left).obj K),
                (nativeForget D.k₀ l X.base.left).obj L)) (𝟙 _)) ≫
        (closed D l R X).evaluation
          ((forget D l R X).obj K) ((forget D l R X).obj L) := by
  let F := nativeForget D.k₀ l X.base.left
  let Q := transport D l R X
  let B := N.homModels.ordinaryHom.obj (op (F.obj K), F.obj L)
  have hn := eval_transpose (closed D l R X) (Q.obj (F.obj K)) (Q.obj (F.obj L)) _
    ((T.tensor.app (B, F.obj K)).inv ≫
      Q.map (N.ordinaryClosed.evaluation (F.obj K) (F.obj L)))
  rw [← T.hom_normalization] at hn
  have hh := tensor_transport_eval F Q N.weilClosed.tensor N.ordinaryClosed.tensor
    (closed D l R X).tensor N.tensorComparison T.tensor
    (N.homModels.weilHom.obj (op K, L)) K L B _
    (N.homComparison.hom.app (op K, L)) (N.weilClosed.evaluation K L)
    (N.ordinaryClosed.evaluation (F.obj K) (F.obj L))
    (T.hom.hom.app (op (F.obj K), F.obj L))
    ((closed D l R X).evaluation (Q.obj (F.obj K)) (Q.obj (F.obj L)))
    (hN.2.2.2.2.1 K L) hn
  simpa only [Presentation.nativeTensor, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.comp_id,
    Functor.prod_obj, Functor.comp_obj, Functor.comp_map, F, Q, forget] using hh

private theorem iso_composite_naturality
    {E : Type a} [Category.{b} E] {A A' B B' C C' : E}
    (f : A ⟶ A') (g : B ⟶ B') (k : C ⟶ C')
    (a : A ≅ C) (a' : A' ≅ C') (b : B ≅ C) (b' : B' ≅ C')
    (ha : f ≫ a'.hom = a.hom ≫ k) (hb : g ≫ b'.hom = b.hom ≫ k) :
    f ≫ (a' ≪≫ b'.symm).hom = (a ≪≫ b.symm).hom ≫ g := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq b').2
  rw [ha]
  simp only [Category.assoc]
  apply congrArg (a.hom ≫ ·)
  apply (Iso.eq_inv_comp b).2
  simpa only [Category.assoc] using hb.symm

private theorem cancel_comparison
    {E : Type a} [Category.{b} E] {A B C : E} (i : A ≅ C) (j : B ≅ C) :
    (i.hom ≫ j.inv) ≫ j.hom = i.hom := by
  rw [Category.assoc, j.inv_hom_id, Category.comp_id]

private theorem model_composite
    {C : Type a} {E : Type a₁} [Category.{b} C] [Category.{b₁} E]
    (F : C ⥤ E) {A B : C} {V P Q : E} (i : A ≅ B)
    (v : F.obj A ⟶ P) (w : P ⟶ Q) (c : F.obj B ⟶ V) (β : V ⟶ Q)
    (hc : c ≫ β = F.map i.inv ≫ v ≫ w) :
    (F.map i.hom ≫ c) ≫ β = v ≫ w := by
  rw [Category.assoc, hc, ← Category.assoc, ← F.map_comp, i.hom_inv_id]
  erw [F.map_id]
  exact Category.id_comp _

private theorem comparison_evaluation
    (P : Package D l R) (V : ForgetModel D l R X)
    (S : StructuralSystem D l X) (c : Compactification (geometric D X).base.hom)
    (T : Presentation D l R X N) (hN : N.Compatible)
    (permitted : ∀ K : W D l X,
      commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left
        (op (V.functor.obj K), coefficientOmega D l R X S c))
    (comparison : nativeHom D l X G ⋙ forget D l R X ≅
      coefficientHom D l R X V S c permitted ⋙ rho D l R X)
    (composite : ∀ K : W D l X,
      comparison.hom.app (op K) ≫
        beta D l R X ⟨(op (V.functor.obj K), coefficientOmega D l R X S c), permitted K⟩ =
      (T.alpha D l R X G N K).hom ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom (V.realization.hom.app K).op
            (omegaComparison D l R X G adj P S c).hom))
    (K : W D l X) :
    (closed D l R X).tensor.map
        (Prod.mkHom (𝟙 _) (V.realization.hom.app K)) ≫
      (T.nativeTensor D l R X N).inv.app
        (N.homModels.weilHom.obj (op K.obj, (nativeOmega D l X G).obj), K.obj) ≫
      (forget D l R X).map (N.weilClosed.evaluation K.obj (nativeOmega D l X G).obj) ≫
      (omegaComparison D l R X G adj P S c).hom =
    (closed D l R X).tensor.map
        (Prod.mkHom
          ((forget D l R X).map
            ((N.homModels.nativeModel (nativeOmega D l X G).obj).app (op K.obj)).hom ≫
              comparison.hom.app (op K)) (𝟙 _)) ≫
      (tensorator D l R X).hom.app
        ((coefficientHom D l R X V S c permitted).obj (op K), V.functor.obj K) ≫
      (rho D l R X).map
        (coefficientEvaluation D l R X
          ⟨(op (V.functor.obj K), coefficientOmega D l R X S c),
            permitted K⟩) := by
  let := (R.data (geometric D X)).units
  let Q : (commonStageHomPairs l (PadicAlgCl l)
      (geometric D X).base.left).FullSubcategory :=
    ⟨(op (V.functor.obj K), coefficientOmega D l R X S c), permitted K⟩
  let F := forget D l R X
  let Z := closed D l R X
  let W₀ := (nativeOmega D l X G).obj
  let n := F.map ((N.homModels.nativeModel W₀).app (op K.obj)).hom
  let v := (transport D l R X).map (N.homComparison.hom.app (op K.obj, W₀)) ≫
    T.hom.hom.app (op ((nativeForget D.k₀ l X.base.left).obj K.obj),
      (nativeForget D.k₀ l X.base.left).obj W₀)
  have hc : (n ≫ comparison.hom.app (op K)) ≫ beta D l R X Q =
      v ≫ (ambientHom l (geometric D X).base.left
        (R.data (geometric D X)).realization).map
          (Prod.mkHom (V.realization.hom.app K).op
            (omegaComparison D l R X G adj P S c).hom) := by
    apply model_composite F ((N.homModels.nativeModel W₀).app (op K.obj)) v _
      (comparison.hom.app (op K)) (beta D l R X Q)
    simpa only [Presentation.alpha, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, F, W₀, v, Q, nativeHom, Functor.comp_obj,
      Functor.op_obj, ObjectProperty.ι_obj, Iso.app_hom, Category.assoc] using composite K
  have he : Z.tensor.map (Prod.mkHom (beta D l R X Q) (𝟙 _)) ≫
      Z.evaluation ((rho D l R X).obj (V.functor.obj K))
        ((rho D l R X).obj (coefficientOmega D l R X S c)) =
    (tensorator D l R X).hom.app
      ((coefficientHom D l R X V S c permitted).obj (op K), V.functor.obj K) ≫
        (rho D l R X).map (coefficientEvaluation D l R X Q) :=
    (R.data (geometric D X)).hom.evaluation Q
  have hx := eval_composite Z
    (A := F.obj K.obj)
    (A' := (rho D l R X).obj (V.functor.obj K))
    (B := F.obj W₀)
    (B' := (rho D l R X).obj (coefficientOmega D l R X S c))
    (V := F.obj (N.homModels.weilHom.obj (op K.obj, W₀)))
    (V' := (rho D l R X).obj
      ((commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left).obj Q))
    (V.realization.hom.app K)
    (omegaComparison D l R X G adj P S c).hom v
    (n ≫ comparison.hom.app (op K)) (beta D l R X Q) _ hc he
  have hp := presentation_evaluation D l R X N T hN K.obj W₀
  have hp' := congrArg
    (fun z ↦ Z.tensor.map (Prod.mkHom (𝟙 _) (V.realization.hom.app K)) ≫ z ≫
      (omegaComparison D l R X G adj P S c).hom) hp
  apply Eq.trans _ hx
  simpa only [Category.assoc] using hp'

/-- Native dualizing Hom is realized common-stage duality, by the specified
three-arrow composite, naturally for all native derived morphisms and preserving
evaluation. The inverse model V is any fixed inverse of the fully faithful rho
on the bounded constructible image, with its counit; its unit is determined by
full faithfulness. No faithfulness of native forgetting is assumed. A presentation
change exists, and for every presentation change T the comparison is the composite
through T.alpha; in particular for the canonical one it is the node's c.
Source: current blueprint, cor-coef-verdier-weil-equivariance, internal Hom,
exceptional counits and evaluation; native DAG refinement
(blueprint: lem-sf-weil-dual-realization-comparison).

Proof:
1. By lem-sf-weil-native-closed-forgetful, UK is bounded constructible.
The equivalence lem-sf-adic-qbar-constructible-realization gives M_K and its
chosen counit j_K. By thm-coef-qbar-verdier, Hom(M,omega_Y) is constructible
for M_K; hence these are permitted coefficient-passage Hom pairs.
2. Apply lem-sf-weil-native-exceptional-forgetful to the structural morphism
and the specified native adjunction. Its point-unit and exceptional-counit
normalizations give omegaComparison, with the very h fixed in the statement.
3. Transport the canonical native tensor and Hom comparisons through the
closure isomorphism and the section-module equivalence. Tensor is the usual
K-flat tensor comparison, and Hom is the transpose of transported evaluation;
this gives a presentation change. For any presentation change T, compose with
N.homComparison to give alpha. The realization comparison beta
is exactly homComparison, the evaluation transpose of realized evaluation.
4. Put c = alpha followed by Hom(j,h), followed by inverse beta. The middle
arrow is invertible by bifunctoriality, and beta is invertible by the realization
theorem. Thus c is an isomorphism. Its target is a realized constructible object,
so its source has bounded constructible cohomology.
5. For an arbitrary native derived u, counit naturality gives rho(M_u) followed by j_L equal to
j_K followed by Uu. Naturality of alpha and beta gives the naturality of c. This applies to
all extension morphisms since it is an identity of derived functors, without
assuming U faithful.
6. Preservation of evaluation by alpha and beta, and evaluation naturality
in j and h, give exactly the displayed evaluation square, with the tensorator
of rho included. For alpha this is the evaluation clause of N.Compatible,
naturality of T.tensor, and hom_normalization of T, which says that T.hom
uncurries to T.tensor inverse followed by transported evaluation. Empty schemes
and zero complexes satisfy the same formulas. -/
theorem dual_realization_comparison (P : Package D l R) (V : ForgetModel D l R X)
    (S : StructuralSystem D l X) (c : Compactification (geometric D X).base.hom)
    (hN : N.Compatible) : Nonempty (Presentation D l R X N) ∧
      ∀ T : Presentation D l R X N, Nonempty (Comparison D l R X G adj N P V S c T) := by
  classical
  let := (R.data (geometric D X)).units
  obtain ⟨t, h, hn⟩ := NativeDualPresentation.ordinary_closed_presentation D l R X N hN
  refine ⟨⟨⟨t, h, hn⟩⟩, ?_⟩
  intro T
  let permitted := fun K : W D l X ↦
    NativeDualPresentation.structural_omega_hom_pairs D l R X S c (V.functor.obj K)
  let pair := fun K : (W D l X)ᵒᵖ ↦
    (⟨(op (V.functor.obj K.unop), coefficientOmega D l R X S c), permitted K.unop⟩ :
      (commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left).FullSubcategory)
  let a := fun K : (W D l X)ᵒᵖ ↦
    T.alpha D l R X G N K.unop ≪≫
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).mapIso
        (Iso.prod (V.realization.app K.unop).op (omegaComparison D l R X G adj P S c))
  have hbiso (K : (W D l X)ᵒᵖ) : IsIso (beta D l R X (pair K)) :=
    (R.data (geometric D X)).tensor.hom_isIso (pair K)
  let b := fun K : (W D l X)ᵒᵖ ↦
    @asIso _ _ _ _ (beta D l R X (pair K)) (hbiso K)
  let d := fun K ↦ a K ≪≫ (b K).symm
  have natural : ∀ {K L : (W D l X)ᵒᵖ} (f : K ⟶ L),
      (nativeHom D l X G ⋙ forget D l R X).map f ≫ (d L).hom =
        (d K).hom ≫ (coefficientHom D l R X V S c permitted ⋙ rho D l R X).map f := by
    intro K L f
    have hb := (R.data (geometric D X)).hom.naturality (pair K) (pair L)
      (ObjectProperty.homMk (Prod.mkHom (V.functor.map f.unop).op (𝟙 _)))
    let H := ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization
    let m := Prod.mkHom ((rho D l R X).map (V.functor.map f.unop)).op
      (𝟙 ((rho D l R X).obj (coefficientOmega D l R X S c)))
    have ha : (nativeHom D l X G ⋙ forget D l R X).map f ≫ (a L).hom =
        (a K).hom ≫ H.map m := by
      dsimp only [a, Iso.trans_hom, Functor.mapIso_hom]
      dsimp only [Functor.comp_map]
      rw [← Category.assoc, alpha_naturality D l R X G N T f]
      simp only [Category.assoc, ← Functor.map_comp]
      congr 1
      change H.map _ = H.map _ ≫ H.map _
      rw [← H.map_comp]
      apply congrArg H.map
      ext
      · apply Quiver.Hom.unop_inj
        simpa [m, Functor.comp_map] using
          (V.realization.hom.naturality f.unop).symm
      · simp [m]
    have hb' : (coefficientHom D l R X V S c permitted ⋙ rho D l R X).map f ≫
        (b L).hom = (b K).hom ≫ H.map m := by
      change (coefficientHom D l R X V S c permitted ⋙ rho D l R X).map f ≫
        (b L).hom = (b K).hom ≫
          H.map (Prod.mkHom ((rho D l R X).map (V.functor.map f.unop)).op
            ((rho D l R X).map (𝟙 (coefficientOmega D l R X S c)))) at hb
      rw [(rho D l R X).map_id] at hb
      exact hb
    exact iso_composite_naturality _ _ _ (a K) (a L) (b K) (b L) ha hb'
  let comparison : nativeHom D l X G ⋙ forget D l R X ≅
      coefficientHom D l R X V S c permitted ⋙ rho D l R X :=
    NatIso.ofComponents d (fun f ↦ natural f)
  have composite (K : W D l X) : comparison.hom.app (op K) ≫ beta D l R X (pair (op K)) =
      (a (op K)).hom := by
    change ((a (op K)).hom ≫ (b (op K)).inv) ≫ (b (op K)).hom = _
    exact cancel_comparison (a (op K)) (b (op K))
  refine ⟨{ permitted := permitted
            comparison := comparison
            composite := ?_
            bounded := ?_
            evaluation := ?_ }⟩
  · intro K
    exact composite K
  · intro K
    apply ((R.data (geometric D X)).image _).mpr
    exact ⟨(coefficientHom D l R X V S c permitted).obj (op K),
      ⟨(comparison.app (op K)).symm⟩⟩
  · exact comparison_evaluation D l R X G adj N P V S c T hN permitted comparison
      (fun K ↦ composite K)

end WeilConjectures.NativeDualRealization
