/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeDualRealization.NativeDualRealizationComparisonData

/-! # Realization of the native Weil evaluation transpose

Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation and
transposition paragraph, with the six-step native-derived refinement
(blueprint: lem-sf-weil-bidual-evaluation-realization).
The conclusion compares actual arrows, keeps the signed tensor symmetry,
and makes no invertibility assertion for the native double-dual arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open WeilConjectures WeilConjectures.AdicQbarRealization
open WeilConjectures.NativeExceptionalForgetful
open WeilConjectures.NativeDualRealization
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeBidualRealization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D) (A : Datum D l R X)

/-- The sole additional hypothesis: native Hom into omega_X preserves WeilComplex.
No hypothesis about invertibility of the evaluation transpose is included.
Source: current blueprint, cor-coef-verdier-weil-equivariance, native restriction
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def Closed : Prop := ∀ K : W D l X,
  WeilComplex.objectProperty D.k₀ l X.base.left ((nativeHom D l R X A).obj (op K.obj))

/-- D_X is the full-subcategory restriction of the specified ambient native Hom.
Source: current blueprint, cor-coef-verdier-weil-equivariance, D_X
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def dualX (h : Closed D l R X A) : (W D l X)ᵒᵖ ⥤ W D l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (WeilComplex.objectProperty D.k₀ l X.base.left)).op ⋙
      nativeHom D l R X A) (fun K ↦ h K.unop)

/-- Full faithfulness of the given realization, with the inverse on Hom sets
obtained from its recorded bijection. No new equivalence is chosen.
Source: BS 6.8.14; current blueprint, inverse-realization identifications
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def realizationFullyFaithful : (rho D l R X).FullyFaithful where
  preimage {M N} := (Equiv.ofBijective _ ((R.data (geometric D X)).fully_faithful M N)).symm
  map_preimage {M N} f :=
    (Equiv.ofBijective _ ((R.data (geometric D X)).fully_faithful M N)).apply_symm_apply f
  preimage_map {M N} f :=
    (Equiv.ofBijective _ ((R.data (geometric D X)).fully_faithful M N)).symm_apply_apply f

variable (hp : Permitted D l R X A)

/-- t_K : M_(D_X K) ≅ D_Y M_K is the unique lift of j_(D_X K) followed by c_K.
Full faithfulness makes this exactly the fixed inverse-equivalence unit transport.
Source: current blueprint, cor-coef-verdier-weil-equivariance, inverse first-dual map
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def firstDualIso (h : Closed D l R X A) (K : W D l X) :
    (model D l R X A).obj ((dualX D l R X A h).obj (op K)) ≅
      (commonDual D l R X A hp).obj (op ((model D l R X A).obj K)) :=
  (realizationFullyFaithful D l R X).preimageIso
    (counit D l R X A ((dualX D l R X A h).obj (op K)) ≪≫ comparison D l R X A hp K)

/-- b_K is c_(D_X K) followed by rho D_Y(t_K inverse), in the prescribed order.
Source: current blueprint, cor-coef-verdier-weil-equivariance, double-dual comparison
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def secondComparison (h : Closed D l R X A) (K : W D l X) :
    (U D l R X).obj
        ((dualX D l R X A h).obj (op ((dualX D l R X A h).obj (op K)))) ≅
      (rho D l R X).obj
        ((commonDual D l R X A hp).obj
          (op ((commonDual D l R X A hp).obj (op ((model D l R X A).obj K))))) :=
  comparison D l R X A hp ((dualX D l R X A h).obj (op K)) ≪≫
    (rho D l R X).mapIso
      ((commonDual D l R X A hp).mapIso (firstDualIso D l R X A hp h K).symm.op)

/-- The common-stage double-dual arrow is the transpose of evaluation after the
signed symmetry, using the recorded common-stage tensor-Hom adjunction.
Source: current blueprint, cor-coef-verdier-weil-equivariance, delta^Y
(blueprint: lem-sf-weil-bidual-evaluation-realization). -/
def commonBidual (M : C D l X) :=
  letI := (R.data (geometric D X)).units
  (podCommonClosed l (PadicAlgCl l) (geometric D X).base.left).transpose M
    (pair D l R X A hp ((commonDual D l R X A hp).obj (op M)))
    ((pullbackTensorCommonBraiding l (PadicAlgCl l) (geometric D X).base.left M
        ((commonDual D l R X A hp).obj (op M))).hom ≫
      (podCommonClosed l (PadicAlgCl l) (geometric D X).base.left).evaluation
        (pair D l R X A hp M))

set_option Elab.async false

attribute [local irreducible] HasDerivedCategory.standard
  derivedInternalHomOfUniverses AlgebraicGeometry.Scheme.residueField

private theorem permitted : Permitted D l R X A := by
  obtain ⟨B, _⟩ := coef_qbar_verdier D l (Fact.out : l ≠ D.p) (PadicAlgCl l) (geometric D
    X).base.left
  intro M
  exact (B.finite.hom _).permitted _ _

private def delta (h : Closed D l R X A) :
    𝟭 (W D l X) ⟶ (dualX D l R X A h).rightOp ⋙ dualX D l R X A h
    where
  app K :=
    ObjectProperty.homMk
      (nativeBidual A.closed.native.weilClosed A.closed.native.weilSymmetry (nativeOmega D l R X
        A).obj K.obj)
  naturality K L f := by
    apply ObjectProperty.hom_ext
    exact A.closed.compatible.2.2.2.2.2.1 _ _ _ f.hom

private theorem untranspose {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T P Q : B) (f : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm f = S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q f

private theorem native_transpose {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (sym : @SymmetricCategory B _ S.monoidal) (W K : B) :
    S.tensor.map (Prod.mkHom (nativeBidual S sym W K) (𝟙 _)) ≫ S.evaluation (H.obj (op K, W)) W =
      (sym.braiding K (H.obj (op K, W))).hom ≫ S.evaluation K W :=
  by rw [← untranspose, nativeBidual, Equiv.symm_apply_apply]

private theorem tensor_comp {B : Type*} [Category B] (T : B × B ⥤ B) {X Y Z X' Y' Z' : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
    T.map (Prod.mkHom (f ≫ g) (f' ≫ g')) = T.map (Prod.mkHom f f') ≫ T.map (Prod.mkHom g g') :=
  T.map_comp (Prod.mkHom f f') (Prod.mkHom g g')

private theorem evaluation_natural {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (P Q P' Q' : B) (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫ S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫ S.evaluation P' Q =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q :=
    by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫ S.evaluation P' Q' =
      S.evaluation P' Q ≫ g :=
    by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) = H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op
    P')) g) :=
    by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht := tensor_comp S.tensor (H.map (Prod.mkHom f.op (𝟙 Q))) (H.map (Prod.mkHom (𝟙 (op P'))
    g)) (𝟙 P') (𝟙 P')
  simp only [Category.id_comp] at ht
  rw [ht, Category.assoc, hg, ← Category.assoc, he, Category.assoc]

private theorem section_evaluation {B E : Type*} [Category B] [Category E]
    {H : Bᵒᵖ × B ⥤ B} {J : Eᵒᵖ × E ⥤ E} (S : CoefficientClosedStructure H) (T :
      CoefficientClosedStructure J)
    (V : B ⥤ E) (t : S.tensor ⋙ V ≅ V.prod V ⋙ T.tensor) (P Q : B) :
    T.tensor.map (Prod.mkHom (NativeSectionClosed.sectionHomComparison S T V t P Q) (𝟙 (V.obj P))) ≫
        T.evaluation (V.obj P) (V.obj Q) =
      (t.app (H.obj (op P, Q), P)).inv ≫ V.map (S.evaluation P Q) :=
  by rw [← untranspose, NativeSectionClosed.sectionHomComparison, Equiv.symm_apply_apply]

private theorem section_natural {B E : Type*} [Category B] [Category E] {H : Bᵒᵖ × B ⥤ B}
    {J : Eᵒᵖ × E ⥤ E} (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure J) (V : B
      ⥤ E)
    (t : S.tensor ⋙ V ≅ V.prod V ⋙ T.tensor) (P Q P' Q' : B) (f : P' ⟶ P) (g : Q ⟶ Q') :
    V.map (H.map (Prod.mkHom f.op g)) ≫ NativeSectionClosed.sectionHomComparison S T V t P' Q' =
      NativeSectionClosed.sectionHomComparison S T V t P Q ≫ J.map (Prod.mkHom (V.map f).op (V.map
        g)) := by
  apply (T.transpose _ (V.obj P') (V.obj Q')).symm.injective
  rw [untranspose, untranspose]
  have tc {U V Z R : E} (a : U ⟶ V) (b : V ⟶ Z) :
    T.tensor.map (Prod.mkHom (a ≫ b) (𝟙 R)) =
      T.tensor.map (Prod.mkHom a (𝟙 R)) ≫ T.tensor.map (Prod.mkHom b (𝟙 R)) :=
    by simpa only [Category.id_comp] using tensor_comp T.tensor a b (𝟙 R) (𝟙 R)
  simp only [tc, Category.assoc]
  rw [evaluation_natural T, section_evaluation]
  have hn := t.inv.naturality (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P'))
  have hn' := t.inv.naturality (Prod.mkHom (𝟙 (H.obj (op P, Q))) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  erw [V.map_id] at hn
  erw [V.map_id] at hn'
  change _ ≫ t.inv.app (H.obj (op P', Q'), P') ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc, ← V.map_comp, evaluation_natural S]
  rw [V.map_comp, V.map_comp]
  have ht :
    T.tensor.map (Prod.mkHom (NativeSectionClosed.sectionHomComparison S T V t P Q) (𝟙 (V.obj
      P'))) ≫
        T.tensor.map (Prod.mkHom (𝟙 _) (V.map f)) =
      T.tensor.map (Prod.mkHom (𝟙 _) (V.map f)) ≫
        T.tensor.map (Prod.mkHom (NativeSectionClosed.sectionHomComparison S T V t P Q) (𝟙 (V.obj
          P))) :=
    by
    rw [← T.tensor.map_comp, ← T.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% ht, reassoc_of% section_evaluation S T V t P Q, ← reassoc_of% hn']
  rfl

private theorem iso_cancel {B : Type*} [Category B] {X Y Z : B} (e : Y ≅ Z) {f g : X ⟶ Y}
    (h : f ≫ e.hom = g ≫ e.hom) : f = g := by
  have ht := congrArg (fun q ↦ q ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht

private theorem composition_square {B : Type*} [Category B]
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ T₀ T₁ : B}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (k : Z₀ ⟶ Z₁) (r : T₀ ⟶ T₁)
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (b₀ : Y₀ ⟶ Z₀) (b₁ : Y₁ ⟶ Z₁)
    (c₀ : X₀ ⟶ T₀) (c₁ : X₁ ⟶ T₁) (e₀ : T₀ ≅ Z₀) (e₁ : T₁ ≅ Z₁)
    (ha : f ≫ a₁ = a₀ ≫ g) (hb : g ≫ b₁ = b₀ ≫ k)
    (hc₀ : c₀ ≫ e₀.hom = a₀ ≫ b₀) (hc₁ : c₁ ≫ e₁.hom = a₁ ≫ b₁)
    (he : r ≫ e₁.hom = e₀.hom ≫ k) : f ≫ c₁ = c₀ ≫ r := by
  apply iso_cancel e₁
  simp only [Category.assoc]
  rw [hc₁, ← Category.assoc, ha, Category.assoc, hb, ← Category.assoc, ← hc₀,
    Category.assoc, ← he]

private theorem hom_square {B : Type*} [Category B] (H : Bᵒᵖ × B ⥤ B)
    {M N K L W O : B} (f : K ⟶ L) (m : M ⟶ N) (jK : M ⟶ K) (jL : N ⟶ L)
    (h : W ⟶ O) (hj : m ≫ jL = jK ≫ f) :
    H.map (Prod.mkHom f.op (𝟙 W)) ≫ H.map (Prod.mkHom jK.op h) =
      H.map (Prod.mkHom jL.op h) ≫ H.map (Prod.mkHom m.op (𝟙 O)) := by
  rw [← H.map_comp, ← H.map_comp]
  congr 1
  apply Prod.hom_ext
  · apply Quiver.Hom.unop_inj
    exact hj.symm
  · simp

private theorem evaluation_composite {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) {F K M W O DN : B}
    (j : M ⟶ K) (h : W ⟶ O) (alpha : F ⟶ H.obj (op K, W))
    (c : F ⟶ DN) (beta : DN ⟶ H.obj (op M, O))
    (e : S.tensor.obj (F, K) ⟶ W) (E : S.tensor.obj (DN, M) ⟶ O)
    (hc : c ≫ beta = alpha ≫ H.map (Prod.mkHom j.op h))
    (ha : S.tensor.map (Prod.mkHom alpha (𝟙 K)) ≫ S.evaluation K W = e)
    (hb : S.tensor.map (Prod.mkHom beta (𝟙 M)) ≫ S.evaluation M O = E) :
    S.tensor.map (Prod.mkHom c (𝟙 M)) ≫ E =
      S.tensor.map (Prod.mkHom (𝟙 F) j) ≫ e ≫ h := by
  have tc {U V Z P : B} (a : U ⟶ V) (b : V ⟶ Z) :
      S.tensor.map (Prod.mkHom (a ≫ b) (𝟙 P)) =
        S.tensor.map (Prod.mkHom a (𝟙 P)) ≫ S.tensor.map (Prod.mkHom b (𝟙 P)) := by
    simpa only [Category.id_comp] using tensor_comp S.tensor a b (𝟙 P) (𝟙 P)
  have ht : S.tensor.map (Prod.mkHom alpha (𝟙 M)) ≫
        S.tensor.map (Prod.mkHom (𝟙 _) j) =
      S.tensor.map (Prod.mkHom (𝟙 F) j) ≫
        S.tensor.map (Prod.mkHom alpha (𝟙 K)) := by
    rw [← S.tensor.map_comp, ← S.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [← hb, ← Category.assoc, ← tc, hc, tc, Category.assoc,
    evaluation_natural, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [reassoc_of% ha]

private theorem mapped_transpose {B E : Type*} [Category B] [Category E]
    {H : Bᵒᵖ × B ⥤ B} {J : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure J)
    (b : @SymmetricCategory B _ S.monoidal) (e : @SymmetricCategory E _ T.monoidal)
    (V : B ⥤ E) (t : S.tensor ⋙ V ≅ V.prod V ⋙ T.tensor)
    (hs : NativeSectionClosed.SectionSymmetryCompatibility S T b e V t) (W K : B) :
    T.tensor.map (Prod.mkHom (V.map (nativeBidual S b W K)) (𝟙 _)) ≫
        (t.app (H.obj (op (H.obj (op K, W)), W), H.obj (op K, W))).inv ≫
          V.map (S.evaluation (H.obj (op K, W)) W) =
      (e.braiding (V.obj K) (V.obj (H.obj (op K, W)))).hom ≫
        (t.app (H.obj (op K, W), K)).inv ≫ V.map (S.evaluation K W) := by
  have hn := t.inv.naturality (Prod.mkHom (nativeBidual S b W K)
    (𝟙 (H.obj (op K, W))))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [V.map_id] at hn
  change T.tensor.map (Prod.mkHom (V.map (nativeBidual S b W K))
      (𝟙 (V.obj (H.obj (op K, W))))) ≫
    t.inv.app (H.obj (op (H.obj (op K, W)), W), H.obj (op K, W)) ≫
      V.map (S.evaluation (H.obj (op K, W)) W) = _
  rw [← Category.assoc, hn, Category.assoc, ← V.map_comp, native_transpose,
    V.map_comp, ← Category.assoc]
  have hh := congrArg (fun q ↦ (t.app (K, H.obj (op K, W))).inv ≫ q ≫
    (t.app (H.obj (op K, W), K)).inv) (hs K (H.obj (op K, W)))
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] at hh
  erw [hh]
  exact Category.assoc _ _ _

private theorem identify_transpose {B : Type*} [Category B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) {F P O T : B} (beta : F ≅ H.obj (op P, O))
    (E : S.tensor.obj (F, P) ⟶ O)
    (he : S.tensor.map (Prod.mkHom beta.hom (𝟙 P)) ≫ S.evaluation P O = E)
    (z a : T ⟶ F) (b : S.tensor.obj (T, P) ⟶ O)
    (ha : S.transpose T P O b = a ≫ beta.hom)
    (hz : S.tensor.map (Prod.mkHom z (𝟙 P)) ≫ E = b) : z = a := by
  apply iso_cancel beta
  rw [← ha]
  apply (S.transpose T P O).symm.injective
  rw [Equiv.symm_apply_apply, untranspose]
  have tc := tensor_comp S.tensor z beta.hom (𝟙 P) (𝟙 P)
  simp only [Category.id_comp] at tc
  rw [tc, Category.assoc, he, hz]

private theorem comparison_beta (hp : Permitted D l R X A) (K : W D l X) :
    (comparison D l R X A hp K).hom ≫ realizationHom D l R X A hp ((model D l R X A).obj K) =
      NativeSectionClosed.sectionHomComparison A.closed.native.weilClosed
          (NativeSectionClosed.ordinaryClosed D l R X) (NativeSectionClosed.ambientForget D l R X)
            A.closed.tensor
          K.obj (nativeOmega D l R X A).obj ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom (counit D l R X A K).hom.op (dualizingComparison D l R X A).hom) := by
  change (_ ≫ _ ≫ (realizationHomIso D l R X A hp _).inv) ≫ (realizationHomIso D l R X A hp _).hom
    = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem comparison_natural (hp : Permitted D l R X A) {K L : W D l X} (f : K ⟶ L) :
    (NativeSectionClosed.ambientForget D l R X).map ((nativeHom D l R X A).map f.hom.op) ≫
        (comparison D l R X A hp K).hom =
      (comparison D l R X A hp L).hom ≫
        (rho D l R X).map ((commonDual D l R X A hp).map ((model D l R X A).map f).op) := by
  let := (R.data (geometric D X)).units
  apply composition_square
    (NativeSectionClosed.ambientForget D l R X |>.map
      ((nativeHom D l R X A).map f.hom.op))
    ((ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
      (Prod.mkHom ((U D l R X).map f).op (𝟙 _)))
    ((ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
      (Prod.mkHom ((rho D l R X).map ((model D l R X A).map f)).op (𝟙 _)))
    ((rho D l R X).map
      ((commonDual D l R X A hp).map ((model D l R X A).map f).op))
    (NativeSectionClosed.sectionHomComparison A.closed.native.weilClosed
      (NativeSectionClosed.ordinaryClosed D l R X)
      (NativeSectionClosed.ambientForget D l R X) A.closed.tensor L.obj
      (nativeOmega D l R X A).obj)
    (NativeSectionClosed.sectionHomComparison A.closed.native.weilClosed
      (NativeSectionClosed.ordinaryClosed D l R X)
      (NativeSectionClosed.ambientForget D l R X) A.closed.tensor K.obj
      (nativeOmega D l R X A).obj)
    ((ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
      (Prod.mkHom (counit D l R X A L).hom.op (dualizingComparison D l R X A).hom))
    ((ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
      (Prod.mkHom (counit D l R X A K).hom.op (dualizingComparison D l R X A).hom))
    (comparison D l R X A hp L).hom (comparison D l R X A hp K).hom
    (realizationHomIso D l R X A hp ((model D l R X A).obj L))
    (realizationHomIso D l R X A hp ((model D l R X A).obj K))
  · have hn := section_natural A.closed.native.weilClosed
        (NativeSectionClosed.ordinaryClosed D l R X)
        (NativeSectionClosed.ambientForget D l R X) A.closed.tensor
        L.obj (nativeOmega D l R X A).obj K.obj (nativeOmega D l R X A).obj f.hom (𝟙 _)
    erw [(NativeSectionClosed.ambientForget D l R X).map_id] at hn
    exact hn
  · exact hom_square _ _ _ _ _ (dualizingComparison D l R X A).hom
      ((A.exceptional.model X).realization.hom.naturality f)
  · exact comparison_beta D l R X A hp L
  · exact comparison_beta D l R X A hp K
  · have hn := (R.data (geometric D X)).hom.naturality
      (pair D l R X A hp ((model D l R X A).obj L))
      (pair D l R X A hp ((model D l R X A).obj K))
      (ObjectProperty.homMk (Prod.mkHom ((model D l R X A).map f).op (𝟙 _)))
    change _ ≫ realizationHom D l R X A hp _ =
      realizationHom D l R X A hp _ ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom ((rho D l R X).map ((model D l R X A).map f)).op
            ((rho D l R X).map (𝟙 _))) at hn
    erw [(rho D l R X).map_id] at hn
    exact hn

private theorem comparison_evaluation (hp : Permitted D l R X A) (K : W D l X) :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map (Prod.mkHom (comparison D l R X A hp
      K).hom (𝟙 _)) ≫
        realizedEvaluation D l R X A hp ((model D l R X A).obj K) =
      (NativeSectionClosed.ordinaryClosed D l R X).tensor.map (Prod.mkHom (𝟙 _) (counit D l R X A
        K).hom) ≫
        forgottenEvaluation D l R X A K ≫ (dualizingComparison D l R X A).hom := by
  let := (R.data (geometric D X)).units
  exact evaluation_composite (NativeSectionClosed.ordinaryClosed D l R X)
    (counit D l R X A K).hom (dualizingComparison D l R X A).hom
    (NativeSectionClosed.sectionHomComparison A.closed.native.weilClosed
      (NativeSectionClosed.ordinaryClosed D l R X)
      (NativeSectionClosed.ambientForget D l R X) A.closed.tensor K.obj
      (nativeOmega D l R X A).obj)
    (comparison D l R X A hp K).hom
    (realizationHom D l R X A hp ((model D l R X A).obj K))
    (forgottenEvaluation D l R X A K)
    (realizedEvaluation D l R X A hp ((model D l R X A).obj K))
    (comparison_beta D l R X A hp K)
    (section_evaluation A.closed.native.weilClosed _ _ _ _ _)
    ((R.data (geometric D X)).hom.evaluation
      (pair D l R X A hp ((model D l R X A).obj K)))

private theorem realized_evaluation_natural (hp : Permitted D l R X A) {M N : C D l X}
    (f : M ⟶ N) :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom ((rho D l R X).map ((commonDual D l R X A hp).map f.op)) (𝟙 _)) ≫
        realizedEvaluation D l R X A hp M =
      (NativeSectionClosed.ordinaryClosed D l R X).tensor.map (Prod.mkHom (𝟙 _) ((rho D l R X).map
        f)) ≫
        realizedEvaluation D l R X A hp N := by
  let := (R.data (geometric D X)).units
  have hn := (R.data (geometric D X)).hom.naturality
    (pair D l R X A hp N) (pair D l R X A hp M)
    (ObjectProperty.homMk (Prod.mkHom f.op (𝟙 _)))
  have hn' : (rho D l R X).map ((commonDual D l R X A hp).map f.op) ≫
      realizationHom D l R X A hp M =
    realizationHom D l R X A hp N ≫
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
        (Prod.mkHom ((rho D l R X).map f).op (𝟙 _)) := by
    change _ ≫ realizationHom D l R X A hp M =
      realizationHom D l R X A hp N ≫
        (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).map
          (Prod.mkHom ((rho D l R X).map f).op ((rho D l R X).map (𝟙 _))) at hn
    erw [(rho D l R X).map_id] at hn
    exact hn
  simpa only [Category.comp_id] using
    evaluation_composite (NativeSectionClosed.ordinaryClosed D l R X)
      ((rho D l R X).map f) (𝟙 _)
      (realizationHom D l R X A hp N)
      ((rho D l R X).map ((commonDual D l R X A hp).map f.op))
      (realizationHom D l R X A hp M)
      (realizedEvaluation D l R X A hp N) (realizedEvaluation D l R X A hp M) hn'
      ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp N))
      ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp M))

private theorem pairing_diagram {B : Type*} [Category B] (T : B × B ⥤ B)
    {M X Y DM N Z DN DDM O : B} (j : M ≅ X) (c : Y ≅ DM) (j' : N ≅ Y) (c' : Z ≅ DN) (t : DM ⟶ N)
      (d : DN ⟶ DDM)
    (v : X ⟶ Z) (eX : T.obj (Y, X) ⟶ O) (eY : T.obj (Z, Y) ⟶ O) (eM : T.obj (DM, M) ⟶ O) (eN :
      T.obj (DN, N) ⟶ O)
    (eDM : T.obj (DDM, DM) ⟶ O) (s : T.obj (X, Y) ⟶ T.obj (Y, X)) (s' : T.obj (M, DM) ⟶ T.obj (DM,
      M))
    (ht : t ≫ j'.hom = c.inv) (hd : T.map (Prod.mkHom d (𝟙 DM)) ≫ eDM = T.map (Prod.mkHom (𝟙 DN)
      t) ≫ eN)
    (hX : T.map (Prod.mkHom c.hom (𝟙 M)) ≫ eM = T.map (Prod.mkHom (𝟙 Y) j.hom) ≫ eX)
    (hY : T.map (Prod.mkHom c'.hom (𝟙 N)) ≫ eN = T.map (Prod.mkHom (𝟙 Z) j'.hom) ≫ eY)
    (hv : T.map (Prod.mkHom v (𝟙 Y)) ≫ eY = s ≫ eX)
    (hs : T.map (Prod.mkHom j.hom c.inv) ≫ s = s' ≫ T.map (Prod.mkHom c.inv j.hom)) :
    T.map (Prod.mkHom (j.hom ≫ v ≫ c'.hom ≫ d) (𝟙 DM)) ≫ eDM = s' ≫ eM := by
  have norm {P Q P' Q' P'' Q'' : B} (a : P ⟶ Q) (b : Q ⟶ P') (a' : Q' ⟶ P'') (b' : P'' ⟶ Q'') :
    T.map (Prod.mkHom a a') ≫ T.map (Prod.mkHom b b') = T.map (Prod.mkHom (a ≫ b) (a' ≫ b')) :=
    (tensor_comp T a b a' b').symm
  calc
    _ = T.map (Prod.mkHom (j.hom ≫ v ≫ c'.hom) (𝟙 DM)) ≫ (T.map (Prod.mkHom d (𝟙 DM)) ≫ eDM) :=
      by
      simp only [← Category.assoc, norm]
      simp only [Category.id_comp, Category.assoc]
    _ = T.map (Prod.mkHom (j.hom ≫ v ≫ c'.hom) t) ≫ eN :=
      by
      rw [hd, ← Category.assoc, norm]
      simp only [Category.id_comp, Category.comp_id]
    _ = T.map (Prod.mkHom (j.hom ≫ v) t) ≫ (T.map (Prod.mkHom c'.hom (𝟙 N)) ≫ eN) :=
      by
      simp only [← Category.assoc, norm]
      simp only [Category.comp_id, Category.assoc]
    _ = T.map (Prod.mkHom (j.hom ≫ v) c.inv) ≫ eY :=
      by
      rw [hY, ← Category.assoc, norm]
      simp only [Category.comp_id, ht]
    _ = T.map (Prod.mkHom j.hom c.inv) ≫ (T.map (Prod.mkHom v (𝟙 Y)) ≫ eY) :=
      by
      simp only [← Category.assoc, norm]
      simp only [Category.comp_id]
    _ = s' ≫ (T.map (Prod.mkHom c.inv j.hom) ≫ eX) := by rw [hv, ← Category.assoc, hs,
      Category.assoc]
    _ = s' ≫ eM := by
      congr 1
      have hx := congrArg (fun q ↦ T.map (Prod.mkHom c.inv (𝟙 M)) ≫ q) hX
      simp only [← Category.assoc, norm, Iso.inv_hom_id, Category.comp_id, Category.id_comp,
        ← CategoryTheory.prod_id] at hx
      simpa only [T.map_id, Category.id_comp] using hx.symm

private theorem firstDual_natural (hp : Permitted D l R X A) (h : Closed D l R X A)
    {K L : W D l X} (f : K ⟶ L) :
    (model D l R X A).map ((dualX D l R X A h).map f.op) ≫ (firstDualIso D l R X A hp h K).hom =
      (firstDualIso D l R X A hp h L).hom ≫ (commonDual D l R X A hp).map ((model D l R X A).map
        f).op := by
  apply (realizationFullyFaithful D l R X).map_injective
  simp only [Functor.map_comp]
  have ht (P : W D l X) :
    (rho D l R X).map (firstDualIso D l R X A hp h P).hom =
      (counit D l R X A ((dualX D l R X A h).obj (op P))).hom ≫ (comparison D l R X A hp P).hom :=
    (realizationFullyFaithful D l R X).map_preimage _
  rw [ht K, ht L]
  have hj := (A.exceptional.model X).realization.hom.naturality ((dualX D l R X A h).map f.op)
  change
    (rho D l R X).map ((model D l R X A).map _) ≫ (counit D l R X A ((dualX D l R X A h).obj (op
      K))).hom =
      (counit D l R X A ((dualX D l R X A h).obj (op L))).hom ≫ _ at hj
  erw [← Category.assoc, hj, Category.assoc]
  have hn := comparison_natural D l R X A hp f
  change (U D l R X).map ((dualX D l R X A h).map f.op) ≫ _ = _ at hn
  simpa only [Category.assoc] using
    congrArg (fun q ↦ (counit D l R X A ((dualX D l R X A h).obj (op L))).hom ≫ q) hn

private theorem second_natural (hp : Permitted D l R X A) (h : Closed D l R X A)
    {K L : W D l X} (f : K ⟶ L) :
    (U D l R X).map (((dualX D l R X A h).rightOp ⋙ dualX D l R X A h).map f) ≫
        (secondComparison D l R X A hp h L).hom =
      (secondComparison D l R X A hp h K).hom ≫
        (rho D l R X).map
          (((commonDual D l R X A hp).rightOp ⋙ commonDual D l R X A hp).map ((model D l R X
            A).map f)) := by
  have hi :
    (firstDualIso D l R X A hp h L).inv ≫ (model D l R X A).map ((dualX D l R X A h).map f.op) =
      (commonDual D l R X A hp).map ((model D l R X A).map f).op ≫ (firstDualIso D l R X A hp h
        K).inv :=
    by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← firstDual_natural D l R X A hp h f, Category.assoc,
      Iso.hom_inv_id,
      Category.comp_id]
  have hh := congrArg (fun q ↦ (rho D l R X).map ((commonDual D l R X A hp).map q.op)) hi
  simp only [op_comp, Functor.map_comp] at hh
  dsimp only [secondComparison, Iso.trans_hom, Functor.mapIso_hom]
  have hn := comparison_natural D l R X A hp ((dualX D l R X A h).map f.op)
  change (U D l R X).map (((dualX D l R X A h).rightOp ⋙ dualX D l R X A h).map f) ≫ _ = _ at hn
  erw [← Category.assoc, hn, Category.assoc]
  erw [hh]
  exact (Category.assoc _ _ _).symm

private theorem forgotten_transpose (h : Closed D l R X A) (K : W D l X) :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom ((U D l R X).map ((delta D l R X A h).app K)) (𝟙 _)) ≫
        forgottenEvaluation D l R X A ((dualX D l R X A h).obj (op K)) =
      ((NativeSectionClosed.ordinarySymmetry D l R X).braiding ((U D l R X).obj K)
            ((U D l R X).obj ((dualX D l R X A h).obj (op K)))).hom ≫
        forgottenEvaluation D l R X A K := by
  exact mapped_transpose A.closed.native.weilClosed
    (NativeSectionClosed.ordinaryClosed D l R X) A.closed.native.weilSymmetry
    (NativeSectionClosed.ordinarySymmetry D l R X)
    (NativeSectionClosed.ambientForget D l R X) A.closed.tensor A.closed.symmetric
    (nativeOmega D l R X A).obj K.obj

private theorem realized_transpose (hp : Permitted D l R X A) (M : C D l X)
    (z :
      (rho D l R X).obj M ⟶
        (rho D l R X).obj ((commonDual D l R X A hp).obj (op ((commonDual D l R X A hp).obj (op
          M)))))
    (hz :
      (NativeSectionClosed.ordinaryClosed D l R X).tensor.map (Prod.mkHom z (𝟙 _)) ≫
          realizedEvaluation D l R X A hp ((commonDual D l R X A hp).obj (op M)) =
        ((NativeSectionClosed.ordinarySymmetry D l R X).braiding ((rho D l R X).obj M)
              ((rho D l R X).obj ((commonDual D l R X A hp).obj (op M)))).hom ≫
          realizedEvaluation D l R X A hp M) :
    z = (rho D l R X).map (commonBidual D l R X A hp M) := by
  let := (R.data (geometric D X)).units
  let DM := (commonDual D l R X A hp).obj (op M)
  let f := (pullbackTensorCommonBraiding l (PadicAlgCl l)
    (geometric D X).base.left M DM).hom
  let g := (podCommonClosed l (PadicAlgCl l)
    (geometric D X).base.left).evaluation (pair D l R X A hp M)
  have hs := (R.data (geometric D X)).tensor.symmetric M DM
  have hb : (R.data (geometric D X)).tensor.tensor.hom.app (M, DM) ≫
      (rho D l R X).map (f ≫ g) =
    ((NativeSectionClosed.ordinarySymmetry D l R X).braiding
      ((rho D l R X).obj M) ((rho D l R X).obj DM)).hom ≫
        realizedEvaluation D l R X A hp M := by
    rw [(rho D l R X).map_comp, ← Category.assoc]
    simpa only [Category.assoc, realizedEvaluation, f, g, DM,
      NativeSectionClosed.ordinarySymmetry] using
      congrArg (fun q ↦ q ≫ (rho D l R X).map g) hs
  have ht := (R.data (geometric D X)).hom.transpose M
    (pair D l R X A hp DM) (f ≫ g)
  have ha := (congrArg
    ((NativeSectionClosed.ordinaryClosed D l R X).transpose
      ((rho D l R X).obj M) ((rho D l R X).obj DM)
      ((rho D l R X).obj (commonOmega D l R X A))) hb).symm.trans ht
  exact identify_transpose (NativeSectionClosed.ordinaryClosed D l R X)
    (realizationHomIso D l R X A hp DM) (realizedEvaluation D l R X A hp DM)
    ((R.data (geometric D X)).hom.evaluation (pair D l R X A hp DM))
    z ((rho D l R X).map (commonBidual D l R X A hp M)) _ ha hz

private theorem component_realization (hp : Permitted D l R X A) (h : Closed D l R X A)
    (K : W D l X) :
    (counit D l R X A K).hom ≫
        (U D l R X).map ((delta D l R X A h).app K) ≫ (secondComparison D l R X A hp h K).hom =
      (rho D l R X).map (commonBidual D l R X A hp ((model D l R X A).obj K)) := by
  let := (R.data (geometric D X)).units
  apply realized_transpose D l R X A hp
  let := (R.data (geometric D X)).tensor.closed.monoidal
  let := (R.data (geometric D X)).tensor.symmetry
  have ht :
    (rho D l R X).map (firstDualIso D l R X A hp h K).inv ≫
        (counit D l R X A ((dualX D l R X A h).obj (op K))).hom =
      (comparison D l R X A hp K).inv :=
    by
    change (rho D l R X).map ((realizationFullyFaithful D l R X).preimage _) ≫ _ = _
    rw [(realizationFullyFaithful D l R X).map_preimage]
    simp
  have hs :
    (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom (counit D l R X A K).hom (comparison D l R X A hp K).inv) ≫
        ((NativeSectionClosed.ordinarySymmetry D l R X).braiding _ _).hom =
      ((NativeSectionClosed.ordinarySymmetry D l R X).braiding _ _).hom ≫
        (NativeSectionClosed.ordinaryClosed D l R X).tensor.map
          (Prod.mkHom (comparison D l R X A hp K).inv (counit D l R X A K).hom) :=
    by exact CategoryTheory.BraidedCategory.braiding_naturality _ _
  have hv := congrArg (fun q ↦ q ≫ (dualizingComparison D l R X A).hom) (forgotten_transpose D l R
    X A h K)
  simp only [Category.assoc] at hv
  have hx := comparison_evaluation D l R X A hp K
  have hy := comparison_evaluation D l R X A hp ((dualX D l R X A h).obj (op K))
  have hh :=
    pairing_diagram (NativeSectionClosed.ordinaryClosed D l R X).tensor (counit D l R X A K)
      (comparison D l R X A hp K) (counit D l R X A ((dualX D l R X A h).obj (op K)))
      (comparison D l R X A hp ((dualX D l R X A h).obj (op K)))
      ((rho D l R X).map (firstDualIso D l R X A hp h K).inv)
      ((rho D l R X).map ((commonDual D l R X A hp).map (firstDualIso D l R X A hp h K).inv.op))
      ((U D l R X).map ((delta D l R X A h).app K))
      (forgottenEvaluation D l R X A K ≫ (dualizingComparison D l R X A).hom)
      (forgottenEvaluation D l R X A ((dualX D l R X A h).obj (op K)) ≫ (dualizingComparison D l R
        X A).hom)
      (realizedEvaluation D l R X A hp ((model D l R X A).obj K))
      (realizedEvaluation D l R X A hp ((model D l R X A).obj ((dualX D l R X A h).obj (op K))))
      (realizedEvaluation D l R X A hp ((commonDual D l R X A hp).obj (op ((model D l R X A).obj
        K))))
      ((NativeSectionClosed.ordinarySymmetry D l R X).braiding _ _).hom
      ((NativeSectionClosed.ordinarySymmetry D l R X).braiding _ _).hom ht
      (realized_evaluation_natural D l R X A hp (firstDualIso D l R X A hp h K).inv) hx hy hv hs
  simpa only [secondComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom,
    Category.assoc] using
    hh

/-- There is a natural native evaluation transpose, and its actual underlying
arrow, conjugated by j and b, is the realized common-stage evaluation transpose.
Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation/transposition
and coefficient-descent paragraphs; native refinement, proof steps 1--6
(blueprint: lem-sf-weil-bidual-evaluation-realization).

Proof:
1. Apply lem-sf-weil-native-closed-forgetful with W = nativeOmega. Its ambient
transpose nativeBidual is natural. The assumed closure permits restriction to
the full WeilComplex subcategory; its transpose equation retains the symmetry.
2. By thm-coef-qbar-verdier the common dual and its iterate are constructible.
Use lem-sf-adic-qbar-constructible-realization to write E_M for realized evaluation.
The ambient tensor-Hom adjunction (lem-sf-ringed-derived-closed-symmetric-monoidal)
makes z maps to E_DM composed with (z tensor 1) injective. Transposition of common
signed evaluation gives the analogous equation for rho(commonBidual M).
3. Uncurry sectionHomComparison and use the recorded realization evaluation law
for K and D_X K to obtain both comparison squares. Full faithfulness lifts
j_(D_X K) followed by c_K uniquely to t_K. Thus b_K is exactly c_(D_X K)
followed by rho D_Y(t_K inverse). Both evaluation squares use the same
exceptional-counit-normalized dualizingComparison h.
4. Naturality in the first Hom argument gives
E_DM (rho D(t inverse) tensor 1) = E_N (1 tensor rho(t inverse)), N = M_(D_X K).
This is uncurrying precomposition; both Hom comparisons preserve evaluation.
5. Put z = j_K followed by U(delta_K) followed by b_K. Substitute step 4 and
the evaluation square for D_X K. The native transpose equation gives the pairing
h e_K sigma (j_K tensor c_K inverse). Naturality of the signed symmetry and the
first evaluation square reduce this to E_M sigma. No cancellation of U on maps
is used.
6. The two uncurries agree, so injectivity in step 2 proves the displayed arrow
equality. Naturality of j,c,t and contravariant D gives naturality of b on every
native derived morphism, including extension morphisms. Only j,c,t,h are inverted;
the native transpose is never assumed invertible. -/
theorem bidual_evaluation_realization (h : Closed D l R X A) :
    ∃ hp : Permitted D l R X A,
    ∃ delta : 𝟭 (W D l X) ⟶ (dualX D l R X A h).rightOp ⋙ dualX D l R X A h,
      (∀ K : W D l X, (delta.app K).hom =
        nativeBidual A.closed.native.weilClosed A.closed.native.weilSymmetry
          (nativeOmega D l R X A).obj K.obj) ∧
      (∀ K : W D l X,
        A.closed.native.weilClosed.tensor.map
            (Prod.mkHom (delta.app K).hom (𝟙 ((dualX D l R X A h).obj (op K)).obj)) ≫
          A.closed.native.weilClosed.evaluation
            ((dualX D l R X A h).obj (op K)).obj (nativeOmega D l R X A).obj =
        (A.closed.native.weilSymmetry.braiding K.obj
            ((dualX D l R X A h).obj (op K)).obj).hom ≫
          A.closed.native.weilClosed.evaluation K.obj (nativeOmega D l R X A).obj) ∧
      (∀ K : W D l X,
        (counit D l R X A K).hom ≫ (U D l R X).map (delta.app K) ≫
            (secondComparison D l R X A hp h K).hom =
          (rho D l R X).map (commonBidual D l R X A hp ((model D l R X A).obj K))) ∧
      (∀ (K L : W D l X) (f : K ⟶ L),
        (U D l R X).map (((dualX D l R X A h).rightOp ⋙ dualX D l R X A h).map f) ≫
            (secondComparison D l R X A hp h L).hom =
          (secondComparison D l R X A hp h K).hom ≫ (rho D l R X).map
            (((commonDual D l R X A hp).rightOp ⋙ commonDual D l R X A hp).map
              ((model D l R X A).map f))) := by
  let hp := permitted D l R X A
  refine ⟨hp, delta D l R X A h, fun K ↦ rfl, ?_, ?_, ?_⟩
  · intro K
    exact native_transpose A.closed.native.weilClosed A.closed.native.weilSymmetry
      (nativeOmega D l R X A).obj K.obj
  · intro K
    exact component_realization D l R X A hp h K
  · intro K L f
    exact second_natural D l R X A hp h f

end WeilConjectures.NativeBidualRealization
