/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorPresentationComparison
public import WeilConjectures.PoincareDuality.ReindexingSystemHomReductionSquare
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseFlatKFlat

/-! # The ordinary scalar tensor reindexing square

Source: BS Remark 6.8.15; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] podCompletedRingMap coefficientMap
variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 800000 in
-- Compare the fully faithful restriction across the two module presentations.
private theorem presentation_model (k : Type u) [Field k]
    [Algebra (Padic l) k] [FiniteDimensional (Padic l) k] (X : Scheme.{u})
    (N : ConstructibleTensorCompletionPresentation l k X)
    (P Q : (integralOperationsGoodComplex l k X).FullSubcategory) :
    N.model.hom.app (P, Q) ≫ (tensorPresentationComparison l k X N).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      ((pullbackTensorCalculus l k X).integralTensorModel.iso _ _ _ _ _
        P.property.1 Q.property.1).hom := by
  let G := integralOperationsGoodComplex l k X
  let q := integralOperationsGoodLocalization l k X
  let i := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l k X) :
        ObjectProperty (CochainComplex (integralTowerModules l k X) ℤ)) G.ι
    (fun P ↦ P.property.1)
  let r := Functor.isoWhiskerLeft (i.prod i)
    (pullbackTensorCalculus l k X).integralTensorModel.comparison
  let T := (Functor.whiskeringLeft _ _
    (DerivedCategory (integralTowerModules l k X))).obj (q.prod q)
  let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l k X)).choose_spec.2.2
  let ff : T.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective T).2
      (fun U V ↦ h _ inferInstance U V)).some
  have ht := congrArg (fun τ ↦ τ.app (P, Q))
    (ff.map_preimage (X := N.tensor)
      (Y := (pullbackTensorCalculus l k X).integralClosed.tensor) (N.model.symm ≪≫ r).hom)
  change (tensorPresentationComparison l k X N).hom.app
    (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      N.model.inv.app (P, Q) ≫ r.hom.app (P, Q) at ht
  rw [ht, Iso.hom_inv_id_app_assoc]
  rfl

private theorem model_cancellation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b c : C} {z t : D}
    (r : a ⟶ c) (s : a ⟶ b) (e : b ≅ c)
    (v : F.obj b ⟶ z) (w : z ⟶ t) (d : F.obj a ⟶ t)
    (hr : s ≫ e.hom = r) (hd : F.map s ≫ v ≫ w = d) :
    F.map r ≫ (F.map e.inv ≫ v) ≫ w = d := by
  rw [← hr, F.map_comp]
  simpa only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
    F.map_id, Category.id_comp] using hd

private theorem ambient_scalar_representative (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E)
    (P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory) :
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (((pullbackTensorCalculus l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          X).integralTensorModel.iso
             _ _ _ _ _ P.property.1 Q.property.1).hom) ≫
      (finiteAmbientScalarTensor l X R A E N).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (N.balance.hom.app (P.obj, Q.obj)) ≫
      (A.models.iso _ _ _ _ _ (N.kflat P) (N.kflat Q)).hom := by
  exact model_cancellation (pbcDerivedExtend (coefficientMap l X R E)) _ _
    ((tensorPresentationComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
        N.completion).app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    (N.ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) _ _
    (presentation_model l _ X N.completion P Q) (N.representative P Q)

private theorem scalar_total_ext (k : Type u) [Field k]
    [Algebra (Padic l) k] [FiniteDimensional (Padic l) k] {X : Scheme.{u}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : completedIntegralCommRingSheafUnrestricted l k X ⟶ S)
    (P Q : CochainComplex (integralTowerModules l k X) ℤ)
    (L : CochainComplex (pbcModules X S) ℤ)
    {f g : ((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj
      ((constructibleTensorTotal l k X).obj (P, Q)) ⟶ L}
    (hh : ∀ (p q : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (f.f (p + q)).val.app U
        (pbcTensorSection a _ U 1 (constructibleTensorTotalSection l k X P Q p q U x y)) =
      (g.f (p + q)).val.app U
        (pbcTensorSection a _ U 1 (constructibleTensorTotalSection l k X P Q p q U x y))) :
    f = g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ((pbcScalarAdjunction a).homEquiv _ (L.X n)).injective
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l k X)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intros p q h
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext
    (completedIntegralCommRingSheafUnrestricted l k X) (P.X p) (Q.X q)
  intros U x y
  subst n
  change (f.f (p + q)).val.app U
      (((pbcScalarAdjunction a).unit.app _).val.app U
        (constructibleTensorTotalSection l k X P Q p q U x y)) =
    (g.f (p + q)).val.app U
      (((pbcScalarAdjunction a).unit.app _).val.app U
        (constructibleTensorTotalSection l k X P Q p q U x y))
  erw [(pbcScalarAdjunction_exists a).exists.choose_spec]
  exact hh p q U x y

private theorem scalar_map_section {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules X R} (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcExtend a).map f).val.app U (pbcTensorSection a M U 1 x) =
      pbcTensorSection a N U 1 (f.val.app U x) := by
  exact reductionTensor_map X a f U 1 x

private theorem inverse_integral_reindex_section
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (V : IntegralReindex l X g B E)
    (M : integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)
    (U : X.ProEtᵒᵖ) (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    (V.balance.inv.app M).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        ((podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj M)
        U 1 x) =
    pbcTensorSection (coefficientMap l Y S E) M
      ((proEtaleIsoPostcompose g).op.obj U) 1 x := by
  have hs := V.sections M U 1 x
  rw [map_one] at hs
  have hi := congrArg ((V.balance.inv.app M).val.app U) hs
  have hc := congrArg (fun f ↦ f.val.app U
    (pbcTensorSection (coefficientMap l Y S E) M
      ((proEtaleIsoPostcompose g).op.obj U) 1 x)) (V.balance.hom_inv_id_app M)
  exact hi.symm.trans hc

private theorem map_pair_comp {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {a b c x y z : C}
    (f : a ⟶ b) (f' : b ⟶ c) (g : x ⟶ y) (g' : y ⟶ z) :
    T.map (Prod.mkHom (f ≫ f') (g ≫ g')) =
      T.map (Prod.mkHom f g) ≫ T.map (Prod.mkHom f' g') := by
  simpa only [prod_comp] using T.map_comp (Prod.mkHom f g) (Prod.mkHom f' g')

private theorem pair_isIso {C D : Type*} [Category C] [Category D]
    {a b : C} {x y : D} (f : a ⟶ b) (g : x ⟶ y) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (isIso_prod_iff (f := Prod.mkHom f g)).2 ⟨inferInstance, inferInstance⟩

attribute [local instance] pair_isIso

-- This diagram lemma keeps the coefficient constructions out of reassociation.
private theorem paste_left {C : Type*} [Category C]
    {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₉ a₂₀ : C}
    (i : a₀ ⟶ a₂) (mu : a₂ ⟶ a₃) (v : a₃ ⟶ a₄)
    (sy : a₄ ⟶ a₅) (w : a₅ ⟶ a₆) (e : a₆ ⟶ a₇) (d : a₇ ⟶ a₈)
    (j : a₀ ⟶ a₁₀) (h : a₉ ≅ a₁₀) (r : a₉ ⟶ a₃)
    (v' : a₉ ⟶ a₁₂) (ry : a₁₂ ⟶ a₄) (ey : a₅ ⟶ a₁₇)
    (w' : a₁₇ ⟶ a₇) (epsy : a₁₂ ⟶ a₁₃) (byy : a₁₃ ⟶ a₁₅)
    (my : a₁₅ ⟶ a₁₇) (dt : a₁₅ ⟶ a₁₆) (cw : a₁₆ ⟶ a₁₉)
    (mx : a₁₉ ⟶ a₈) (dc : a₁₃ ⟶ a₁₄) (cb : a₁₄ ⟶ a₁₆)
    (epsx : a₁₀ ⟶ a₁₁) (cv : a₁₁ ⟶ a₁₄)
    (eps : a₀ ⟶ a₂₀) (cj : a₂₀ ⟶ a₁₁)
    (hmu : i ≫ mu = j ≫ h.inv ≫ r)
    (hv : r ≫ v = v' ≫ ry)
    (hw : w ≫ e = ey ≫ w')
    (hsy : ry ≫ sy ≫ ey = epsy ≫ byy ≫ my)
    (hw' : my ≫ w' ≫ d = dt ≫ cw ≫ mx)
    (hd : byy ≫ dt = dc ≫ cb)
    (hv' : v' ≫ epsy ≫ dc = h.hom ≫ epsx ≫ cv)
    (heps : j ≫ epsx = eps ≫ cj) :
    i ≫ mu ≫ v ≫ sy ≫ w ≫ e ≫ d =
      eps ≫ cj ≫ cv ≫ cb ≫ cw ≫ mx := by
  slice_lhs 1 2 => exact hmu
  slice_lhs 3 4 => exact hv
  slice_lhs 6 7 => exact hw
  slice_lhs 4 6 => exact hsy
  slice_lhs 6 8 => exact hw'
  slice_lhs 5 6 => exact hd
  slice_lhs 3 5 => exact hv'
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 1 2 => exact heps
  simp only [Category.assoc]

private theorem paste_right {C : Type*} [Category C]
    {a b c d e f g h i j k : C}
    (aa : a ⟶ b) (ss : b ⟶ c) (tt : c ⟶ d) (uu : d ⟶ e)
    (rr : a ⟶ f) (ss' : f ⟶ g) (vv : g ⟶ c)
    (zz : g ⟶ h) (pp : h ⟶ e) (ee : a ⟶ i) (bb : i ⟶ j)
    (mm : j ⟶ h) (qq : j ⟶ k) (nn : k ⟶ e)
    (ha : aa ≫ ss = rr ≫ ss' ≫ vv)
    (hv : vv ≫ tt ≫ uu = zz ≫ pp)
    (hr : rr ≫ ss' ≫ zz = ee ≫ bb ≫ mm)
    (hn : mm ≫ pp = qq ≫ nn) :
    aa ≫ ss ≫ tt ≫ uu = ee ≫ bb ≫ qq ≫ nn := by
  slice_lhs 1 2 => exact ha
  slice_lhs 3 5 => exact hv
  slice_lhs 1 3 => exact hr
  slice_lhs 3 4 => exact hn

private def scalar_counit {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend a ⟶
      (pbcExtend a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := pbcComplexCounit a P
  naturality := by
    intro P Q f
    simpa only [complexCounitNat_app, reductionComplexCounit, pbcComplexCounit] using
      (complexCounitNat (pbcExtend a) (pbcDerivedExtend a)
        (pbcExtensionCounit a)).naturality f

private theorem scalar_counit_iso {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (pbcModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := R) P) :
    IsIso (pbcComplexCounit a P) := by
  dsimp only [pbcComplexCounit]
  have := pbcExtensionCounit_isIso a P hP
  infer_instance

private theorem iso_rotate {C : Type*} [Category C]
    {a b c d e f : C} (i : a ≅ b) (j : b ≅ c) (k : c ≅ d)
    (v : d ≅ e) (s : a ≅ f) (t : f ≅ e)
    (h : i.hom ≫ j.hom ≫ k.hom ≫ v.hom = s.hom ≫ t.hom) :
    k.inv ≫ j.inv ≫ i.inv = v.hom ≫ t.inv ≫ s.inv := by
  have hh : i ≪≫ j ≪≫ k ≪≫ v = s ≪≫ t := Iso.ext h
  have hi := congrArg (fun z ↦ v.hom ≫ z.inv) hh
  simpa only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc] using hi

private theorem solve_suffix {C : Type*} [Category C]
    {a b c d e : C} (i : a ⟶ b) (m : b ⟶ c) (r : d ≅ c) (h : d ≅ e)
    (j : a ⟶ e) (hj : i ≫ m ≫ r.inv ≫ h.hom = j) :
    i ≫ m = j ≫ h.inv ≫ r.hom := by
  calc
    i ≫ m = (i ≫ m ≫ r.inv ≫ h.hom) ≫ h.inv ≫ r.hom := by simp
    _ = j ≫ h.inv ≫ r.hom := by rw [hj]

private theorem inverse_representative {C : Type*} [Category C]
    {a b c d : C} (v : a ≅ b) (e : b ⟶ c) (f : a ⟶ d) (w : d ≅ c)
    (h : v.hom ≫ e = f ≫ w.hom) : v.inv ≫ f = e ≫ w.inv := by
  calc
    v.inv ≫ f = v.inv ≫ (f ≫ w.hom) ≫ w.inv := by simp
    _ = v.inv ≫ (v.hom ≫ e) ≫ w.inv := by rw [h]
    _ = e ≫ w.inv := by simp

private theorem completed_inverse_good (k : Type u) [Field k]
    [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l k Y) ℤ)
    (hP : integralOperationsGoodComplex l k Y P) :
    integralOperationsGoodComplex l k X
      (((podCompletedModuleInverseImage l k g).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l k Y) ≅
        completedIntegralCommRingSheafUnrestricted l k X :=
    W.preimageIso (asIso (podCompletedRingMap l k g))
  have he : W.map e.hom = podCompletedRingMap l k g := W.map_preimage _
  have hF : podCompletedModuleInverseImage l k g =
      isoSectionwiseModuleInverseImage.{u, u} g (W.mapIso e).hom := by
    unfold podCompletedModuleInverseImage
    simp only [Functor.mapIso_hom, he]
  have h := isoSectionwiseModuleInverseImage_flat_kFlat g
    (completedIntegralCommRingSheafUnrestricted l k Y)
    (completedIntegralCommRingSheafUnrestricted l k X) e
    (podCompletedModuleInverseImage l k g) hF
  exact ⟨h.2 P hP.1, fun n ↦ h.1 (P.X n) (hP.2 n)⟩

section IntegralModel
variable (k : Type u) [Field k] [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (μ : (pullbackTensorCalculus l k Y).integralClosed.tensor ⋙
      podCompletedDerivedInverseImage l k g ≅
    (podCompletedDerivedInverseImage l k g).prod
      (podCompletedDerivedInverseImage l k g) ⋙
        (pullbackTensorCalculus l k X).integralClosed.tensor)
  (T : SemilinearSections.TensorComparisonModel.{u + 1, u, u}
    (ProEt.topology Y) (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l k Y)
    (completedIntegralCommRingSheafUnrestricted l k X)
    (podCompletedModuleInverseImage l k g)
    (pullbackTensorCalculus l k Y).integralClosed
    (pullbackTensorCalculus l k X).integralClosed
    (pullbackTensorCalculus l k Y).integralTensorModel
    (pullbackTensorCalculus l k X).integralTensorModel μ)

private theorem integral_chain_sections
    (hp : ∀ (M N : integralTowerModules l k Y) (U : X.ProEt)
      (x : M.val.obj (Opposite.op ((proEtaleIsoPostcompose g).obj U)))
      (y : N.val.obj (Opposite.op ((proEtaleIsoPostcompose g).obj U))),
      (T.ordinary M N).hom.val.app (Opposite.op U)
        (SemilinearSections.tensorSection.{u + 1, u, u} (ProEt.topology Y)
          (completedIntegralCommRingSheafUnrestricted l k Y) M N
          (Opposite.op ((proEtaleIsoPostcompose g).obj U)) x y) =
        SemilinearSections.tensorSection.{u + 1, u, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l k X)
          ((podCompletedModuleInverseImage l k g).obj M)
          ((podCompletedModuleInverseImage l k g).obj N) (Opposite.op U) x y)
    (P Q : CochainComplex (integralTowerModules l k Y) ℤ)
    (p q : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj ((proEtaleIsoPostcompose g).op.obj U))
    (y : (Q.X q).val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    ((T.chain P Q).f (p + q)).val.app U
      (constructibleTensorTotalSection l k X
        (((podCompletedModuleInverseImage l k g).mapHomologicalComplex (.up ℤ)).obj P)
        (((podCompletedModuleInverseImage l k g).mapHomologicalComplex (.up ℤ)).obj Q)
        p q U x y) =
      constructibleTensorTotalSection l k Y P Q p q
        ((proEtaleIsoPostcompose g).op.obj U) x y := by
  have hi := congrArg ((T.ordinary (P.X p) (Q.X q)).inv.val.app U)
    (hp (P.X p) (Q.X q) U.unop x y)
  have hc := congrArg (fun f ↦ f.val.app U
    (SemilinearSections.tensorSection.{u + 1, u, u} (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l k Y) (P.X p) (Q.X q)
      ((proEtaleIsoPostcompose g).op.obj U) x y))
    (T.ordinary (P.X p) (Q.X q)).hom_inv_id
  have hinv := hi.symm.trans hc
  have hs := congrArg (fun f ↦ f.val.app U
    (SemilinearSections.tensorSection.{u + 1, u, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l k X)
      ((podCompletedModuleInverseImage l k g).obj (P.X p))
      ((podCompletedModuleInverseImage l k g).obj (Q.X q)) U x y))
    (T.summand P Q p q (p + q) rfl)
  change ((T.chain P Q).f (p + q)).val.app U _ =
    (SemilinearSections.tensorSummand.{u + 1, u, u} (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l k Y) P Q p q (p + q) rfl).val.app
      ((proEtaleIsoPostcompose g).op.obj U)
      ((T.ordinary (P.X p) (Q.X q)).inv.val.app U _) at hs
  rw [hinv] at hs
  exact hs

end IntegralModel

private def cochain_comparison {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

-- Give components their expanded endpoints before using concrete tensor functors.
private def tensor_component {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C × C ⥤ D) (F : D ⥤ E) (G : C ⥤ E) (S : E × E ⥤ E)
    (α : T ⋙ F ⟶ G.prod G ⋙ S) (P Q : C) :
    F.obj (T.obj (P, Q)) ⟶ S.obj (G.obj P, G.obj Q) := by
  simpa only [Functor.comp_obj, Functor.prod_obj] using α.app (P, Q)

private theorem tensor_component_eq {C D E : Type*}
    [Category C] [Category D] [Category E]
    (T : C × C ⥤ D) (F : D ⥤ E) (G : C ⥤ E) (S : E × E ⥤ E)
    (α : T ⋙ F ⟶ G.prod G ⋙ S) (P Q : C) :
    tensor_component T F G S α P Q = α.app (P, Q) := rfl

attribute [local irreducible] tensor_component

private theorem native_total_map_generator (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P Q P' Q' : CochainComplex (proEtaleRingModules X R) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (p q i : ℤ) (h : p + q = i) (U : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) R).map
      (Prod.mkHom a b)).f i).val.app U
        (coefficientTensorGenerator.{u + 1, u + 1, u}
          (ProEt.topology X) R P Q p q i h U x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u}
        (ProEt.topology X) R P' Q' p q i h U
        ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  simpa only [coefficientTotalTensor, coefficientTensorGenerator] using
    coefficientTotalTensor_map_generator X R a b p q i h U x y

section CochainSquare
attribute [local irreducible] SheafOfModules.monoidalCategory
  LocallyFiniteAdicRealization.ringSheaf
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S)
  (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
  (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S C E)
  (V : IntegralReindex l X g B E) (W : ReindexTensor l X g A C B)
section CochainCalculation
attribute [local irreducible] coefficientTotalTensor

attribute [local irreducible] Scheme.residueField in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Compare the scalar-extension module structures without expanding their chosen data.
private theorem cochain_scalar_square :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let Hc : CochainComplex (integralTowerModules l k Y) ℤ ⥤
        CochainComplex (integralTowerModules l k X) ℤ :=
      (podCompletedModuleInverseImage l k g).mapHomologicalComplex (.up ℤ)
    let Fc := (modulePull l X g B).mapHomologicalComplex (.up ℤ)
    let eX := integralComplex l X R E
    let eY := integralComplex l Y S E
    let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
    let cX := constructibleTensorTotal l k X
    let cY := constructibleTensorTotal l k Y
    let v : eY ⋙ Fc ≅ Hc ⋙ eX := by
      simpa only [eX, eY, Fc, Hc, integralComplex] using
        cochain_comparison (pbcExtend (coefficientMap l Y S E)) (modulePull l X g B)
          (podCompletedModuleInverseImage l k g) (pbcExtend (coefficientMap l X R E))
          V.balance
    ∀ (P Q : CochainComplex (integralTowerModules l k Y) ℤ)
    (J : cX.obj (Hc.obj P, Hc.obj Q) ⟶ Hc.obj (cY.obj (P, Q)))
    (_hJ : ∀ (p q : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj ((proEtaleIsoPostcompose g).op.obj U))
      (y : (Q.X q).val.obj ((proEtaleIsoPostcompose g).op.obj U)),
      (J.f (p + q)).val.app U
        (constructibleTensorTotalSection l k X (Hc.obj P) (Hc.obj Q) p q U x y) =
      constructibleTensorTotalSection l k Y P Q p q
        ((proEtaleIsoPostcompose g).op.obj U) x y),
    eX.map J ≫ v.inv.app (cY.obj (P, Q)) ≫
        Fc.map (tensor_component cY eY eY
          (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S))
          NY.balance.hom P Q) ≫
        tensor_component
          (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S))
          Fc Fc tX W.cochain.hom (eY.obj P) (eY.obj Q) =
      tensor_component cX eX eX tX NX.balance.hom (Hc.obj P) (Hc.obj Q) ≫
        tX.map (X := (eX.obj (Hc.obj P), eX.obj (Hc.obj Q)))
          (Y := (Fc.obj (eY.obj P), Fc.obj (eY.obj Q)))
          (Prod.mkHom (v.inv.app P) (v.inv.app Q)) := by
  intros k Hc Fc eX eY tX cX cY v P Q J hJ
  simp only [tensor_component_eq]
  apply scalar_total_ext l k (coefficientMap l X R E) (Hc.obj P) (Hc.obj Q)
  intros p q U x y
  change (P.X p).val.obj ((proEtaleIsoPostcompose g).op.obj U) at x
  change (Q.X q).val.obj ((proEtaleIsoPostcompose g).op.obj U) at y
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((W.cochain.hom.app (eY.obj P, eY.obj Q)).f (p + q)).val.app U
      (((NY.balance.hom.app (P, Q)).f (p + q)).val.app
        ((proEtaleIsoPostcompose g).op.obj U)
        ((V.balance.inv.app ((cY.obj (P, Q)).X (p + q))).val.app U
          (((pbcExtend (coefficientMap l X R E)).map (J.f (p + q))).val.app U
            (pbcTensorSection (coefficientMap l X R E) _ U 1
              (constructibleTensorTotalSection l k X (Hc.obj P) (Hc.obj Q)
                p q U x y))))) = _
  have hs := scalar_map_section (coefficientMap l X R E) (J.f (p + q)) U
    (constructibleTensorTotalSection l k X (Hc.obj P) (Hc.obj Q) p q U x y)
  have hj := congrArg
    (pbcTensorSection (coefficientMap l X R E) ((Hc.obj (cY.obj (P, Q))).X (p + q)) U 1)
    (hJ p q U x y)
  have hi := inverse_integral_reindex_section l g B E V
    ((cY.obj (P, Q)).X (p + q)) U
    (constructibleTensorTotalSection l k Y P Q p q
      ((proEtaleIsoPostcompose g).op.obj U) x y)
  have ht := (congrArg ((V.balance.inv.app ((cY.obj (P, Q)).X (p + q))).val.app U)
    (hs.trans hj)).trans hi
  have hn := congrArg
    (fun z ↦ ((W.cochain.hom.app (eY.obj P, eY.obj Q)).f (p + q)).val.app U
      (((NY.balance.hom.app (P, Q)).f (p + q)).val.app
        ((proEtaleIsoPostcompose g).op.obj U) z)) ht
  refine hn.trans ?_
  simp only [cY]
  have hny := congrArg
    (((W.cochain.hom.app (eY.obj P, eY.obj Q)).f (p + q)).val.app U)
    (NY.balance_sections P Q p q ((proEtaleIsoPostcompose g).op.obj U) 1 x y)
  refine hny.trans ?_
  have hw := W.pure (eY.obj P) (eY.obj Q) p q U
    (pbcTensorSection (coefficientMap l Y S E) (P.X p)
      ((proEtaleIsoPostcompose g).op.obj U) 1 x)
    (pbcTensorSection (coefficientMap l Y S E) (Q.X q)
      ((proEtaleIsoPostcompose g).op.obj U) 1 y)
  refine hw.trans ?_
  have hx := congrArg
    (((tX.map (Prod.mkHom (v.inv.app P) (v.inv.app Q))).f (p + q)).val.app U)
    (NX.balance_sections (Hc.obj P) (Hc.obj Q) p q U 1 x y)
  have ht := native_total_map_generator X (ring l X R)
    (v.inv.app P) (v.inv.app Q) p q (p + q) rfl U
    (pbcTensorSection (coefficientMap l X R E) ((Hc.obj P).X p) U 1 x)
    (pbcTensorSection (coefficientMap l X R E) ((Hc.obj Q).X q) U 1 y)
  have hp : ((v.inv.app P).f p).val.app U
      (pbcTensorSection (coefficientMap l X R E) ((Hc.obj P).X p) U 1 x) =
    pbcTensorSection (coefficientMap l Y S E) (P.X p)
      ((proEtaleIsoPostcompose g).op.obj U) 1 x := by
    change (V.balance.inv.app (P.X p)).val.app U
      (pbcTensorSection (coefficientMap l X R E) _ U 1 x) = _
    exact inverse_integral_reindex_section l g B E V (P.X p) U x
  have hq : ((v.inv.app Q).f q).val.app U
      (pbcTensorSection (coefficientMap l X R E) ((Hc.obj Q).X q) U 1 y) =
    pbcTensorSection (coefficientMap l Y S E) (Q.X q)
      ((proEtaleIsoPostcompose g).op.obj U) 1 y := by
    change (V.balance.inv.app (Q.X q)).val.app U
      (pbcTensorSection (coefficientMap l X R E) _ U 1 y) = _
    exact inverse_integral_reindex_section l g B E V (Q.X q) U y
  have hh := congrArg₂
    (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
      (Fc.obj (eY.obj P)) (Fc.obj (eY.obj Q)) p q (p + q) rfl U) hp hq
  exact ((hx.trans ht).trans hh).symm

end CochainCalculation

private theorem cancel_mapped_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b : C} {z : D} (e : a ≅ b)
    (f : F.obj a ⟶ z) (g : F.obj b ⟶ z) (h : f = F.map e.hom ≫ g) :
    F.map e.inv ≫ f = g := by
  rw [h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

-- Keep the diagram calculation independent of the concrete tensor endpoints.
private theorem scalar_square_pasting
    {IX IY OX OY DX DY AX AY : Type*}
    [Category IX] [Category IY] [Category OX] [Category OY]
    [Category DX] [Category DY] [Category AX] [Category AY]
    (qX : IX ⥤ DX) (qY : IY ⥤ DY) (oX : OX ⥤ AX) (oY : OY ⥤ AY)
    (Hc : IY ⥤ IX) (Fc : OY ⥤ OX) (eX : IX ⥤ OX) (eY : IY ⥤ OY)
    (H : DY ⥤ DX) (F : AY ⥤ AX) (EX : DX ⥤ AX) (EY : DY ⥤ AY)
    (cX : IX × IX ⥤ IX) (cY : IY × IY ⥤ IY)
    (tX : OX × OX ⥤ OX) (tY : OY × OY ⥤ OY)
    (TX : DX × DX ⥤ DX) (TY : DY × DY ⥤ DY)
    (aX : AX × AX ⥤ AX) (aY : AY × AY ⥤ AY)
    (δH : qY ⋙ H ≅ Hc ⋙ qX) (δF : oY ⋙ F ≅ Fc ⋙ oX)
    (εX : qX ⋙ EX ⟶ eX ⋙ oX) (εY : qY ⋙ EY ⟶ eY ⋙ oY)
    (v : eY ⋙ Fc ≅ Hc ⋙ eX) (vd : EY ⋙ F ≅ H ⋙ EX)
    (bX : cX ⋙ eX ≅ eX.prod eX ⋙ tX)
    (bY : cY ⋙ eY ≅ eY.prod eY ⋙ tY)
    (w : tY ⋙ Fc ≅ Fc.prod Fc ⋙ tX)
    (μ : TY ⋙ H ≅ H.prod H ⋙ TX)
    (σX : TX ⋙ EX ≅ EX.prod EX ⋙ aX)
    (σY : TY ⋙ EY ≅ EY.prod EY ⋙ aY)
    (ω : aY ⋙ F ≅ F.prod F ⋙ aX)
    (P Q : IY)
    (rX : qX.obj (cX.obj (Hc.obj P, Hc.obj Q)) ≅
      TX.obj (qX.obj (Hc.obj P), qX.obj (Hc.obj Q)))
    (rY : qY.obj (cY.obj (P, Q)) ≅ TY.obj (qY.obj P, qY.obj Q))
    (mX : oX.obj (tX.obj (eX.obj (Hc.obj P), eX.obj (Hc.obj Q))) ≅
      aX.obj (oX.obj (eX.obj (Hc.obj P)), oX.obj (eX.obj (Hc.obj Q))))
    (mY : oY.obj (tY.obj (eY.obj P, eY.obj Q)) ≅
      aY.obj (oY.obj (eY.obj P), oY.obj (eY.obj Q)))
    (mF : oX.obj (tX.obj (Fc.obj (eY.obj P), Fc.obj (eY.obj Q))) ≅
      aX.obj (oX.obj (Fc.obj (eY.obj P)), oX.obj (Fc.obj (eY.obj Q))))
    (J : cX.obj (Hc.obj P, Hc.obj Q) ⟶ Hc.obj (cY.obj (P, Q)))
    (hchain : eX.map J ≫ v.inv.app (cY.obj (P, Q)) ≫
      Fc.map (bY.hom.app (P, Q)) ≫ w.hom.app (eY.obj P, eY.obj Q) =
      bX.hom.app (Hc.obj P, Hc.obj Q) ≫
        tX.map (Prod.mkHom (v.inv.app P) (v.inv.app Q)))
    (hmu : EX.map (rX.hom ≫ TX.map
        (Prod.mkHom (δH.inv.app P) (δH.inv.app Q))) ≫
        EX.map (μ.inv.app (qY.obj P, qY.obj Q)) =
      EX.map (qX.map J) ≫ EX.map (δH.inv.app (cY.obj (P, Q))) ≫ EX.map (H.map rY.hom))
    (hv : ∀ Z, vd.inv.app (qY.obj Z) ≫ F.map (εY.app Z) ≫ δF.hom.app (eY.obj Z) =
      EX.map (δH.hom.app Z) ≫ εX.app (Hc.obj Z) ≫ oX.map (v.inv.app Z))
    (hx : EX.map rX.hom ≫ σX.hom.app (qX.obj (Hc.obj P), qX.obj (Hc.obj Q)) ≫
      aX.map (Prod.mkHom (εX.app (Hc.obj P)) (εX.app (Hc.obj Q))) =
      εX.app (cX.obj (Hc.obj P, Hc.obj Q)) ≫
        oX.map (bX.hom.app (Hc.obj P, Hc.obj Q)) ≫ mX.hom)
    (hy : EY.map rY.hom ≫ σY.hom.app (qY.obj P, qY.obj Q) ≫
      aY.map (Prod.mkHom (εY.app P) (εY.app Q)) =
      εY.app (cY.obj (P, Q)) ≫ oY.map (bY.hom.app (P, Q)) ≫ mY.hom)
    (hw : F.map mY.hom ≫ ω.hom.app (oY.obj (eY.obj P), oY.obj (eY.obj Q)) ≫
      aX.map (Prod.mkHom (δF.hom.app (eY.obj P)) (δF.hom.app (eY.obj Q))) =
      δF.hom.app (tY.obj (eY.obj P, eY.obj Q)) ≫
        oX.map (w.hom.app (eY.obj P, eY.obj Q)) ≫ mF.hom)
    (hm : mX.hom ≫ aX.map
      (Prod.mkHom (oX.map (v.inv.app P)) (oX.map (v.inv.app Q))) =
      oX.map (tX.map (Prod.mkHom (v.inv.app P) (v.inv.app Q))) ≫ mF.hom)
    [IsIso (εY.app P)] [IsIso (εY.app Q)] :
    EX.map (μ.inv.app (qY.obj P, qY.obj Q)) ≫
      vd.inv.app (TY.obj (qY.obj P, qY.obj Q)) ≫
      F.map (σY.hom.app (qY.obj P, qY.obj Q)) ≫
      ω.hom.app (EY.obj (qY.obj P), EY.obj (qY.obj Q)) =
    σX.hom.app (H.obj (qY.obj P), H.obj (qY.obj Q)) ≫
      aX.map (Prod.mkHom (vd.inv.app (qY.obj P)) (vd.inv.app (qY.obj Q))) := by
  let i := EX.map (rX.hom ≫ TX.map
    (Prod.mkHom (δH.inv.app P) (δH.inv.app Q)))
  let e := aX.map (Prod.mkHom (F.map (εY.app P)) (F.map (εY.app Q)))
  let d := aX.map (Prod.mkHom (δF.hom.app (eY.obj P)) (δF.hom.app (eY.obj Q)))
  have left : i ≫ EX.map (μ.inv.app (qY.obj P, qY.obj Q)) ≫
      vd.inv.app (TY.obj (qY.obj P, qY.obj Q)) ≫
      F.map (σY.hom.app (qY.obj P, qY.obj Q)) ≫
      ω.hom.app (EY.obj (qY.obj P), EY.obj (qY.obj Q)) ≫ e ≫ d =
    εX.app (cX.obj (Hc.obj P, Hc.obj Q)) ≫
      oX.map (eX.map J ≫ v.inv.app (cY.obj (P, Q)) ≫
        Fc.map (bY.hom.app (P, Q)) ≫ w.hom.app (eY.obj P, eY.obj Q)) ≫ mF.hom := by
    simp only [Functor.map_comp, Category.assoc]
    exact paste_left i _ _ _ _ e d (EX.map (qX.map J))
      (EX.mapIso (δH.app (cY.obj (P, Q)))) (EX.map (H.map rY.hom))
      (vd.inv.app (qY.obj (cY.obj (P, Q)))) (F.map (EY.map rY.hom))
      (F.map (aY.map (Prod.mkHom (εY.app P) (εY.app Q))))
      (ω.hom.app (oY.obj (eY.obj P), oY.obj (eY.obj Q)))
      (F.map (εY.app (cY.obj (P, Q)))) (F.map (oY.map (bY.hom.app (P, Q))))
      (F.map mY.hom) (δF.hom.app (tY.obj (eY.obj P, eY.obj Q)))
      (oX.map (w.hom.app (eY.obj P, eY.obj Q))) mF.hom
      (δF.hom.app (eY.obj (cY.obj (P, Q)))) (oX.map (Fc.map (bY.hom.app (P, Q))))
      (εX.app (Hc.obj (cY.obj (P, Q)))) (oX.map (v.inv.app (cY.obj (P, Q))))
      (εX.app (cX.obj (Hc.obj P, Hc.obj Q))) (oX.map (eX.map J))
      hmu (vd.inv.naturality rY.hom)
      (ω.hom.naturality (Prod.mkHom (εY.app P) (εY.app Q))).symm
      (by simpa only [Functor.map_comp] using congrArg F.map hy)
      hw (δF.hom.naturality (bY.hom.app (P, Q))) (hv (cY.obj (P, Q)))
      (εX.naturality J)
  have hvp := cancel_mapped_iso EX (δH.app P) _ _ (hv P)
  have hvq := cancel_mapped_iso EX (δH.app Q) _ _ (hv Q)
  have right : i ≫ σX.hom.app (H.obj (qY.obj P), H.obj (qY.obj Q)) ≫
      aX.map (Prod.mkHom (vd.inv.app (qY.obj P)) (vd.inv.app (qY.obj Q))) ≫ e ≫ d =
    εX.app (cX.obj (Hc.obj P, Hc.obj Q)) ≫
      oX.map (bX.hom.app (Hc.obj P, Hc.obj Q) ≫
        tX.map (Prod.mkHom (v.inv.app P) (v.inv.app Q))) ≫ mF.hom := by
    simp only [Functor.map_comp, Category.assoc]
    apply paste_right i _ _ (e ≫ d) (EX.map rX.hom)
      (σX.hom.app (qX.obj (Hc.obj P), qX.obj (Hc.obj Q)))
      (aX.map (Prod.mkHom (EX.map (δH.inv.app P)) (EX.map (δH.inv.app Q))))
      (aX.map (Prod.mkHom (εX.app (Hc.obj P)) (εX.app (Hc.obj Q))))
      (aX.map (Prod.mkHom (oX.map (v.inv.app P)) (oX.map (v.inv.app Q))))
      (εX.app (cX.obj (Hc.obj P, Hc.obj Q)))
      (oX.map (bX.hom.app (Hc.obj P, Hc.obj Q))) mX.hom
      (oX.map (tX.map (Prod.mkHom (v.inv.app P) (v.inv.app Q)))) mF.hom
    · simpa only [i, Functor.map_comp, Functor.comp_map, Functor.comp_obj,
        Functor.prod_map, Functor.prod_obj, Category.assoc] using
        congrArg (fun z ↦ EX.map rX.hom ≫ z)
          (σX.hom.naturality (Prod.mkHom (δH.inv.app P) (δH.inv.app Q)))
    · have hh := congrArg₂ (fun f g ↦ aX.map (Prod.mkHom f g)) hvp hvq
      simpa only [map_pair_comp, e, d, Category.assoc, Iso.app_inv] using hh
    · exact hx
    · exact hm
  have hi : IsIso i := by dsimp only [i]; infer_instance
  have he : IsIso e := by dsimp only [e]; infer_instance
  have hd : IsIso d := by dsimp only [d]; infer_instance
  apply (cancel_epi i).1
  apply (cancel_mono (e ≫ d)).1
  have hh := congrArg
    (fun z ↦ εX.app (cX.obj (Hc.obj P, Hc.obj Q)) ≫ oX.map z ≫ mF.hom) hchain
  simpa only [Category.assoc] using left.trans (hh.trans right.symm)

attribute [local irreducible] finiteAmbientScalarTensor
  tensorPresentationComparison pullbackTensorCalculus in
attribute [local irreducible] Scheme.residueField in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Normalize the endpoints of the scalar counits and the two tensor representative diagrams.
private theorem inverse_square_good :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let G := integralOperationsGoodComplex l k Y
    ∀ P Q : G.FullSubcategory,
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := derivedPull l X g B
    let H := podCompletedDerivedInverseImage l k g
    let σX := finiteAmbientScalarTensor l X R A E NX
    let σY := finiteAmbientScalarTensor l Y S C E NY
    let μ := podCompletedAmbientTensor l k g
    EX.map (μ.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        V.derived.inv.app ((pullbackTensorCalculus l k Y).integralClosed.tensor.obj
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        F.map (σY.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        W.tensor.hom.app (EY.obj (DerivedCategory.Q.obj P.obj),
          EY.obj (DerivedCategory.Q.obj Q.obj)) =
      σX.hom.app (H.obj (DerivedCategory.Q.obj P.obj),
        H.obj (DerivedCategory.Q.obj Q.obj)) ≫
        A.closed.tensor.map (Prod.mkHom (V.derived.inv.app (DerivedCategory.Q.obj P.obj))
          (V.derived.inv.app (DerivedCategory.Q.obj Q.obj))) := by
  intros k G P Q EX EY F H σX σY μ
  let H₀ := podCompletedModuleInverseImage l k g
  let Hc := H₀.mapHomologicalComplex (.up ℤ)
  let F₀ := modulePull l X g B
  let Fc := F₀.mapHomologicalComplex (.up ℤ)
  let eX := integralComplex l X R E
  let eY := integralComplex l Y S E
  let cX := constructibleTensorTotal l k X
  let cY := constructibleTensorTotal l k Y
  let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  let tY := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
  let TX := (pullbackTensorCalculus l k X).integralClosed.tensor
  let TY := (pullbackTensorCalculus l k Y).integralClosed.tensor
  let AX := A.closed.tensor
  let CY := C.closed.tensor
  let δH := H₀.mapDerivedCategoryFactors
  let δF := F₀.mapDerivedCategoryFactors
  let v : eY ⋙ Fc ≅ Hc ⋙ eX := by
    simpa only [eX, eY, Fc, Hc, H₀, F₀, integralComplex] using
      cochain_comparison (pbcExtend (coefficientMap l Y S E)) (modulePull l X g B)
        (podCompletedModuleInverseImage l k g) (pbcExtend (coefficientMap l X R E)) V.balance
  obtain ⟨T, hp⟩ := (podAmbientReindexingTensor_existsUnique l k g).exists.choose_spec
  let HP : (integralOperationsGoodComplex l k X).FullSubcategory :=
    ⟨Hc.obj P.obj, completed_inverse_good l k g P.obj P.property⟩
  let HQ : (integralOperationsGoodComplex l k X).FullSubcategory :=
    ⟨Hc.obj Q.obj, completed_inverse_good l k g Q.obj Q.property⟩
  let rX := (pullbackTensorCalculus l k X).integralTensorModel.iso _ _ _ _ _
    HP.property.1 HQ.property.1
  let rY := (pullbackTensorCalculus l k Y).integralTensorModel.iso _ _ _ _ _
    P.property.1 Q.property.1
  let J : cX.obj (HP.obj, HQ.obj) ⟶ Hc.obj (cY.obj (P.obj, Q.obj)) := by
    simpa only [cX, cY, HP, HQ, Hc, H₀, SemilinearSections.totalTensor,
      coefficientTotalTensor, constructibleTensorTotal, constructibleTensorOrdinary] using
      T.chain P.obj Q.obj
  have hchain := cochain_scalar_square l g R S A C B E NX NY V W P.obj Q.obj J
    (by
      simpa only [J, id, k, SemilinearSections.totalTensor, coefficientTotalTensor,
        constructibleTensorTotal, constructibleTensorOrdinary,
        Functor.map₂CochainComplex] using
        integral_chain_sections l k g μ T hp P.obj Q.obj)
  let i := EX.map (rX.hom ≫ TX.map
    (Prod.mkHom (δH.inv.app P.obj) (δH.inv.app Q.obj)))
  let mX := A.models.iso _ _ _ _ _ (NX.kflat HP) (NX.kflat HQ)
  let mF := A.models.iso _ _ _ _ _
    (W.kflat _ (NY.kflat P)) (W.kflat _ (NY.kflat Q))
  have hmu : i ≫ EX.map (μ.inv.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) =
    EX.map (DerivedCategory.Q.map J) ≫
      EX.map (δH.inv.app (cY.obj (P.obj, Q.obj))) ≫
      EX.map (H.map rY.hom) := by
    have ht : (rX.hom ≫ TX.map
        (Prod.mkHom (δH.inv.app P.obj) (δH.inv.app Q.obj))) ≫
        μ.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (H.mapIso rY).inv ≫ (δH.app (cY.obj (P.obj, Q.obj))).hom =
        DerivedCategory.Q.map J := by
      simpa only [μ, podCompletedAmbientTensor, rX, rY, HP, HQ, Hc, H₀,
        TX, δH, H, J, cY, SemilinearSections.tensorModelIso,
        podCompletedDerivedInverseImage, SemilinearSections.totalTensor,
        coefficientTotalTensor, constructibleTensorTotal, constructibleTensorOrdinary,
        Functor.map₂CochainComplex, id, Category.assoc, Functor.mapIso_inv, Iso.app_hom] using
        (T.derived P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2)
    have hh := solve_suffix _ _ (H.mapIso rY)
      (δH.app (cY.obj (P.obj, Q.obj))) _ ht
    simpa only [i, Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_inv] using congrArg EX.map hh
  have hv (Z : CochainComplex (integralTowerModules l k Y) ℤ) :
    V.derived.inv.app (DerivedCategory.Q.obj Z) ≫
        F.map (pbcComplexCounit (coefficientMap l Y S E) Z) ≫
        δF.hom.app (eY.obj Z) =
      EX.map (δH.hom.app Z) ≫ pbcComplexCounit (coefficientMap l X R E) (Hc.obj Z) ≫
        DerivedCategory.Q.map (v.inv.app Z) := by
    have hh := inverse_representative (V.derived.app (DerivedCategory.Q.obj Z))
      (EX.map (δH.hom.app Z) ≫ pbcComplexCounit (coefficientMap l X R E) (Hc.obj Z))
      (F.map (pbcComplexCounit (coefficientMap l Y S E) Z) ≫ δF.hom.app (eY.obj Z))
      (DerivedCategory.Q.mapIso (v.app Z))
      (by
        simpa only [EX, F, δH, δF, H₀, F₀, Hc, eY, integralComplex, v,
          cochain_comparison, id, k, Category.assoc, Functor.mapIso_hom, Iso.app_hom] using
          V.representative Z)
    simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using hh
  let : IsIso ((scalar_counit (coefficientMap l Y S E)).app P.obj) :=
    scalar_counit_iso (coefficientMap l Y S E) P.obj P.property.1
  let : IsIso ((scalar_counit (coefficientMap l Y S E)).app Q.obj) :=
    scalar_counit_iso (coefficientMap l Y S E) Q.obj Q.property.1
  refine scalar_square_pasting
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    Hc Fc eX eY H F EX EY cX cY tX tY TX TY AX CY δH δF
    (scalar_counit (coefficientMap l X R E))
    (scalar_counit (coefficientMap l Y S E)) v V.derived
    NX.balance NY.balance W.cochain μ σX σY W.tensor
    P.obj Q.obj rX rY mX
    (C.models.iso _ _ _ _ _ (NY.kflat P) (NY.kflat Q)) mF J
    ?_ hmu hv ?_ ?_ ?_ ?_
  · simpa only [tensor_component_eq] using hchain
  · exact ambient_scalar_representative l X R A E NX HP HQ
  · exact ambient_scalar_representative l Y S C E NY P Q
  · exact W.representative (eY.obj P.obj) (eY.obj Q.obj) (NY.kflat P) (NY.kflat Q)
  · exact (A.models.comparison.hom.naturality
      (X := (⟨eX.obj HP.obj, NX.kflat HP⟩, ⟨eX.obj HQ.obj, NX.kflat HQ⟩))
      (Y := (⟨Fc.obj (eY.obj P.obj), W.kflat _ (NY.kflat P)⟩,
        ⟨Fc.obj (eY.obj Q.obj), W.kflat _ (NY.kflat Q)⟩))
      (Prod.mkHom (ObjectProperty.homMk (v.inv.app P.obj))
        (ObjectProperty.homMk (v.inv.app Q.obj)))).symm

end CochainSquare

set_option maxHeartbeats 1600000 in
-- Normalize the product-localization endpoints of the whiskered isomorphisms.
/-- Ordinary scalar extension commutes with the normalized tensor reindexing.
There are no completion maps or constructible inputs in this equation.
Source: BS Remark 6.8.15; Stacks 03EL and 07A4.
(blueprint: lem-sf-adic-ordinary-scalar-tensor-reindexing).

Proof: first identify the presentation comparison on good complexes with the
fixed integral tensor model, and substitute this in each scalar representative
equation. The integral tensor comparison's ordinary normalization and summand
equation determine its inverse chain map on homogeneous pure tensors. The scalar
adjunction reduces equality of scalar-extended total-complex maps to the generators
1 tensor (x tensor y). On these generators, NY.balance_sections separates the
factors, the inverse of V.sections at scalar 1 reindexes both sections unchanged,
and W.pure preserves the resulting homogeneous tensor. Applying NX.balance_sections
and tensor functoriality gives the same generator. Sheaf tensor extensionality and
total-summand extensionality prove equality of chain maps in every degree.

For flat-term K-flat representatives P,Q, completed inverse image preserves the
representative class. Compare the inverse derived paths after precomposing with
the mapped integral tensor model and the exact reindexing factors, and postcomposing
with the tensor of mapped K-flat scalar counits and exact factors. The representative
equations of the integral comparison, NX, NY, V, and W, together with naturality of
the cochain scalar counit, exact factors, and native tensor model, reduce the two
paths to the localization of the chain identity. Cancel the invertible pre- and
postcompositions. Faithfulness of restriction along the product good-complex
localization descends equality to arbitrary M,N. Invert the composite isomorphism
identity to obtain the displayed square. No completeness, rationalization,
nonzero-input, or quasi-compactness assumption enters this ordinary calculation. -/
theorem ordinary_scalar_tensor_reindexing
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S C E)
    (V : IntegralReindex l X g B E) (W : ReindexTensor l X g A C B)
    (M N : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := derivedPull l X g B
    let H := podCompletedDerivedInverseImage l k g
    F.map ((finiteAmbientScalarTensor l Y S C E NY).inv.app (M, N)) ≫
        V.derived.hom.app ((pullbackTensorCalculus l k Y).integralClosed.tensor.obj (M, N)) ≫
        EX.map ((podCompletedAmbientTensor l k g).hom.app (M, N)) =
      W.tensor.hom.app (EY.obj M, EY.obj N) ≫
        A.closed.tensor.map (Prod.mkHom (V.derived.hom.app M) (V.derived.hom.app N)) ≫
        (finiteAmbientScalarTensor l X R A E NX).inv.app (H.obj M, H.obj N) := by
  classical
  intros k EX EY F H
  let σX := finiteAmbientScalarTensor l X R A E NX
  let σY := finiteAmbientScalarTensor l Y S C E NY
  let μ := podCompletedAmbientTensor l k g
  let TY := (pullbackTensorCalculus l k Y).integralClosed.tensor
  let L := Functor.isoWhiskerRight μ.symm EX ≪≫
    Functor.isoWhiskerLeft TY V.derived.symm ≪≫
    Functor.isoWhiskerRight σY F ≪≫
    Functor.isoWhiskerLeft (EY.prod EY) W.tensor
  let T := Functor.isoWhiskerLeft (H.prod H) σX ≪≫
    Functor.isoWhiskerRight (NatIso.prod V.derived.symm V.derived.symm) A.closed.tensor
  have he : L.hom = T.hom := by
    have hfaith := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l k Y)).choose_spec.2.2
    apply (hfaith _ inferInstance _ _).injective
    apply NatTrans.ext
    funext PQ
    simpa only [L, T, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
      SheafOfModules.cochainTensorRepresentativeLocalization,
      Functor.prod_obj, Functor.comp_obj, ObjectProperty.ι_obj] using
      inverse_square_good l g R S A C B E NX NY V W PQ.1 PQ.2
  have h := congrArg (fun τ ↦ τ.app (M, N)) he
  have hr := iso_rotate (EX.mapIso (μ.app (M, N)).symm)
    (V.derived.app (TY.obj (M, N))).symm (F.mapIso (σY.app (M, N)))
    (W.tensor.app (EY.obj M, EY.obj N)) (σX.app (H.obj M, H.obj N))
    (A.closed.tensor.mapIso ((V.derived.app M).symm.prod (V.derived.app N).symm))
    (by
      simpa only [L, T, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
        Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.prod_hom,
        Functor.prod_obj, Functor.comp_obj] using h)
  simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.prod_inv, Iso.app_inv, Iso.app_hom] using hr

end WeilConjectures.AdicQbarRealization
