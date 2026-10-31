/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionMiddleMap
public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionLocalFactors
import WeilConjectures.SixFunctors.IntegralProjectionReduction.OpenCoordinates.IntegralOpenAdjunctionReduction
import WeilConjectures.SixFunctors.IntegralProjectionReduction.OpenCoordinates.IntegralOpenPullTensorReduction
import WeilConjectures.SixFunctors.IntegralProjectionReduction.OpenCoordinates.IntegralDatumPullCompositionReduction

/-! # Open tensor coordinates before proper image

Source: prop-sf-pf-coherence.proof.md, compatibility with counits and open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization
open IntegralProjectionReduction ProperCoordinates OpenCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntegralConstructible
  Coordinates.datumTensorReductionIso Coordinates.inputReduction
  Coordinates.tensorReductionIso Coordinates.pullReduction Coordinates.pullValue
  ProperCoordinates.pullComparison ProperCoordinates.tensor OpenCoordinates.extensionComparison
  pullbackTensorSystemComparison pullbackTensorSequenceDerived SheafOfModules.instCategory
  IntegralSystemRealization.Open.adj

section
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {S : SixFunctorPushStage D B}

private def normalizedOpenProjection
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    ((T Q.Z).obj ((S.openExtension Q.i Q.open_i).obj K)).obj ((S.pull Q.p).obj N) ≅
      (S.openExtension Q.i Q.open_i).obj (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) :=
  eqToIso (by rw [A.tensorBar, A.openExtension, A.properPull]; rfl) ≪≫
    (A.stage.openProjection.app K).app N ≪≫
    eqToIso (by rw [A.openExtension, A.tensorX, A.pull]; rfl)

private theorem normalizedOpenProjection_inv
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    (normalizedOpenProjection A K N).inv =
      sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N := by
  have h : HEq (normalizedOpenProjection A K N).inv
      ((A.stage.openProjection.inv.app K).app N) := by
    simp only [normalizedOpenProjection, Iso.trans_inv, eqToIso.inv,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  exact eq_of_heq (h.trans (A.openProjectionNormalization K N))

private theorem open_inverse_transpose
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) (N : B Q.Y) :
    let P := S.openExtension Q.i Q.open_i
    let L := (S.pull Q.p).obj N
    let v := eqToHom (congrArg (fun e ↦ (S.pull e).obj N) Q.factorization) ≫
      (S.pullComposition Q.i Q.p).hom.app N
    sixFunctorOpenProjectionInverse S T Q A.openTensorPullback K N =
      ((S.openAdjunction Q.i Q.open_i).homEquiv _ _).symm
        ((Functor.uncurry.obj (T Q.X)).map
            (Prod.mkHom ((S.openAdjunction Q.i Q.open_i).unit.app K) v) ≫
          (A.openTensorPullback.inv.app (P.obj K)).app L) := by
  dsimp only
  dsimp [sixFunctorOpenProjectionInverse]
  rw [← Adjunction.homEquiv_naturality_left_symm]
  congr 1
  simp [NatTrans.naturality_assoc, Category.assoc, eqToHom_app]

end

private theorem projection_reindex_transpose
    {CX CY : Type*} [Category CX] [Category CY] {F : CX ⥤ CY} {G : CY ⥤ CX}
    (a : F ⊣ G) (TC : CX × CX ⥤ CX) (TD : CY × CY ⥤ CY)
    (ψ : TD ⋙ G ≅ G.prod G ⋙ TC) (M : CX) (N : CY) {P : CX}
    (s : P ≅ G.obj N) (φ : TD.obj (F.obj M, N) ≅ F.obj (TC.obj (M, G.obj N)))
    (hφ : (a.homEquiv _ _) φ.inv =
      TC.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ ψ.inv.app (F.obj M, N)) :
    (φ ≪≫ F.mapIso (TC.mapIso (Iso.prod (Iso.refl M) s.symm))).inv =
      (a.homEquiv _ _).symm
        (TC.map (Prod.mkHom (a.unit.app M) s.hom) ≫ ψ.inv.app (F.obj M, N)) := by
  apply (a.homEquiv _ _).injective
  simp only [Iso.trans_inv, Functor.mapIso_inv,
    Iso.prod_inv, Iso.refl_inv, Iso.symm_inv]
  rw [Adjunction.homEquiv_naturality_left, hφ, ← TC.map_comp_assoc]
  simp

private theorem and_rec_eq {P Q : Prop} {α : Sort*} (h : P ∧ Q) (f : P → Q → α) :
    And.rec f h = f h.1 h.2 := by
  cases h
  rfl

private theorem transpose_preserved
    {CX CY CX' CY' : Type*}
    [Category* CX] [Category* CY] [Category* CX'] [Category* CY']
    {L : CX ⥤ CY} {R : CY ⥤ CX} {L' : CX' ⥤ CY'} {R' : CY' ⥤ CX'}
    {a : L ⊣ R} {a' : L' ⊣ R'} {c : CX ⥤ CX'} {d : CY ⥤ CY'}
    (e : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      a a' c d)
    {X : CX} {Y : CY} {X' : CX'} {Y' : CY'}
    (x : c.obj X ≅ X') (y : d.obj Y ≅ Y')
    (f : X ⟶ R.obj Y) (f' : X' ⟶ R'.obj Y')
    (h : c.map f ≫ e.right.hom.app Y ≫ R'.map y.hom = x.hom ≫ f') :
    d.map ((a.homEquiv _ _).symm f) ≫ y.hom =
      e.left.hom.app X ≫ L'.map x.hom ≫ (a'.homEquiv _ _).symm f' := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hc : d.map (a.counit.app Y) =
      e.left.hom.app (R.obj Y) ≫ L'.map (e.right.hom.app Y) ≫
        a'.counit.app (d.obj Y) := by
    rw [e.counit]
    simp
  rw [hc]
  simp only [Category.assoc]
  have hn := e.left.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn' := a'.counit.naturality y.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn'
  rw [← hn']
  rw [← L'.map_comp_assoc, ← L'.map_comp_assoc]
  simp only [Category.assoc]
  rw [h, L'.map_comp]
  simp only [Category.assoc]

private theorem inverse_square
    {CX : Type*} [Category* CX] {A B A' B' : CX}
    (a : A ≅ B) (b : A' ≅ B') (c : A ≅ A') (d : B ≅ B')
    (h : a.inv ≫ c.hom = d.hom ≫ b.inv) :
    a.hom ≫ d.hom = c.hom ≫ b.hom := by
  apply (cancel_epi a.inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem transport_tensor_source
    {CX CY CZ CT : Type*} [Category CX] [Category CY] [Category CZ] [Category CT]
    (R : CZ ⥤ CT) (T₀ T : CZ ⥤ CZ ⥤ CZ) (P₀ P : CX ⥤ CZ) (Q₀ Q : CY ⥤ CZ)
    (hT : T₀ = T) (hP : P₀ = P) (hQ : Q₀ = Q) (U : CT × CT ⥤ CT)
    (μ : ∀ M N, R.obj ((T.obj M).obj N) ≅ U.obj (R.obj M, R.obj N))
    (K : CX) (L : CY) {M N : CT}
    (a : R.obj (P.obj K) ⟶ M) (b : R.obj (Q.obj L) ⟶ N) :
    R.map (eqToHom (show (T₀.obj (P₀.obj K)).obj (Q₀.obj L) =
        (T.obj (P₀.obj K)).obj (Q₀.obj L) by rw [hT])) ≫
      (μ (P₀.obj K) (Q₀.obj L)).hom ≫
      U.map (Prod.mkHom
        (R.map (eqToHom (Functor.congr_obj hP K)) ≫ a)
        (R.map (eqToHom (Functor.congr_obj hQ L)) ≫ b)) =
    R.map (eqToHom (show (T₀.obj (P₀.obj K)).obj (Q₀.obj L) =
        (T.obj (P.obj K)).obj (Q.obj L) by rw [hT, hP, hQ])) ≫
      (μ (P.obj K) (Q.obj L)).hom ≫ U.map (Prod.mkHom a b) := by
  subst T₀ P₀ Q₀
  simp

private theorem pull_factorization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (f : X ⟶ Y) (h : f = i ≫ p)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (reduce (C := C) (E := E) X).map
        (eqToHom (congrArg (fun e ↦ (S.higher.integral.pull e).obj L) h) ≫
          (S.higher.integral.pullComposition i p).hom.app L) ≫
        (pullComparison S.higher hl o z i).hom.app ((S.higher.integral.pull p).obj L) ≫
        (pull C.l E i.hom.left).map ((pullComparison S.higher hl o z p).hom.app L) =
      (pullComparison S.higher hl o z f).hom.app L ≫
        eqToHom (congrArg (fun e : X ⟶ Y ↦
          (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Y).obj L)) h) ≫
        (z.compositors.pullComp i.hom.left p.hom.left).hom.app
          ((reduce (C := C) (E := E) Y).obj L) := by
  subst f
  simpa only [eqToHom_refl, Category.id_comp] using
    integralDatumPullCompositionReduction C E n hn S hl o z i p L

private theorem tensor_chain
    {CX CY : Type*} [Category CX] [Category CY] (T : CX ⥤ CY)
    {A₀ A₁ A₂ A₃ A₄ : CX} {U V W : CY}
    (t : U ⟶ T.obj A₀) (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (d : A₀ ⟶ A₄) (e : A₄ ⟶ A₃)
    (p : T.obj A₂ ⟶ V) (q : V ⟶ W) (r : T.obj A₃ ⟶ W)
    (hm : a ≫ b ≫ c = d ≫ e) (hn : T.map c ≫ r = p ≫ q) :
    t ≫ T.map a ≫ T.map b ≫ p ≫ q = t ≫ T.map d ≫ T.map e ≫ r := by
  calc
    _ = t ≫ T.map a ≫ T.map b ≫ T.map c ≫ r := by rw [hn]
    _ = _ := by
      rw [← T.map_comp_assoc, ← T.map_comp_assoc]
      simp only [Category.assoc]
      rw [hm, T.map_comp]
      simp only [Category.assoc]

private theorem normalized_adjunct_square
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    (Q : SixFunctorCompactifiedSquare D) [QuasiCompact Q.i.hom.left]
    (K : sfIntegralConstructibleCategory C.l E Q.X.obj.left)
    (N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left) :
    letI := Q.open_i
    let H := S.higher
    let A := H.integralExchange Q
    let P := H.integral.openExtension Q.i Q.open_i
    let F := Operations.shriek C.l E o Q.i.hom.left
    let TX := Functor.uncurry.obj (H.integralTensor Q.X)
    let TC := (calculus C.l E Q.X.obj.left).systemClosed.tensor
    let TD := (calculus C.l E Q.Z.obj.left).systemClosed.tensor
    let ρ := extensionComparison S hl o z Q.i Q.open_i
    let ξ := pullComparison H hl o z Q.p
    let L := (H.integral.pull Q.p).obj N
    let L' := (pull C.l E Q.p.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)
    let v := eqToHom (congrArg (fun e ↦ (H.integral.pull e).obj N) Q.factorization) ≫
      (H.integral.pullComposition Q.i Q.p).hom.app N
    let vs := eqToIso (congrArg (fun e : Q.X ⟶ Q.Y ↦
        (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)) Q.factorization) ≪≫
      (z.compositors.pullComp Q.i.hom.left Q.p.hom.left).app ((reduce (C := C) (E := E) Q.Y).obj N)
    let v' := vs.hom
    let m := Prod.mkHom ((H.integral.openAdjunction Q.i Q.open_i).unit.app K) v
    let m' := Prod.mkHom
      ((o.extension Q.i.hom.left).adj.unit.app ((reduce (C := C) (E := E) Q.X).obj K)) v'
    let x := (Coordinates.inputReduction D C E H hl o z Q.f K N).symm
    let y := (Coordinates.datumTensorReduction D C E H hl Q.Z (P.obj K) L) ≪≫
      TD.mapIso (Iso.prod (ρ.app K) (ξ.app N))
    let τ := TX.map m ≫ (A.openTensorPullback.inv.app (P.obj K)).app L
    let τ' := TC.map m' ≫
      (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
        (F.obj ((reduce (C := C) (E := E) Q.X).obj K), L')
    (reduce (C := C) (E := E) Q.Z).map
        (((H.integral.openAdjunction Q.i Q.open_i).homEquiv _ _).symm τ) ≫ y.hom =
      ρ.hom.app (((H.integralTensor Q.X).obj K).obj ((H.integral.pull Q.f).obj N)) ≫
        F.map x.hom ≫ ((o.extension Q.i.hom.left).adj.homEquiv _ _).symm τ' := by
  let := Q.open_i
  let H := S.higher
  let A := H.integralExchange Q
  let P := H.integral.openExtension Q.i Q.open_i
  let F := Operations.shriek C.l E o Q.i.hom.left
  let G := pull C.l E Q.i.hom.left
  let TX := Functor.uncurry.obj (H.integralTensor Q.X)
  let TC := (calculus C.l E Q.X.obj.left).systemClosed.tensor
  let TD := (calculus C.l E Q.Z.obj.left).systemClosed.tensor
  let ρ := extensionComparison S hl o z Q.i Q.open_i
  let χ := pullComparison H hl o z Q.i
  let ξ := pullComparison H hl o z Q.p
  let ζ := pullComparison H hl o z Q.f
  let tX := (Coordinates.datumTensorReductionIso D C E H hl Q.X).hom
  let L := (H.integral.pull Q.p).obj N
  let L' := (pull C.l E Q.p.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)
  let v := eqToHom (congrArg (fun e ↦ (H.integral.pull e).obj N) Q.factorization) ≫
    (H.integral.pullComposition Q.i Q.p).hom.app N
  let vs := eqToIso (congrArg (fun e : Q.X ⟶ Q.Y ↦
      (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)) Q.factorization) ≪≫
    (z.compositors.pullComp Q.i.hom.left Q.p.hom.left).app ((reduce (C := C) (E := E) Q.Y).obj N)
  let v' := vs.hom
  let m := Prod.mkHom ((H.integral.openAdjunction Q.i Q.open_i).unit.app K) v
  let m' := Prod.mkHom
    ((o.extension Q.i.hom.left).adj.unit.app ((reduce (C := C) (E := E) Q.X).obj K)) v'
  let q := Prod.mkHom (ρ.hom.app K) (ξ.hom.app N)
  let x := (Coordinates.inputReduction D C E H hl o z Q.f K N).symm
  let y := (Coordinates.datumTensorReduction D C E H hl Q.Z (P.obj K) L) ≪≫
    TD.mapIso (Iso.prod (ρ.app K) (ξ.app N))
  let β := (z.openComparisons.projection Q.i.hom.left).app
      ((reduce (C := C) (E := E) Q.X).obj K, L') ≪≫
    F.mapIso (TC.mapIso (Iso.prod (Iso.refl _) vs.symm))
  let τ := TX.map m ≫ (A.openTensorPullback.inv.app (P.obj K)).app L
  let τ' := TC.map m' ≫
    (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
      (F.obj ((reduce (C := C) (E := E) Q.X).obj K), L')
  have hAdj := integralOpenAdjunctionReduction C E n hn S hl o z Q.i Q.open_i
  have hu := hAdj.1
  have hc := hAdj.2
  let e : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison
      (H.integral.openAdjunction Q.i Q.open_i) (o.extension Q.i.hom.left).adj
      (reduce (C := C) (E := E) Q.X) (reduce (C := C) (E := E) Q.Z) :=
    { left := ρ
      right := χ
      unit := hu
      counit := fun M ↦ by
        apply (cancel_epi (ρ.hom.app ((H.integral.pull Q.i).obj M))).1
        simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hc M }
  have hv : (reduce (C := C) (E := E) Q.X).map v ≫ χ.hom.app L ≫ G.map (ξ.hom.app N) =
      ζ.hom.app N ≫ v' := by
    simpa only [v, v', vs, Iso.trans_hom, Iso.app_hom, eqToIso.hom] using
      pull_factorization S hl o z Q.i Q.p Q.f Q.factorization N
  have hm : Prod.mkHom ((reduce (C := C) (E := E) Q.X).map m.1)
        ((reduce (C := C) (E := E) Q.X).map m.2) ≫
        Prod.mkHom (χ.hom.app (P.obj K)) (χ.hom.app L) ≫
        Prod.mkHom (G.map q.1) (G.map q.2) =
      Prod.mkHom (𝟙 ((reduce (C := C) (E := E) Q.X).obj K)) (ζ.hom.app N) ≫ m' := by
    apply Prod.hom_ext
    · simpa only [prod_comp_fst, Category.id_comp, Category.assoc] using hu K
    · simpa only [prod_comp_snd, Category.assoc] using hv
  have ht : (reduce (C := C) (E := E) Q.X).map τ ≫
      χ.hom.app (((H.integralTensor Q.Z).obj (P.obj K)).obj L) ≫
      G.map y.hom = x.hom ≫ τ' := by
    have hnat := (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.naturality q
    have htn := tX.naturality m
    change (reduce (C := C) (E := E) Q.X).map (TX.map m) ≫
        tX.app ((H.integral.pull Q.i).obj (P.obj K), (H.integral.pull Q.i).obj L) =
      tX.app (K, (H.integral.pull Q.f).obj N) ≫
        TC.map (Prod.mkHom ((reduce (C := C) (E := E) Q.X).map m.1)
          ((reduce (C := C) (E := E) Q.X).map m.2)) at htn
    have hnat' : TC.map (Prod.mkHom (G.map q.1) (G.map q.2)) ≫
        (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
          (F.obj ((reduce (C := C) (E := E) Q.X).obj K), L') =
      (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
          ((reduce (C := C) (E := E) Q.Z).obj (P.obj K),
            (reduce (C := C) (E := E) Q.Z).obj L) ≫ G.map (TD.map q) := by
      simpa only [TC, TD, G, F, P, L, L', H, calculus, pull,
        Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] using hnat
    simp only [τ, y, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.prod_hom,
      Functor.map_comp, Category.assoc]
    have hμ := integralOpenPullTensorReduction C E H hl o z Q (P.obj K) L
    simp only [tensor, Coordinates.datumTensorReduction, Iso.app_hom] at hμ
    simp only [Functor.comp_map, ObjectProperty.ι_map] at hμ
    simp only [reduce, Functor.comp_map, ObjectProperty.ι_map] at htn ⊢
    rw [reassoc_of% hμ, reassoc_of% htn]
    have hchain := tensor_chain TC (tX.app (K, (H.integral.pull Q.f).obj N))
      (Prod.mkHom ((reduce (C := C) (E := E) Q.X).map m.1)
        ((reduce (C := C) (E := E) Q.X).map m.2))
      (Prod.mkHom (χ.hom.app (P.obj K)) (χ.hom.app L))
      (Prod.mkHom (G.map q.1) (G.map q.2))
      (Prod.mkHom (𝟙 _) (ζ.hom.app N)) m'
      ((pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
        ((reduce (C := C) (E := E) Q.Z).obj (P.obj K),
          (reduce (C := C) (E := E) Q.Z).obj L))
      (G.map (TD.map q))
      ((pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
        (F.obj ((reduce (C := C) (E := E) Q.X).obj K), L')) hm hnat'
    simpa only [reduce, Functor.comp_map, ObjectProperty.ι_map,
      x, Coordinates.inputReduction, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_inv, Iso.prod_inv, Iso.refl_inv, Iso.symm_inv, Iso.app_hom,
      Iso.app_inv, tX, tensor, Functor.uncurry_obj_map, Functor.uncurry_map_app,
      τ', m', G, χ, ζ, q, TC, Functor.mapIso_hom, Functor.comp_obj,
      ObjectProperty.ι_obj, Category.assoc, pullComparison_hom_app, Functor.map_comp]
      using hchain
  have he := transpose_preserved e x y τ τ' ht
  simpa only [e, H, A, P, F, TX, TC, TD, ρ, ξ, L, L', v, vs, v', m, m', x, y, τ, τ',
    Functor.uncurry_obj_obj, Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    Operations.shriek, calculus, Iso.app_hom] using he

private theorem normalized_open_square
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    (Q : SixFunctorCompactifiedSquare D) [QuasiCompact Q.i.hom.left]
    (K : sfIntegralConstructibleCategory C.l E Q.X.obj.left)
    (N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left) :
    letI := Q.open_i
    let H := S.higher
    let A := H.integralExchange Q
    let W := ((H.integralTensor Q.X).obj K).obj ((H.integral.pull Q.f).obj N)
    let v := eqToIso (congrArg (fun e : Q.X ⟶ Q.Y ↦
        (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)) Q.factorization) ≪≫
      (z.compositors.pullComp Q.i.hom.left Q.p.hom.left).app ((reduce (C := C) (E := E) Q.Y).obj N)
    let β := (z.openComparisons.projection Q.i.hom.left).app
        ((reduce (C := C) (E := E) Q.X).obj K,
          (pull C.l E Q.p.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)) ≪≫
      (Operations.shriek C.l E o Q.i.hom.left).mapIso
        ((calculus C.l E Q.X.obj.left).systemClosed.tensor.mapIso
          (Iso.prod (Iso.refl _) v.symm))
    (reduce (C := C) (E := E) Q.Z).map (normalizedOpenProjection A K N).hom ≫
        (extensionComparison S hl o z Q.i Q.open_i).hom.app W ≫
        (Operations.shriek C.l E o Q.i.hom.left).map
          (Coordinates.inputReduction D C E H hl o z Q.f K N).inv =
      ((tensor H hl Q.Z).app ((H.integral.openExtension Q.i Q.open_i).obj K)).app
          ((H.integral.pull Q.p).obj N) ≫
        (calculus C.l E Q.Z.obj.left).systemClosed.tensor.map
          (Prod.mkHom ((extensionComparison S hl o z Q.i Q.open_i).hom.app K)
            ((pullComparison H hl o z Q.p).hom.app N)) ≫ β.hom := by
  let := Q.open_i
  let H := S.higher
  let A := H.integralExchange Q
  let P := H.integral.openExtension Q.i Q.open_i
  let F := Operations.shriek C.l E o Q.i.hom.left
  let G := pull C.l E Q.i.hom.left
  let TX := Functor.uncurry.obj (H.integralTensor Q.X)
  let TC := (calculus C.l E Q.X.obj.left).systemClosed.tensor
  let TD := (calculus C.l E Q.Z.obj.left).systemClosed.tensor
  let ρ := extensionComparison S hl o z Q.i Q.open_i
  let χ := pullComparison H hl o z Q.i
  let ξ := pullComparison H hl o z Q.p
  let ζ := pullComparison H hl o z Q.f
  let tX := (Coordinates.datumTensorReductionIso D C E H hl Q.X).hom
  let L := (H.integral.pull Q.p).obj N
  let L' := (pull C.l E Q.p.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)
  let v := eqToHom (congrArg (fun e ↦ (H.integral.pull e).obj N) Q.factorization) ≫
    (H.integral.pullComposition Q.i Q.p).hom.app N
  let vs := eqToIso (congrArg (fun e : Q.X ⟶ Q.Y ↦
      (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj N)) Q.factorization) ≪≫
    (z.compositors.pullComp Q.i.hom.left Q.p.hom.left).app ((reduce (C := C) (E := E) Q.Y).obj N)
  let v' := vs.hom
  let m := Prod.mkHom ((H.integral.openAdjunction Q.i Q.open_i).unit.app K) v
  let m' := Prod.mkHom
    ((o.extension Q.i.hom.left).adj.unit.app ((reduce (C := C) (E := E) Q.X).obj K)) v'
  let q := Prod.mkHom (ρ.hom.app K) (ξ.hom.app N)
  let x := (Coordinates.inputReduction D C E H hl o z Q.f K N).symm
  let y := (Coordinates.datumTensorReduction D C E H hl Q.Z (P.obj K) L) ≪≫
    TD.mapIso (Iso.prod (ρ.app K) (ξ.app N))
  let β := (z.openComparisons.projection Q.i.hom.left).app
      ((reduce (C := C) (E := E) Q.X).obj K, L') ≪≫
    F.mapIso (TC.mapIso (Iso.prod (Iso.refl _) vs.symm))
  let τ := TX.map m ≫ (A.openTensorPullback.inv.app (P.obj K)).app L
  let τ' := TC.map m' ≫
    (pullbackTensorSystemComparison C.l E Q.i.hom.left).inv.app
      (F.obj ((reduce (C := C) (E := E) Q.X).obj K), L')
  have he := normalized_adjunct_square S hl o z Q K N
  have hτ : sixFunctorOpenProjectionInverse H.integral H.integralTensor Q
      A.openTensorPullback K N =
      ((H.integral.openAdjunction Q.i Q.open_i).homEquiv _ _).symm τ := by
    simpa only [τ, TX, m, v, P, L] using open_inverse_transpose A K N
  have hτ' : β.inv = ((o.extension Q.i.hom.left).adj.homEquiv _ _).symm τ' := by
    simpa only [β, τ', m', v', Iso.app_hom, F, TD, TC, openTensorLeft,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Operations.shriek] using
      projection_reindex_transpose (o.extension Q.i.hom.left).adj TC TD
        (pullbackTensorSystemComparison C.l E Q.i.hom.left)
        ((reduce (C := C) (E := E) Q.X).obj K) L' vs
        ((z.openComparisons.projection Q.i.hom.left).app
          ((reduce (C := C) (E := E) Q.X).obj K, L'))
        (z.openComparisons.projection_transpose Q.i.hom.left
          ((reduce (C := C) (E := E) Q.X).obj K) L')
  have hinv : (reduce (C := C) (E := E) Q.Z).map (normalizedOpenProjection A K N).inv ≫ y.hom =
      ρ.hom.app (((H.integralTensor Q.X).obj K).obj ((H.integral.pull Q.f).obj N)) ≫
        F.map x.hom ≫ β.inv := by
    rw [normalizedOpenProjection_inv, hτ, hτ']
    simpa only [x, y, H, A, P, F, TX, TC, TD, ρ, ξ, L, L', v, vs, v', m, m', τ, τ',
      Operations.shriek, ObjectProperty.ι_obj, calculus, Functor.uncurry_obj_obj,
      Functor.id_obj, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.app_hom, Category.assoc] using he
  simpa only [y, x, β, H, A, P, F, L, L', ρ, ξ, vs, TD, TC, tensor,
    Coordinates.datumTensorReduction, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Iso.symm_hom,
    Functor.uncurry_obj_obj, Category.assoc] using
    inverse_square ((reduce (C := C) (E := E) Q.Z).mapIso (normalizedOpenProjection A K N)) β y
      (ρ.app (((H.integralTensor Q.X).obj K).obj ((H.integral.pull Q.f).obj N)) ≪≫
        F.mapIso x) (by
          simpa only [Functor.mapIso_inv, Iso.trans_hom, Functor.mapIso_hom,
            Iso.app_hom, Category.assoc] using hinv)

private theorem identity_f {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).f = f := rfl

private theorem identity_i_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).i.hom.left = c.i := rfl

private theorem identity_p_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).p.hom.left = c.g := rfl

private theorem identity_Z_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).Z.obj.left = c.Z := rfl

private theorem identity_X {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).X = X := rfl

private theorem identity_Y {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).Y = Y := rfl

/-- The open tensor/compositor square before applying any proper direct image.
Neither compact support nor its comparison occurs in this equation.

Source: prop-sf-pf-coherence.proof.md, the j_! factor; proof step 1 and the
pullback-compositor part of step 2 of lem-sf-integral-projection-open-factor-reduction.
(blueprint: lem-sf-integral-projection-open-tensor-coordinates).

Proof: transpose the inverse open projection under the actual open adjunction.
openProjectionNormalization gives the open unit tensored with identity followed
by inverse tensor pullback. The integralOpenTensorPullbackNormalization equation
identifies that pullback/tensor comparison with canonicalIntegralPullbackTensor.
Choose simultaneous flat-term K-flat quotient representatives of K and L. Their
quotient augmentations identify tensorReductionIso and pullReduction with tensor
and pullback of the actual reconstruction counit. The open-unit scalar mate is
exactly realizationModel.openReduction. Its inverse exists by
openReconstructionEffectivity; the ordinary openRealization is pinned by the
openProjection equation of integralNormalization. Paste the unit, tensor and
pullback coefficient squares of generatorReductionCoherence, retaining their
strict transitions. Invert the open-unit square and cancel the adjacent counits
using the triangle identities. This yields the local open tensor square.
Next paste the pullback-composition square for i followed by g, normalized by
integralNormalization.pullProjection and its coefficient comparison's
pullComposition equation. The compactification equation identifies i followed
by g with f. Tensor with identity on reduction K, and compose with inverse
inputReduction. Naturality cancels the intermediate pullback and tensor
comparisons, giving the displayed equality. Residue Tor for K and the finite-Tor
hypothesis for L provide common bounds for all quotient models; quasi-compact
open extension preserves completeness. Empty opens, identity opens, and zero
inputs use these same unit and quotient equations. No equality is inferred from
faithfulness of finite derived evaluation. -/
theorem integralProjectionOpenTensorCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj) :
    let A := S.higher.integralExchange (identitySquare f c)
    let W := ((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L)
    let q := ProjectionFactors.openMap A K L
    (ProjectionFactors.barTensorReduction D C E n hn S hl f c
        (A.stage.openExtension.obj K) (A.stage.properPull.obj L)).hom ≫
      (calculus C.l E c.Z).systemClosed.tensor.map
        (Prod.mkHom (ProjectionFactors.openReduction D C E n hn S hl o z f c K)
          (ProjectionFactors.properPullReduction D C E n hn S hl o z f c L).hom) ≫
      (z.openComparisons.projection c.i).hom.app
        ((calculus C.l E X.obj.left).reduction.obj K.obj,
          (pull C.l E c.g).obj ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≫
      (Operations.shriek C.l E o c.i).map
        ((calculus C.l E X.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _)
            ((z.compositors.pullComp c.i c.g).inv.app
                ((calculus C.l E Y.obj.left).reduction.obj L.obj) ≫
              eqToHom (congrArg (fun g : X.obj.left ⟶ Y.obj.left ↦
                (pull C.l E g).obj
                  ((calculus C.l E Y.obj.left).reduction.obj L.obj)) c.comm.symm)))) =
      (calculus C.l E c.Z).reduction.map q.hom ≫
        ProjectionFactors.openReduction D C E n hn S hl o z f c W ≫
        (Operations.shriek C.l E o c.i).map
          (Coordinates.inputReduction D C E S.higher hl o z f K L).inv := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have _ := hL
  let Q := identitySquare f c
  let : QuasiCompact Q.i.hom.left := by
    change QuasiCompact c.i
    infer_instance
  let A := S.higher.integralExchange Q
  let e : ((A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
      (A.stage.properPull.obj L)) =
      (((S.higher.integralTensor Q.Z).obj
        ((S.higher.integral.openExtension Q.i Q.open_i).obj K)).obj
          ((S.higher.integral.pull Q.p).obj L)) := by
    rw [A.tensorBar, A.openExtension, A.properPull]
  have ha :
      (ProjectionFactors.barTensorReduction D C E n hn S hl f c
          (A.stage.openExtension.obj K) (A.stage.properPull.obj L)).hom ≫
        (calculus C.l E c.Z).systemClosed.tensor.map
          (Prod.mkHom (ProjectionFactors.openReduction D C E n hn S hl o z f c K)
            (ProjectionFactors.properPullReduction D C E n hn S hl o z f c L).hom) =
      (reduce (C := C) (E := E) Q.Z).map (eqToHom e) ≫
        ((tensor S.higher hl Q.Z).app
          ((S.higher.integral.openExtension Q.i Q.open_i).obj K)).app
            ((S.higher.integral.pull Q.p).obj L) ≫
        (calculus C.l E c.Z).systemClosed.tensor.map
          (Prod.mkHom ((extensionComparison S hl o z Q.i Q.open_i).hom.app K)
            ((pullComparison S.higher hl o z Q.p).hom.app L)) := by
    have hs := transport_tensor_source (reduce (C := C) (E := E) Q.Z)
      A.stage.tensorBar (S.higher.integralTensor Q.Z)
      A.stage.openExtension (S.higher.integral.openExtension Q.i Q.open_i)
      A.stage.properPull (S.higher.integral.pull Q.p)
      A.tensorBar A.openExtension A.properPull
      (calculus C.l E c.Z).systemClosed.tensor
      (Coordinates.datumTensorReduction D C E S.higher hl Q.Z) K L
      ((extensionComparison S hl o z Q.i Q.open_i).hom.app K)
      ((pullComparison S.higher hl o z Q.p).hom.app L)
    simpa only [ProjectionFactors.barTensorReduction, ProjectionFactors.openReduction, and_rec_eq,
      ProjectionFactors.properPullReduction, extensionComparison_hom_app,
      pullComparison_hom_app, tensor, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      eqToIso.hom, Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.eqToHom_hom, eqToHom_map,
      reduce, Functor.comp_obj, ObjectProperty.ι_obj, Q, A, identity_i_left, identity_p_left,
      identity_Z_left, identity_X, identity_Y,
      Category.assoc] using hs
  have h := congrArg (fun t ↦ (reduce (C := C) (E := E) Q.Z).map (eqToHom e) ≫ t)
    (normalized_open_square S hl o z Q K L).symm
  let := Q.open_i
  let vs := eqToIso (congrArg (fun e : Q.X ⟶ Q.Y ↦
      (pull C.l E e.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj L)) Q.factorization) ≪≫
    (z.compositors.pullComp Q.i.hom.left Q.p.hom.left).app
      ((reduce (C := C) (E := E) Q.Y).obj L)
  let β := (z.openComparisons.projection Q.i.hom.left).app
      ((reduce (C := C) (E := E) Q.X).obj K,
        (pull C.l E Q.p.hom.left).obj ((reduce (C := C) (E := E) Q.Y).obj L)) ≪≫
    (Operations.shriek C.l E o Q.i.hom.left).mapIso
      ((calculus C.l E Q.X.obj.left).systemClosed.tensor.mapIso
        (Iso.prod (Iso.refl _) vs.symm))
  have hpre := congrArg (fun t ↦ t ≫ β.hom) ha
  simp only [Category.assoc] at h hpre
  have h' := hpre.trans h
  simpa only [ProjectionFactors.barTensorReduction, ProjectionFactors.properPullReduction,
    ProjectionFactors.openReduction, and_rec_eq, ProjectionFactors.openMap,
    normalizedOpenProjection,
    extensionComparison_hom_app, pullComparison_hom_app, tensor,
    Coordinates.datumTensorReduction, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, Iso.prod_hom, Iso.refl_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.symm_inv, Functor.map_comp,
    NatTrans.comp_app, Functor.uncurry_obj_map, eqToIso.hom, eqToIso.inv,
    eqToHom_app, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.eqToHom_hom,
    ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
    reduce, Functor.comp_obj, ObjectProperty.ι_obj, Q, A, identity_f,
    identity_i_left, identity_p_left, identity_Z_left, identity_X, identity_Y,
    β, vs] using h'

end WeilConjectures.FixProjectionCompactification
