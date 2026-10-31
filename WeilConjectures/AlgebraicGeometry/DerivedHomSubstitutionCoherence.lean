/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Derived internal-Hom substitution coherence

Source: current blueprint, sec-six-functors/sk-thm-sf-verdier-exchange,
proof Steps 2--3; Stacks Tags 0A8X, 08JA and 08J9
(blueprint: lem-sf-derived-hom-substitution-coherence).
The maps below use the actual closed-domain Hom, evaluation and ordinary direct image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u a b d e a' b' d' e' c v r w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.DerivedHomSubstitution

section Maps
variable {B : Type a} [Category.{b} B] {D : Type d} [Category.{e} D]
  {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}

/-- Restrict the recorded Hom to its finite-Tor inputs, retaining its ambient output.
Source: blueprint proof Step 2 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def hom (A : SixFunctorClosedDomain P Q H) :
    P.FullSubcategoryᵒᵖ × P.FullSubcategory ⥤ B :=
  sixFunctorDomainHom P Q H A.homPermitted A.homDomain ⋙ P.ι

/-- The contravariant functor J_U = Rf_* RHom(-,U).
Source: blueprint proof Step 2 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def functor (A : SixFunctorClosedDomain P Q H) (R : B ⥤ D) (U : P.FullSubcategory) :
    P.FullSubcategoryᵒᵖ ⥤ D :=
  (Functor.curry.obj (hom A)).flip.obj U ⋙ R

/-- Substitution by c is the mapped Hom natural isomorphism, including its inverse.
Source: blueprint proof Step 2 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def substitution (A : SixFunctorClosedDomain P Q H) (R : B ⥤ D)
    {U V : P.FullSubcategory} (c : U ≅ V) : functor A R U ≅ functor A R V :=
  Functor.isoWhiskerRight ((Functor.curry.obj (hom A)).flip.mapIso c) R

variable {B' : Type a'} [Category.{b'} B'] {D' : Type d'} [Category.{e'} D']
  {P' : ObjectProperty B'} {Q' : ObjectProperty (B'ᵒᵖ × B')}
  {H' : Q'.FullSubcategory ⥤ B'}
  {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
  {T : B ⥤ B'}

/-- The internal-Hom comparison is the transpose of the image of evaluation.
Source: Stacks 08J9, blueprint proof Step 3
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def homComparison (CC : SixFunctorClosedChange A A' T) (M U : P.FullSubcategory) :
    T.obj ((hom A).obj (op M, U)) ⟶
      (hom A').obj
        (op ((sixFunctorDomainChange P P' T CC.domain).obj M),
          (sixFunctorDomainChange P P' T CC.domain).obj U) :=
  P'.ι.map (A'.closed.transpose _ _ _
    (CC.comparison.tensor.inv.app
        ((sixFunctorDomainHom P Q H A.homPermitted A.homDomain).obj (op M, U), M) ≫
      (sixFunctorDomainChange P P' T CC.domain).map (A.closed.evaluation M U)))

/-- The comparison sigma is the ordinary direct-image mate followed by h and u.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def sigma (CC : SixFunctorClosedChange A A' T) (R : B ⥤ D) (R' : B' ⥤ D')
    (TY : D ⥤ D') (γ : R ⋙ TY ⟶ T ⋙ R') (M U : P.FullSubcategory)
    {U' : P'.FullSubcategory}
    (i : (sixFunctorDomainChange P P' T CC.domain).obj U ≅ U') :
    TY.obj ((functor A R U).obj (op M)) ⟶
      (functor A' R' U').obj
        (op ((sixFunctorDomainChange P P' T CC.domain).obj M)) :=
  γ.app ((hom A).obj (op M, U)) ≫ R'.map
    (homComparison CC M U ≫ (hom A').map (Prod.mkHom (𝟙 _) i.hom))

/-- The coefficient substitution square, with no invertibility assertion about h.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def CoefficientSquare (CC : SixFunctorClosedChange A A' T)
    (R : B ⥤ D) (R' : B' ⥤ D') (TY : D ⥤ D') (γ : R ⋙ TY ⟶ T ⋙ R') : Prop :=
  ∀ (M U V : P.FullSubcategory) (c : U ≅ V) (U' V' : P'.FullSubcategory)
    (i : (sixFunctorDomainChange P P' T CC.domain).obj U ≅ U')
    (j : (sixFunctorDomainChange P P' T CC.domain).obj V ≅ V') (c' : U' ≅ V'),
    T.map c.hom.hom ≫ j.hom.hom = i.hom.hom ≫ c'.hom.hom →
    TY.map ((substitution A R c).hom.app (op M)) ≫ sigma CC R R' TY γ M V j =
      sigma CC R R' TY γ M U i ≫ (substitution A' R' c').hom.app
        (op ((sixFunctorDomainChange P P' T CC.domain).obj M))

/-- The substitution square for every allowed evaluation-defined coefficient comparison,
including a supplied realization. Source: blueprint proof Step 3 and Stacks 08J9
(blueprint: lem-sf-derived-hom-substitution-coherence).

Proof: uncurry h_V T(H(1,c)) and H'(1,T(c)) h_U. Naturality of the tensor
comparison and of evaluation identifies both with T(c) T(evaluation) times the
tensor comparison. Injectivity of transposition identifies the original arrows.
Postcompose by H'(1,v) and substitute v T(c) = c' u. Apply R' and paste with
naturality of gamma at H(1,c). Associativity and functoriality give exactly sigma_V
T_Y(j_c) = j_c' sigma_U. Gamma may be the specified ordinary-image mate; no
invertibility of h or sigma is used. The calculation holds in the actual completed
category, then survives rationalization and common-stage endpoint conjugation. -/
theorem coefficient_square (CC : SixFunctorClosedChange A A' T)
    (R : B ⥤ D) (R' : B' ⥤ D') (TY : D ⥤ D') (γ : R ⋙ TY ⟶ T ⋙ R') :
    CoefficientSquare CC R R' TY γ := by
  have homComparison_eq (CC : SixFunctorClosedChange A A' T)
      (M U : P.FullSubcategory) :
      homComparison CC M U = P'.ι.map (CC.comparison.hom.hom.app (op M, U)) := by
    unfold homComparison
    congr 1
    apply (A'.closed.transpose _ _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    change _ = ((A'.closed.adjunction _).homEquiv _ _).symm _
    rw [Adjunction.homEquiv_counit]
    have h := CC.comparison.evaluation M U
    have ht : A'.closed.tensor.map
        (Prod.mkHom (CC.comparison.hom.hom.app (op M, U))
          (𝟙 ((sixFunctorDomainChange P P' T CC.domain).obj M))) =
        (@MonoidalCategory.tensorRight _ _ A'.closed.monoidal
          ((sixFunctorDomainChange P P' T CC.domain).obj M)).map
            (CC.comparison.hom.hom.app (op M, U)) :=
      @MonoidalCategory.tensorHom_id _ _ A'.closed.monoidal _ _ _ _
    rw [ht] at h
    apply (cancel_epi (CC.comparison.tensor.hom.app
      ((sixFunctorDomainHom P Q H A.homPermitted A.homDomain).obj (op M, U), M))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
      CoefficientClosedStructure.evaluation] using h.symm
  intro M U V c U' V' i j c' w
  let F := sixFunctorDomainChange P P' T CC.domain
  let K := sixFunctorDomainHom P Q H A.homPermitted A.homDomain
  let K' := sixFunctorDomainHom P' Q' H' A'.homPermitted A'.homDomain
  have w' : F.map c.hom ≫ j.hom = i.hom ≫ c'.hom := by
    apply P'.ι.map_injective
    exact w
  have hn := CC.comparison.hom.hom.naturality (Prod.mkHom (𝟙 (op M)) c.hom)
  simp only [Functor.comp_map, Functor.prod_map, Functor.op_map, unop_id] at hn
  rw [F.map_id M, op_id] at hn
  change F.map (K.map (Prod.mkHom (𝟙 (op M)) c.hom)) ≫
      CC.comparison.hom.hom.app (op M, V) =
    CC.comparison.hom.hom.app (op M, U) ≫
      K'.map (Prod.mkHom (𝟙 (op (F.obj M))) (F.map c.hom)) at hn
  have hc :
      F.map (K.map (Prod.mkHom (𝟙 (op M)) c.hom)) ≫
          (CC.comparison.hom.hom.app (op M, V) ≫
            K'.map (Prod.mkHom (𝟙 (op (F.obj M))) j.hom)) =
        (CC.comparison.hom.hom.app (op M, U) ≫
          K'.map (Prod.mkHom (𝟙 (op (F.obj M))) i.hom)) ≫
            K'.map (Prod.mkHom (𝟙 (op (F.obj M))) c'.hom) := by
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← K'.map_comp]
    congr 2
    apply Prod.ext
    · simp
    · exact w'
  have hc' := congrArg (fun g ↦ R'.map (P'.ι.map g)) hc
  change TY.map (R.map ((hom A).map (Prod.mkHom (𝟙 (op M)) c.hom))) ≫
      (γ.app _ ≫ R'.map (homComparison CC M V ≫ (hom A').map
        (Prod.mkHom (𝟙 (op (F.obj M))) j.hom))) =
    (γ.app _ ≫ R'.map (homComparison CC M U ≫ (hom A').map
      (Prod.mkHom (𝟙 (op (F.obj M))) i.hom))) ≫
        R'.map ((hom A').map (Prod.mkHom (𝟙 (op (F.obj M))) c'.hom))
  have hg : TY.map (R.map ((hom A).map (Prod.mkHom (𝟙 (op M)) c.hom))) ≫
      γ.app ((hom A).obj (op M, V)) =
    γ.app ((hom A).obj (op M, U)) ≫
      R'.map (T.map ((hom A).map (Prod.mkHom (𝟙 (op M)) c.hom))) :=
    γ.naturality _
  rw [← Category.assoc, hg]
  rw [homComparison_eq, homComparison_eq]
  simp only [Category.assoc]
  congr 1
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc, hom, F, K, K',
    sixFunctorDomainChange, ObjectProperty.ι_obj_lift_map] using hc'

variable [HasShift B ℤ] [HasShift D ℤ]

/-- Source-shift components, with arbitrary coordinates N ≅ M[r].
Source: Stacks 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftFamily (A : SixFunctorClosedDomain P Q H) (R : B ⥤ D) :=
  ∀ (M N : P.FullSubcategory) (r : ℤ) (_e : N.obj ≅ M.obj⟦r⟧)
    (U : P.FullSubcategory),
    (functor A R U).obj (op N) ≅ ((functor A R U).obj (op M))⟦-r⟧

/-- The square in the question, in diagrammatic composition order.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftSquare {A : SixFunctorClosedDomain P Q H} {R : B ⥤ D}
    (s : ShiftFamily A R) : Prop :=
  ∀ (M N : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧)
    (U V : P.FullSubcategory) (c : U ≅ V),
    (substitution A R c).hom.app (op N) ≫ (s M N r e V).hom =
      (s M N r e U).hom ≫ ((substitution A R c).hom.app (op M))⟦-r⟧'

/-- Naturality of the comparison in both Hom variables and source coordinates.
Source: Stacks 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftNaturality {A : SixFunctorClosedDomain P Q H} {R : B ⥤ D}
    (s : ShiftFamily A R) : Prop :=
  (∀ (M N : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧)
    (U V : P.FullSubcategory) (c : U ⟶ V),
    R.map ((hom A).map (Prod.mkHom (𝟙 _) c)) ≫ (s M N r e V).hom =
      (s M N r e U).hom ≫ (R.map ((hom A).map (Prod.mkHom (𝟙 _) c)))⟦-r⟧') ∧
  (∀ (M N M' N' : P.FullSubcategory) (r : ℤ)
    (e : N.obj ≅ M.obj⟦r⟧) (e' : N'.obj ≅ M'.obj⟦r⟧)
    (a : M' ⟶ M) (b : N' ⟶ N), b.hom ≫ e.hom = e'.hom ≫ a.hom⟦r⟧' →
    ∀ U : P.FullSubcategory,
    (functor A R U).map b.op ≫ (s M' N' r e' U).hom =
      (s M N r e U).hom ≫ ((functor A R U).map a.op)⟦-r⟧')
end Maps

section Realization
variable {B : Type a} [Category.{b} B] [HasShift B ℤ]
  {D : Type d} [Category.{e} D] [HasShift D ℤ]
  {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
  (A : SixFunctorClosedDomain P Q H) (R : B ⥤ D)
  {C₀ : Type c} [Category.{v} C₀] (J : GrothendieckTopology C₀)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (O : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedHomUniverses.Modules.{c, v, u} J O)]
  {DY : Type d'} [Category.{e'} DY] [HasShift DY ℤ]
  (FX : B ⥤ RingedHomUniverses.D.{c, v, u, w} J O) [FX.CommShift ℤ]
  (FY : D ⥤ DY) [FY.CommShift ℤ]
  (R₀ : RingedHomUniverses.D.{c, v, u, w} J O ⥤ DY) [R₀.CommShift ℤ]
  (η : hom A ⋙ FX ≅ ((P.ι ⋙ FX).op.prod (P.ι ⋙ FX)) ⋙
    derivedInternalHomOfUniverses.{c, v, u, w} J O)
  (δ : R ⋙ FY ≅ FX ⋙ R₀)

/-- The realized comparison, using the fixed signed ringed-site source shift.
Source: Stacks 0A8X and 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def realizedShift (M N : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧)
    (U : P.FullSubcategory) :
    FY.obj ((functor A R U).obj (op N)) ≅
      FY.obj (((functor A R U).obj (op M))⟦-r⟧) :=
  δ.app _ ≪≫ R₀.mapIso (η.app (op N, U)) ≪≫
    R₀.mapIso ((derivedInternalHomOfUniverses.{c, v, u, w} J O).mapIso
      (Iso.prod ((FX.mapIso e ≪≫ (FX.commShiftIso r).app M.obj).symm.op) (Iso.refl _))) ≪≫
    R₀.mapIso ((RingedHomUniverses.sourceShift.{c, v, u, w} J O
      (FX.obj M.obj) r).symm.app (FX.obj U.obj)) ≪≫
    (R₀.commShiftIso (-r)).app _ ≪≫
    (shiftFunctor DY (-r)).mapIso
      (R₀.mapIso (η.symm.app (op M, U)) ≪≫ δ.symm.app _) ≪≫
    (FY.commShiftIso (-r)).symm.app _

/-- A family is normalized by the actual signed representative comparison.
Source: Stacks 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def RealizationNormalization (s : ShiftFamily A R) : Prop :=
  ∀ (M N : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧)
    (U : P.FullSubcategory),
    FY.map (s M N r e U).hom = (realizedShift A R J O FX FY R₀ η δ M N r e U).hom
end Realization

section Transport
variable {B : Type a} [Category.{b} B] [HasShift B ℤ]
  {D : Type d} [Category.{e} D] [HasShift D ℤ]
  {B' : Type a'} [Category.{b'} B'] [HasShift B' ℤ]
  {D' : Type d'} [Category.{e'} D'] [HasShift D' ℤ]
  {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
  {P' : ObjectProperty B'} {Q' : ObjectProperty (B'ᵒᵖ × B')}
  {H' : Q'.FullSubcategory ⥤ B'}
  {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
  {T : B ⥤ B'} [T.CommShift ℤ]
  (CC : SixFunctorClosedChange A A' T) (R : B ⥤ D) (R' : B' ⥤ D')
  (TY : D ⥤ D') [TY.CommShift ℤ] (γ : R ⋙ TY ⟶ T ⋙ R')

/-- Transport of the signed comparison by the specified coefficient maps.
Source: blueprint proof Step 3, field-stage passage
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftTransport (s : ShiftFamily A R) (s' : ShiftFamily A' R') : Prop :=
  ∀ (M N : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧)
    (U : P.FullSubcategory),
    TY.map (s M N r e U).hom ≫
        (TY.commShiftIso (-r)).hom.app ((functor A R U).obj (op M)) ≫
        (sigma CC R R' TY γ M U (Iso.refl _))⟦-r⟧' =
      sigma CC R R' TY γ N U (Iso.refl _) ≫
        (s' ((sixFunctorDomainChange P P' T CC.domain).obj M)
          ((sixFunctorDomainChange P P' T CC.domain).obj N) r
          (T.mapIso e ≪≫ (T.commShiftIso r).app M.obj)
          ((sixFunctorDomainChange P P' T CC.domain).obj U)).hom
end Transport

section Stages
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D} (f : X ⟶ Y)

/-- The signed comparison at finite coefficients, normalized in the actual ambient model.
Source: Stacks 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def FiniteNormalization (s : ShiftFamily (S.finiteClosed X) (S.finite.direct f)) : Prop :=
  RealizationNormalization (S.finiteClosed X) (S.finite.direct f)
    (Scheme.ProEt.topology X.obj.left)
    ((constantSheaf (Scheme.ProEt.topology X.obj.left) CommRingCat.{u+1}).obj
      (.of (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E n))))
    (Scheme.intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    (Scheme.intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    (Scheme.proEtaleConstantDerivedDirectImage f.hom.left (Padic.coefficientExtensionRing C.l E n))
    (S.finiteModelComparison X).comparison.hom (S.finiteDirectImage f) s

/-- Normalization at completed integral coefficients, in the completed ambient category.
Source: Stacks 08JA (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def IntegralNormalization
    (s : ShiftFamily (S.integralClosed X) (S.higher.integral.direct f)) : Prop :=
  RealizationNormalization (S.integralClosed X) (S.higher.integral.direct f)
    (Scheme.ProEt.topology X.obj.left) (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left)
    (sfIntegralConstructible C.l E X.obj.left).ι
    (sfIntegralConstructible C.l E Y.obj.left).ι
    (sfCompletedDerivedDirectImage C.l E f.hom.left)
    (S.integralModelComparison X).comparison.hom (S.higher.integralDirectImage f) s

/-- The same completed normalization at each finite coefficient field.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def StageIntegralNormalization (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    (s : ShiftFamily (S.coefficientClosedModels E₀ X).integral
      ((S.closure.coefficientStages E₀).integral.direct f)) : Prop :=
  RealizationNormalization (S.coefficientClosedModels E₀ X).integral
    ((S.closure.coefficientStages E₀).integral.direct f)
    (Scheme.ProEt.topology X.obj.left)
    (completedIntegralCommRingSheafUnrestricted C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
    (sfIntegralConstructible C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left).ι
    (sfIntegralConstructible C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Y.obj.left).ι
    (sfCompletedDerivedDirectImage C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) f.hom.left)
    (S.coefficientClosedModels E₀ X).realization.comparison.hom
    ((S.closure.coefficientStages E₀).integralDirectImage f) s

/-- Comparisons at the four coefficient kinds, including every common finite stage.
Source: blueprint proof Steps 2--3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
structure ShiftFamilies where
  finite : ShiftFamily (S.finiteClosed X) (S.finite.direct f)
  integral : ShiftFamily (S.integralClosed X) (S.higher.integral.direct f)
  rational : ShiftFamily (S.rationalClosed X) (S.higher.rational.direct f)
  stageIntegral : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    ShiftFamily (S.coefficientClosedModels E₀ X).integral
      ((S.closure.coefficientStages E₀).integral.direct f)
  stage : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    ShiftFamily (S.coefficientClosedModels E₀ X).rational
      ((S.closure.coefficientStages E₀).rational.direct f)
  closure : ShiftFamily (S.commonClosed X) (S.closure.commonStage.direct f)

/-- Normalization of all source shifts by signed representatives and coefficient images.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def Normalization (s : ShiftFamilies S f) : Prop := by
  letI (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E₀
  letI (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E₀
  exact
    FiniteNormalization S f s.finite ∧ IntegralNormalization S f s.integral ∧
    (∀ E₀, StageIntegralNormalization S f E₀ (s.stageIntegral E₀)) ∧
    ShiftNaturality s.rational ∧ (∀ E₀, ShiftNaturality (s.stage E₀)) ∧
    ShiftNaturality s.closure ∧
    ShiftTransport (S.rationalClosedComparison X) (S.higher.integral.direct f)
      (S.higher.rational.direct f) (sfRationalConstructibleLocalization C.l E Y.obj.left)
      (S.higher.rationalization.directAdjunction f).right.hom s.integral s.rational ∧
    (∀ E₀, ShiftTransport (S.coefficientClosedModels E₀ X).rationalization
      ((S.closure.coefficientStages E₀).integral.direct f)
      ((S.closure.coefficientStages E₀).rational.direct f)
      (sfRationalConstructibleLocalization C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Y.obj.left)
      ((S.closure.coefficientStages E₀).rationalization.directAdjunction f).right.hom
      (s.stageIntegral E₀) (s.stage E₀)) ∧
    (∀ E₀, ShiftTransport (S.commonClosedComparison E₀ X)
      ((S.closure.coefficientStages E₀).rational.direct f) (S.closure.commonStage.direct f)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
      ((S.closure.commonStageComparison E₀).directAdjunction f).right.hom
      (s.stage E₀) s.closure)

/-- All the allowed A5 coefficient substitution squares.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def CoefficientCoherence : Prop :=
  (∀ m : ℕ, CoefficientSquare (S.reductionClosedComparison m X)
    (S.higher.integral.direct f) ((S.integralNormalization.finiteLevels m).finite.direct f)
    (sixFunctorIntegralReduction D C E m Y)
    ((S.integralNormalization.reduction m).directAdjunction f).right.hom) ∧
  CoefficientSquare (S.rationalClosedComparison X) (S.higher.integral.direct f)
    (S.higher.rational.direct f) (sfRationalConstructibleLocalization C.l E Y.obj.left)
    (S.higher.rationalization.directAdjunction f).right.hom ∧
  (∀ (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L),
    CoefficientSquare (S.coefficientClosedComparison E₀ L h X)
    ((S.closure.coefficientStages E₀).rational.direct f)
    ((S.closure.coefficientStages L).rational.direct f)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left).T h)
    ((S.closure.coefficientTransition h).directAdjunction f).right.hom) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    CoefficientSquare (S.commonClosedComparison E₀ X)
    ((S.closure.coefficientStages E₀).rational.direct f) (S.closure.commonStage.direct f)
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
    ((S.closure.commonStageComparison E₀).directAdjunction f).right.hom)

/-- The normalized source-shift family exists at every coefficient stage.
Source: blueprint Verdier exchange proof Step 3; Stacks 0A8X and 08JA
(blueprint: lem-sf-derived-hom-substitution-shift-families-exists).

Proof: (1) At finite, completed integral and each stage-integral coefficient, define the
component at `M N r e U` by `realizedShift`: it is an isomorphism in the ambient ringed
derived category between objects in the essential image of the fully faithful inclusion
`FY`, so it is `FY` of a unique isomorphism of the coefficient category; this is the
component, and `FiniteNormalization`, `IntegralNormalization`, `StageIntegralNormalization`
hold by construction. (2) On Hom complexes the signed source shift reindexes a degree-`d`
family with sign `(-1)^(r*d)`; it commutes with postcomposition by chain maps, hence after
localization with `H(1,c)`; together with naturality of the direct-image shift comparison
this gives `ShiftSquare` at these three kinds. (3) At rational coefficients transport the
integral family through the invertible comparison `sigma` of the rationalization (its Hom
comparison and direct-image mate are isomorphisms) and extend to all objects by essential
surjectivity of rationalization; at each stage `E₀` likewise from `stageIntegral E₀`; at the
common stage transport from the stages `E₀`, which cover all objects, the transition
compatibilities making the result independent of the stage. (4) `ShiftTransport` holds by
construction, and `ShiftNaturality`, `ShiftSquare` at field coefficients follow from the
integral ones by naturality of `sigma` (`coefficient_square`) and of the shift
commutations. -/
theorem shift_families_exists [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    ∃ s : ShiftFamilies S f, Normalization S f s ∧
      ShiftSquare s.finite ∧ ShiftSquare s.integral ∧ ShiftSquare s.rational ∧
      (∀ E₀, ShiftSquare (s.stage E₀)) ∧ ShiftSquare s.closure := by
  sorry

/-- The normalization and naturality clauses determine a source-shift family uniquely.
Source: blueprint Verdier exchange proof Step 3; Stacks 08JA
(blueprint: lem-sf-derived-hom-substitution-shift-families-unique).

Proof: `ShiftFamilies` is a structure of six families, so compare them one by one
(funext over every index). Finite, integral and stage-integral: both components have the
same image `realizedShift` under the faithful full-subcategory inclusion `FY`, hence agree.
Rational: `ShiftTransport` from the (already equal) integral families, with `sigma`
invertible, determines the component at `(T M, T N, r, T e ≫ commShift, T U)`; every
rational object is isomorphic to such an image, and the two clauses of `ShiftNaturality`
(applied to isomorphisms `a`, `b`, `c`) carry the component to arbitrary `M N e U`. Each
stage `E₀`: the same, from `stageIntegral E₀`. Common stage: the same, by transport from the
stages `E₀`, whose images cover all objects. The `ShiftSquare` hypotheses are not needed. -/
theorem shift_families_unique [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (s t : ShiftFamilies S f)
    (hs : Normalization S f s ∧ ShiftSquare s.finite ∧ ShiftSquare s.integral ∧
      ShiftSquare s.rational ∧ (∀ E₀, ShiftSquare (s.stage E₀)) ∧ ShiftSquare s.closure)
    (ht : Normalization S f t ∧ ShiftSquare t.finite ∧ ShiftSquare t.integral ∧
      ShiftSquare t.rational ∧ (∀ E₀, ShiftSquare (t.stage E₀)) ∧ ShiftSquare t.closure) :
    s = t := by
  sorry

/-- Substitution is natural, commutes with the signed source shift, and obeys the
specified coefficient square. Source: current blueprint Verdier exchange proof Steps 2--3;
Stacks 0A8X, 08JA and 08J9 (blueprint: lem-sf-derived-hom-substitution-coherence).

Proof: (1) use the actual Hom bifunctor and ordinary direct-image functor. (2) The
Hom image of c and its inverse form the displayed natural isomorphism. (3) On Hom
complexes the signed source shift reindexes degree-d families with (-1)^(r*d).
It commutes with postcomposition, hence with localization and inverses of inverted
quasi-isomorphisms. Compose with direct-image shift naturality. Faithful ambient
inclusions determine the finite and completed families uniquely. (4) Uncurry the two
candidate coefficient composites: tensor-comparison naturality and evaluation naturality
identify both with T(c) composed with T(evaluation). Transpose back. (5) Postcompose by
v and use v T(c) = c' u. (6) Paste with the naturality square of the specified direct-image
mate. (7) Carry these identities through the completed category itself, rationalization,
and a common finite field stage. Adjacent endpoint comparisons cancel in composites.
The integral residue-Tor equality covers all integral representatives used to determine
the field families; naturality extends their normalization to every localized morphism.
No inference of completed equality from finite reductions, or inversion of ambient h,
is involved. -/
theorem coherence [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (∃! s : ShiftFamilies S f, Normalization S f s ∧
      ShiftSquare s.finite ∧ ShiftSquare s.integral ∧ ShiftSquare s.rational ∧
      (∀ E₀, ShiftSquare (s.stage E₀)) ∧ ShiftSquare s.closure) ∧
    CoefficientCoherence S f := by
  constructor
  · obtain ⟨s, hs⟩ := shift_families_exists S f
    refine ⟨s, hs, ?_⟩
    intro t ht
    exact (shift_families_unique S f s t hs ht).symm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro m
      exact coefficient_square (S.reductionClosedComparison m X)
        (S.higher.integral.direct f)
        ((S.integralNormalization.finiteLevels m).finite.direct f)
        (sixFunctorIntegralReduction D C E m Y)
        ((S.integralNormalization.reduction m).directAdjunction f).right.hom
    · exact coefficient_square (S.rationalClosedComparison X)
        (S.higher.integral.direct f) (S.higher.rational.direct f)
        (sfRationalConstructibleLocalization C.l E Y.obj.left)
        (S.higher.rationalization.directAdjunction f).right.hom
    · intro E₀ L h
      exact coefficient_square (S.coefficientClosedComparison E₀ L h X)
        ((S.closure.coefficientStages E₀).rational.direct f)
        ((S.closure.coefficientStages L).rational.direct f)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left).T h)
        ((S.closure.coefficientTransition h).directAdjunction f).right.hom
    · intro E₀
      exact coefficient_square (S.commonClosedComparison E₀ X)
        ((S.closure.coefficientStages E₀).rational.direct f)
        (S.closure.commonStage.direct f)
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀)
        ((S.closure.commonStageComparison E₀).directAdjunction f).right.hom
end Stages
end WeilConjectures.DerivedHomSubstitution
