/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseAdicAutomorphismPullback
public import WeilConjectures.AlgebraicGeometry.LisseAdicFiberFunctors
public import WeilConjectures.RepresentationTheory.LAdic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
import all WeilConjectures.AlgebraicGeometry.IntegralFibrePathConstruction
import all WeilConjectures.AlgebraicGeometry.FibreFunctorLinearTransport
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport

/-!
# The Weil fundamental representation on actual etale adic fibres

Source: Weil II (1.1.1), (1.1.6), (1.1.10); blueprint main-20261015,
def-wf-fundamental-representation (blueprint: def-wf-fundamental-representation).

Finite-cover germs specify path transport. Inverse limits and the two coefficient
extensions then specify its adic extension. No pro-etale sheaf is substituted for an
etale adic sheaf. The general degree-datum construction also applies away from curves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y z : Spec (.of Ω) ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
private def finiteSetPath (τ : fiber y ≅ fiber z) : flcFiber y ≅ flcFiber z :=
  NatIso.ofComponents (fun S ↦ (FiniteLocallyConstant.transport y z τ S).toIso) (by
    intro S T f
    apply ConcreteCategory.hom_ext
    intro x
    exact (FiniteLocallyConstant.sheafFiber_map_transport y z τ f x).symm)
set_option backward.isDefEq.respectTransparency false in
private theorem finiteSetPath_germ (τ : fiber y ≅ fiber z) (S : Y.FLC)
    (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : S.obj.obj.obj (op P.obj)) :
    (finiteSetPath τ).hom.app S ((pointSmallEtale y).toPresheafFiber P.obj a S.obj.obj s) =
      (pointSmallEtale z).toPresheafFiber P.obj (τ.hom.app P a) S.obj.obj s := by
  apply (FiniteLocallyConstant.stalkEquiv z S).injective
  change FiniteLocallyConstant.stalkEquiv z S
    (FiniteLocallyConstant.transport y z τ S _) = _
  rw [FiniteLocallyConstant.stalkEquiv_transport,
    FiniteLocallyConstant.stalkEquiv_toPresheafFiber,
    FiniteLocallyConstant.stalkEquiv_toPresheafFiber]
  let k : P ⟶ (equivalenceFiniteLocallyConstant Y).inverse.obj S :=
    ObjectProperty.homMk
      (((equivalenceFiniteLocallyConstant Y).counitIso.inv.app S).hom.hom.app
        (op P.obj) s).down
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom.naturality k) a)
set_option backward.isDefEq.respectTransparency false in
private theorem finiteSetGerm_surjective (S : Y.FLC)
    (x : (flcFiber y).obj S) :
    ∃ (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : S.obj.obj.obj (op P.obj)),
      (pointSmallEtale y).toPresheafFiber P.obj a S.obj.obj s = x := by
  let E := FiniteEtale.equivalenceFiniteLocallyConstant Y
  let P := E.inverse.obj S
  let a := (FiniteLocallyConstant.stalkEquiv y S x).down
  let s := (E.counitIso.hom.app S).hom.hom.app (op P.obj) (ULift.up (𝟙 P.obj))
  refine ⟨P, a, s, ?_⟩
  apply (FiniteLocallyConstant.stalkEquiv y S).injective
  rw [FiniteLocallyConstant.stalkEquiv_toPresheafFiber]
  have hs : (E.counitIso.inv.app S).hom.hom.app (op P.obj) s = ULift.up (𝟙 P.obj) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.hom.app (op P.obj)) (E.counitIso.app S).hom_inv_id) _
  change ULift.up ((pointSmallEtale y).fiber.map
    ((E.counitIso.inv.app S).hom.hom.app (op P.obj) s).down a) = _
  rw [hs]
  change ULift.up a = _
  exact ULift.up_down _
set_option backward.isDefEq.respectTransparency false in
private theorem finiteModuleGerm_surjective (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (hF : IsLisseModuleSheaf F)
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    ∃ (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : F.obj.obj (op P.obj)),
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s = x := by
  let S : Y.FLC := galoisUnderlyingFLC R F (pathLisseUnderlying R F hF)
  obtain ⟨P, a, s, hs⟩ := finiteSetGerm_surjective S (pathUnderlyingStalk y R F x)
  refine ⟨P, a, s, (pathUnderlyingStalk y R F).injective ?_⟩
  rw [pathUnderlyingStalk_germ]
  exact hs
set_option backward.isDefEq.respectTransparency false in
private theorem finiteLinearPath_germ (R : Type (u + 1)) [Ring R]
    (F : LisseModuleSheafCategory Y R) (τ : fiber y ≅ fiber z)
    (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : F.obj.obj.obj (op P.obj)) :
    ((pathFiniteIso y z (finiteSetPath τ) R).app F).hom
        ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj.obj s) =
      (pointSmallEtale z).ulift.{u + 1}.toPresheafFiber P.obj
        ⟨τ.hom.app P a⟩ F.obj.obj s := by
  apply (pathUnderlyingStalk z R F.obj).injective
  change pathUnderlyingStalk z R F.obj
    ((pathFiniteIso y z (finiteSetPath τ) R).hom.app F _) = _
  rw [pathFiniteIso_evaluation, pathUnderlyingStalk_germ, pathUnderlyingStalk_germ]
  exact finiteSetPath_germ τ
    (galoisUnderlyingFLC R F.obj (pathLisseUnderlying R F.obj F.property)) P a s

/-- Finite-cover germs determine the finite-coefficient path uniquely, even when the
coefficient ring itself is infinite; the underlying stalks are required to be finite.
Source: Stacks 0BND(2), Weil II (1.1.6)
(blueprint: def-wf-fundamental-representation).
Proof: represent the underlying finite locally constant set sheaf by a finite etale
cover. Evaluate the given path on that cover. Naturality for addition and scalar
multiplication makes the resulting bijection linear. Every germ is represented on
such a cover, so the displayed germ rule determines it uniquely. The inverse path
supplies its inverse. This is the finite step of the node's stalk transport. -/
theorem etaleFinitePathIso_exists (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (τ : fiber y ≅ fiber z) :
    ∃! e : (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F ≅
        (pointSmallEtale z).ulift.{u + 1}.sheafFiber.obj F,
      ∀ (P : Y.FiniteEtale) (a : (fiber y).obj P) (s : F.obj.obj (op P.obj)),
        e.hom ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s) =
          (pointSmallEtale z).ulift.{u + 1}.toPresheafFiber P.obj
            ⟨τ.hom.app P a⟩ F.obj s := by
  let hL := isLisseModuleSheaf_of_locallyConstant_of_finite_stalk R F
    hF.toIsLocallyConstantSheaf hfin
  let A : LisseModuleSheafCategory Y R := ⟨F, hL⟩
  refine ⟨(pathFiniteIso y z (finiteSetPath τ) R).app A,
    finiteLinearPath_germ R A τ, ?_⟩
  intro e he
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨P, a, s, rfl⟩ := finiteModuleGerm_surjective (y := y) R F hL x
  exact (he P a s).trans (finiteLinearPath_germ R A τ P a s).symm

/-- The uniquely normalized finite path, not an arbitrary stalk isomorphism.
Source: Stacks 0BND(2) (blueprint: def-wf-fundamental-representation). -/
def etaleFinitePathIso (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (τ : fiber y ≅ fiber z) :
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F ≅
      (pointSmallEtale z).ulift.{u + 1}.sheafFiber.obj F :=
  (etaleFinitePathIso_exists R F hF hfin τ).exists.choose

private theorem etaleFinitePath_germ (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale) (a : (fiber y).obj P)
    (s : F.obj.obj (op P.obj)) :
    (etaleFinitePathIso R F hF hfin τ).hom
        ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s) =
      (pointSmallEtale z).ulift.{u + 1}.toPresheafFiber P.obj
        ⟨τ.hom.app P a⟩ F.obj s :=
  (etaleFinitePathIso_exists R F hF hfin τ).exists.choose_spec P a s

set_option backward.isDefEq.respectTransparency false in
private theorem etaleFinitePath_naturality (R : Type (u + 1)) [Ring R]
    (F H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) (hH : IsFiniteLocallyConstantSheaf H)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (hhin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj H))
    (τ : fiber y ≅ fiber z) (f : F ⟶ H) :
    ((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map f ≫
        (etaleFinitePathIso R H hH hhin τ).hom =
      (etaleFinitePathIso R F hF hfin τ).hom ≫
        ((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map f := by
  apply ConcreteCategory.hom_ext
  intro x
  let hL := isLisseModuleSheaf_of_locallyConstant_of_finite_stalk R F
    hF.toIsLocallyConstantSheaf hfin
  obtain ⟨P, a, s, rfl⟩ := finiteModuleGerm_surjective (y := y) R F hL x
  change (etaleFinitePathIso R H hH hhin τ).hom
    (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map f _) =
      ((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map f
        ((etaleFinitePathIso R F hF hfin τ).hom _)
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
    etaleFinitePath_germ, etaleFinitePath_germ,
    GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  rfl

private theorem etaleFinitePath_refl (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    (t : Spec (.of Ω) ⟶ Y) :
    etaleFinitePathIso R F hF hfin (Iso.refl (fiber t)) = Iso.refl _ := by
  apply (etaleFinitePathIso_exists R F hF hfin (Iso.refl (fiber t))).unique
  · exact (etaleFinitePathIso_exists R F hF hfin _).exists.choose_spec
  · intro P a s
    rfl

private theorem etaleFinitePath_trans (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F)
    (hfin : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y),
      Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F))
    {t : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (σ : fiber z ≅ fiber t) :
    etaleFinitePathIso R F hF hfin (τ ≪≫ σ) =
      etaleFinitePathIso R F hF hfin τ ≪≫ etaleFinitePathIso R F hF hfin σ := by
  apply (etaleFinitePathIso_exists R F hF hfin (τ ≪≫ σ)).unique
  · exact (etaleFinitePathIso_exists R F hF hfin _).exists.choose_spec
  · intro P a s
    change (etaleFinitePathIso R F hF hfin σ).hom
      ((etaleFinitePathIso R F hF hfin τ).hom _) = _
    rw [etaleFinitePath_germ, etaleFinitePath_germ]
    rfl

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

/-- Adic levels have finite underlying stalks, not merely finitely generated modules.
Source: Weil II (1.1.1) b) (blueprint: def-wf-fundamental-representation).
Proof: the level-n stalk is finitely generated over O_E and annihilated by the
prescribed positive power of its uniformizer. It is therefore a quotient of a finite
power of O_E modulo that power. The residue field of the integers of the finite
extension E of Q_l is finite, so each such quotient ring, and then the stalk, is finite.
The lifted stalk has the same underlying module, hence the same finiteness. -/
theorem etaleIntegralLevel_finite (F : LisseIntegralSheaf l E Y) (n : ℕ)
    (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ Y) :
    Finite (((pointSmallEtale t).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
        (F.obj.obj (op n))) := by
  exact finite_integral_level l E F n t

/-- The inverse-limit extension of the normalized finite paths.
Source: Weil II (1.1.1) b), (1.1.6)
(blueprint: def-wf-fundamental-representation).
Proof: finite path maps commute with coefficient transitions by the germ rule.
Their composites with the limit projections form a cone. The limit universal
property gives a unique map; inverse paths give its inverse, projectionwise. -/
theorem etaleIntegralPathIso_exists (F : LisseIntegralSheaf l E Y)
    (τ : fiber y ≅ fiber z) :
    ∃! e : lisseIntegralFiber l E Y y F ≅ lisseIntegralFiber l E Y z F,
      ∀ n : ℕ, e.hom ≫ limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber)
          (op n) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
          (etaleFinitePathIso (Padic.coefficientExtensionIntegers l E)
            (F.obj.obj (op n)) (F.property.1 n) (etaleIntegralLevel_finite l E F n) τ).hom := by
  let e : F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber ≅
      F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber :=
    NatIso.ofComponents (fun n ↦
      etaleFinitePathIso (Padic.coefficientExtensionIntegers l E)
        (F.obj.obj n) (F.property.1 n.unop)
        (etaleIntegralLevel_finite l E F n.unop) τ) (by
      intro n m f
      exact etaleFinitePath_naturality _ _ _ _ _ _ _ τ (F.obj.map f))
  let φ : lisseIntegralFiber l E Y y F ≅ lisseIntegralFiber l E Y z F :=
    HasLimit.isoOfNatIso e
  have hφ : ∀ n : ℕ, φ.hom ≫
      limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber) (op n) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
          (etaleFinitePathIso (Padic.coefficientExtensionIntegers l E)
            (F.obj.obj (op n)) (F.property.1 n)
            (etaleIntegralLevel_finite l E F n) τ).hom := by
    intro n
    exact HasLimit.isoOfNatIso_hom_π e (op n)
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply Iso.ext
  apply limit.hom_ext
  intro n
  exact (hψ n.unop).trans (hφ n.unop).symm

/-- The unique limit map with the specified finite-level projections.
Source: Weil II (1.1.1) b) (blueprint: def-wf-fundamental-representation). -/
def etaleIntegralPathIso (F : LisseIntegralSheaf l E Y) (τ : fiber y ≅ fiber z) :
    lisseIntegralFiber l E Y y F ≅ lisseIntegralFiber l E Y z F :=
  (etaleIntegralPathIso_exists l E F τ).exists.choose

private theorem etaleIntegralPath_projection (F : LisseIntegralSheaf l E Y)
    (τ : fiber y ≅ fiber z) (n : ℕ) :
    (etaleIntegralPathIso l E F τ).hom ≫
        limit.π (F.obj ⋙ (pointSmallEtale z).ulift.{u + 1}.sheafFiber) (op n) =
      limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ≫
        (etaleFinitePathIso (Padic.coefficientExtensionIntegers l E)
          (F.obj.obj (op n)) (F.property.1 n) (etaleIntegralLevel_finite l E F n) τ).hom :=
  (etaleIntegralPathIso_exists l E F τ).exists.choose_spec n

private theorem etaleIntegralPath_refl (F : LisseIntegralSheaf l E Y)
    (t : Spec (.of Ω) ⟶ Y) :
    etaleIntegralPathIso l E F (Iso.refl (fiber t)) = Iso.refl _ := by
  apply (etaleIntegralPathIso_exists l E F (Iso.refl (fiber t))).unique
  · exact (etaleIntegralPathIso_exists l E F _).exists.choose_spec
  · intro n
    rw [etaleFinitePath_refl]
    simp

private theorem etaleIntegralPath_trans (F : LisseIntegralSheaf l E Y)
    {t : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (σ : fiber z ≅ fiber t) :
    etaleIntegralPathIso l E F (τ ≪≫ σ) =
      etaleIntegralPathIso l E F τ ≪≫ etaleIntegralPathIso l E F σ := by
  apply (etaleIntegralPathIso_exists l E F (τ ≪≫ σ)).unique
  · exact (etaleIntegralPathIso_exists l E F _).exists.choose_spec
  · intro n
    simp only [Iso.trans_hom]
    rw [Category.assoc, etaleIntegralPath_projection, ← Category.assoc,
      etaleIntegralPath_projection, Category.assoc, etaleFinitePath_trans]
    rfl

/-- Rational transport is exactly scalar extension of integral transport.
Source: Weil II (1.1.1) c) (blueprint: def-wf-fundamental-representation). -/
def etaleRationalPathIso (F : LisseRationalSheaf l E Y) (τ : fiber y ≅ fiber z) :
    lisseRationalFiber l E Y y F ≅ lisseRationalFiber l E Y z F :=
  (ModuleCat.extendScalars (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapIso
    (etaleIntegralPathIso l E F.integral τ)

variable (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

/-- Algebraic transport uses the finite coefficient field already in the object's pair.
Source: Weil II (1.1.1) d) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicPathIso (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    lisseAlgebraicFiber l Y Q y F ≅ lisseAlgebraicFiber l Y Q z F :=
  (ModuleCat.extendScalars (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).mapIso
    (etaleRationalPathIso l (lisseAlgebraicPair l Y Q F).base.val
      (lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F)) τ)

/-- Its linear equivalence retains the same actual etale adic fibres.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicPath (F : LisseAlgebraicSheaf l Y Q) (τ : fiber y ≅ fiber z) :
    lisseAlgebraicFiber l Y Q y F ≃ₗ[Q] lisseAlgebraicFiber l Y Q z F :=
  (etaleAlgebraicPathIso l Q F τ).toLinearEquiv

omit [IsAlgClosure ℚ_[l] Q] in
set_option backward.isDefEq.respectTransparency false in
private theorem etaleAlgebraicPath_refl (F : LisseAlgebraicSheaf l Y Q)
    (t : Spec (.of Ω) ⟶ Y) :
    etaleAlgebraicPathIso l Q F (Iso.refl (fiber t)) = Iso.refl _ := by
  unfold etaleAlgebraicPathIso etaleRationalPathIso
  rw [etaleIntegralPath_refl]
  exact (congrArg (fun e ↦ (ModuleCat.extendScalars
    (algebraMap (lisseAlgebraicPair l Y Q F).base.val Q)).mapIso e)
    (Functor.mapIso_refl
      (ModuleCat.extendScalars (algebraMap
        (Padic.coefficientExtensionIntegers l (lisseAlgebraicPair l Y Q F).base.val)
        (lisseAlgebraicPair l Y Q F).base.val)) _)).trans
      (Functor.mapIso_refl _ _)

omit [IsAlgClosure ℚ_[l] Q] in
set_option backward.isDefEq.respectTransparency false in
private theorem etaleAlgebraicPath_trans (F : LisseAlgebraicSheaf l Y Q)
    {t : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (σ : fiber z ≅ fiber t) :
    etaleAlgebraicPathIso l Q F (τ ≪≫ σ) =
      etaleAlgebraicPathIso l Q F τ ≪≫ etaleAlgebraicPathIso l Q F σ := by
  unfold etaleAlgebraicPathIso etaleRationalPathIso
  rw [etaleIntegralPath_trans, Functor.mapIso_trans, Functor.mapIso_trans]

-- Keep the original public closure assumption although the transport laws need less.
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized paths obey the representation laws.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation).
Proof: identity and composition hold on finite-cover germs, then on all finite
stalks. Apply the limit projections and extend scalars twice. -/
theorem etaleAlgebraicPath_laws (F : LisseAlgebraicSheaf l Y Q)
    (t : Spec (.of Ω) ⟶ Y) :
    (etaleAlgebraicPath l Q F (Iso.refl (fiber t))).toLinearMap = LinearMap.id ∧
    ∀ g h : Aut (fiber t),
      (etaleAlgebraicPath l Q F (g * h)).toLinearMap =
        (etaleAlgebraicPath l Q F g).toLinearMap *
          (etaleAlgebraicPath l Q F h).toLinearMap := by
  constructor
  · unfold etaleAlgebraicPath
    rw [etaleAlgebraicPath_refl]
    rfl
  · intro g h
    change (etaleAlgebraicPathIso l Q F (h ≪≫ g)).toLinearEquiv.toLinearMap = _
    rw [etaleAlgebraicPath_trans]
    rfl

/-- The geometric representation on the actual etale fibre.
Source: Weil II (1.1.6) (blueprint: def-wf-fundamental-representation). -/
def etaleGeometricRep (F : LisseAlgebraicSheaf l Y Q) (t : Spec (.of Ω) ⟶ Y) :
    Representation Q (Aut (fiber t)) (lisseAlgebraicFiber l Y Q t F) where
  toFun g := (etaleAlgebraicPath l Q F g).toLinearMap
  map_one' := (etaleAlgebraicPath_laws l Q F t).1
  map_mul' := (etaleAlgebraicPath_laws l Q F t).2

/-- An actual etale adic Weil sheaf, with no Frobenius-stable integral lattice required.
Source: Weil II (1.1.10)(i) (blueprint: def-wf-fundamental-representation). -/
abbrev EtaleLisseWeilSheaf (h : Y ≅ Y) :=
  Endofunctor.IsoAlgebra (lisseAlgebraicAutomorphismPullback h l Q)

/-- The stalk of an algebraic-coefficient morphism on the recorded object fibres.
Source: Weil II (1.1.1) d) (blueprint: def-wf-fundamental-representation). -/
def etaleAlgebraicFiberMap (t : Spec (.of Ω) ⟶ Y)
    {F G : LisseAlgebraicSheaf l Y Q} (f : F ⟶ G) :
    lisseAlgebraicFiber l Y Q t F ⟶ lisseAlgebraicFiber l Y Q t G :=
  eqToHom (lisseAlgebraicFiberFunctor_obj l Y t Q F).symm ≫
    (lisseAlgebraicFiberFunctor l Y t Q).map f ≫
      eqToHom (lisseAlgebraicFiberFunctor_obj l Y t Q G)

omit [IsAlgClosure ℚ_[l] Q] in
/-- Composition of normalized algebraic paths, in the actual recorded fibres.
Source: Weil II (1.1.6), finite germs followed by inverse limits and scalar extension
(blueprint: new-t2-etale-adic-path-data).
Proof: the finite germ rule is compatible with composition. The integral limit
projections detect equality, and both scalar-extension functors preserve composition. -/
theorem etaleAlgebraicPathIso_trans (F : LisseAlgebraicSheaf l Y Q)
    {t : Spec (.of Ω) ⟶ Y} (τ : fiber y ≅ fiber z) (σ : fiber z ≅ fiber t) :
    etaleAlgebraicPathIso l Q F (τ ≪≫ σ) =
      etaleAlgebraicPathIso l Q F τ ≪≫ etaleAlgebraicPathIso l Q F σ :=
  etaleAlgebraicPath_trans l Q F τ σ

end AlgebraicGeometry.Scheme
