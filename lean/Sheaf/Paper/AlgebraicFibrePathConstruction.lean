/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.IntegralFibrePathConstruction
public import Sheaf.Paper.RationalFibrePathConstruction
public import Sheaf.Paper.LocalizedFibrePathTransport
import Sheaf.Paper.RationalFibrePathScalarSquare
import Sheaf.Paper.CoefficientFibreComparisonNaturality

/-!
# Algebraic coefficient fibre paths

Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme

private theorem scalarTensorObjEq {R : Type*} {K : Type (u + 1)}
    [Field R] [Field K]
    [Algebra R K] (E : IntermediateField R K) {C : Type*} [Category C]
    (R S : C ⥤ ModuleCat.{u + 1} E)
    (δ : R ≅ S) {H F : C} (h : H = F) {V W : ModuleCat.{u + 1} E}
    (ey : R.obj F = V) (ez : S.obj F = W)
    (hy : (ModuleCat.extendScalars (algebraMap E K)).obj (R.obj H) =
      ModuleCat.of K (K ⊗[E] V))
    (hz : (ModuleCat.extendScalars (algebraMap E K)).obj (S.obj H) =
      ModuleCat.of K (K ⊗[E] W))
    (a : K) (x : R.obj F) :
    eqToHom hz
      ((ModuleCat.extendScalars (algebraMap E K)).map (δ.hom.app H)
        (eqToHom hy.symm (a ⊗ₜ[E] (eqToHom ey x)))) =
      a ⊗ₜ[E] (eqToHom ez (δ.hom.app F x)) := by
  cases h
  cases ey
  cases ez
  simp only [eqToHom_refl]
  rfl

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  (i : IntegralFibrePathTransport l Y Q)
  {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
  {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
  (t : flcFiber y ≅ flcFiber z)

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber
  GrothendieckTopology.Point.presheafFiber lisseIntegralFiberFunctor
  lisseRationalFiberFunctor lisseIntegralFiber lisseRationalFiber

/-- Extension of the rational path to one recorded coefficient category.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction). -/
def coefficientModelFibrePathIso (E : Padic.FiniteCoefficientFields l Q) :
    lisseCanonicalCoefficientModelFiberFunctor l Y y Q E ≅
      lisseCanonicalCoefficientModelFiberFunctor l Y z Q E :=
  Functor.isoWhiskerLeft
    (eqToHom ((lisseCoefficientDiagramData l Y Q).obj_eq E)).toFunctor
    (Functor.isoWhiskerRight
      ((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t)
      (ModuleCat.extendScalars (algebraMap E.val Q)))

/-- The explicit coefficient comparison respects model paths.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
Proof: apply the rational scalar square and transfer it along the fixed category values. -/
theorem canonicalRawCoefficientPath {E L : Padic.FiniteCoefficientFields l Q}
    (f : E ⟶ L) :
    lisseCanonicalRawCoefficientComparison l Y y Q f ≪≫
        Functor.isoWhiskerLeft
          ((lisseCoefficientDiagramData l Y Q).diagram.map f.toLoc).toFunctor
          (coefficientModelFibrePathIso l Y Q i y z t L) =
      coefficientModelFibrePathIso l Y Q i y z t E ≪≫
        lisseCanonicalRawCoefficientComparison l Y z Q f := by
  unfold lisseCanonicalRawCoefficientComparison coefficientModelFibrePathIso
  apply coefficientFiberRawComparison_path l Y Q
    (fun E ↦ lisseRationalFiberFunctor l E.val Y y)
    (fun E ↦ lisseRationalFiberFunctor l E.val Y z)
    (fun E ↦ (rationalFibrePathFamily l E.val Y (i.linear E)).map y z t)
  apply Iso.ext
  apply NatTrans.ext
  funext F
  have hs := rationalFibreComparisonIso_path l Y Q i y z t E L (leOfHom f) Q
    (algebraMap E.val Q) (algebraMap L.val Q) (by ext a; rfl) F
  unfold rationalFibreComparisonIso at hs
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using hs.symm

/-- A natural path on coefficient pairs using the uniquely normalized comparisons.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction). -/
def canonicalCoefficientFibrePathIso :
    lisseCanonicalCoefficientFiberFunctor l Y y Q ≅
      lisseCanonicalCoefficientFiberFunctor l Y z Q := by
  unfold lisseCanonicalCoefficientFiberFunctor
  exact Pseudofunctor.normalizedGrothendieckFiberPathIso
    (Padic.finiteCoefficientBase l Q)
    (fun E ↦ show (⊥ : IntermediateField ℚ_[l] Q) ≤ E.val from bot_le)
    (lisseCoefficientDiagramData l Y Q).diagram
    (lisseCanonicalCoefficientModelFiberFunctor l Y y Q)
    (fun {_ _} f ↦ lisseCanonicalRawCoefficientComparison l Y y Q f)
    (lisseCanonicalCoefficientEndomorphisms l Y y Q)
    (lisseCanonicalCoefficientModelFiberFunctor l Y z Q)
    (fun {_ _} f ↦ lisseCanonicalRawCoefficientComparison l Y z Q f)
    (lisseCanonicalCoefficientEndomorphisms l Y z Q)
    (coefficientModelFibrePathIso l Y Q i y z t)
    (fun E ↦ canonicalRawCoefficientPath l Y Q i y z t
      (homOfLE (show Padic.finiteCoefficientBase l Q ≤ E from
        show (⊥ : IntermediateField ℚ_[l] Q) ≤ E.val from bot_le)))

/-- The model paths descend to the algebraic coefficient localization.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction). -/
@[irreducible]
def algebraicFibrePathIso :
    lisseAlgebraicFiberFunctor l Y y Q ≅ lisseAlgebraicFiberFunctor l Y z Q := by
  unfold lisseAlgebraicFiberFunctor
  exact Localization.Construction.liftFiberNatIso _
    (lisseCanonicalCoefficientFiberFunctor_inverts l Y y Q)
    (lisseCanonicalCoefficientFiberFunctor_inverts l Y z Q)
    (canonicalCoefficientFibrePathIso l Y Q i y z t)

attribute [local semireducible] lisseAlgebraicFiberFunctor
  lisseCanonicalCoefficientFiberFunctor Pseudofunctor.normalizedGrothendieckFiberFunctor

/-- The descended path is scalar extension of the rational path on each pair.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
Proof: localization keeps the components, and the coefficient path has the displayed
rational components by its construction. -/
theorem algebraicFibrePathIso_component (X : LisseCoefficientPairs l Y Q) :
    (algebraicFibrePathIso l Y Q i y z t).hom.app
        ((lisseCoefficientCocartesian l Y Q).Q.obj X) =
      (ModuleCat.extendScalars (algebraMap X.base.val Q)).map
        (((rationalFibrePathFamily l X.base.val Y (i.linear X.base)).map y z t).hom.app
          (lisseCoefficientPairModel l Y Q X)) := by
  unfold algebraicFibrePathIso
  with_unfolding_all
    change (Localization.Construction.liftFiberNatIso _ _ _
    (canonicalCoefficientFibrePathIso l Y Q i y z t)).hom.app _ = _
  rw [Localization.Construction.liftFiberNatIso_hom_app]
  rfl

/-- The inverse descended path has the inverse rational components.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
Proof: the inverse localization functor preserves the inverse components of an isomorphism. -/
theorem algebraicFibrePathIso_inv_component (X : LisseCoefficientPairs l Y Q) :
    (algebraicFibrePathIso l Y Q i y z t).inv.app
        ((lisseCoefficientCocartesian l Y Q).Q.obj X) =
      (ModuleCat.extendScalars (algebraMap X.base.val Q)).map
        (((rationalFibrePathFamily l X.base.val Y (i.linear X.base)).map y z t).inv.app
          (lisseCoefficientPairModel l Y Q X)) := by
  unfold algebraicFibrePathIso
  with_unfolding_all
    change (Localization.Construction.liftFiberNatIso _ _ _
    (canonicalCoefficientFibrePathIso l Y Q i y z t).symm).hom.app _ = _
  rw [Localization.Construction.liftFiberNatIso_hom_app]
  rfl

/-- The descended algebraic paths satisfy the four path laws.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
Proof: evaluate on each localized coefficient pair, use the rational path laws,
and use functoriality of extension of scalars. -/
def algebraicFibrePathFamily :
    LinearFibrePathFamily Y (LisseAlgebraicSheaf l Y Q) Q
      (fun y ↦ lisseAlgebraicFiberFunctor l Y y Q) where
  map := by
    intro Ωy _ _ y Ωz _ _ z t
    exact algebraicFibrePathIso l Y Q i y z t
  identity := by
    intro Ωy _ _ y
    apply Iso.ext
    apply NatTrans.ext
    funext F
    obtain ⟨X, rfl⟩ :=
      (Localization.Construction.objEquiv (lisseCoefficientCocartesian l Y Q)).surjective F
    dsimp only [Localization.Construction.objEquiv, Equiv.coe_fn_mk]
    rw [algebraicFibrePathIso_component l Y Q i y y (Iso.refl _) X,
      (rationalFibrePathFamily l X.base.val Y (i.linear X.base)).identity]
    simp only [Iso.refl_hom, NatTrans.id_app]
    unfold lisseAlgebraicFiberFunctor lisseCanonicalCoefficientFiberFunctor
      Pseudofunctor.normalizedGrothendieckFiberFunctor
    exact (ModuleCat.extendScalars (algebraMap X.base.val Q)).map_id _
  composition := by
    intro Ωy _ _ y Ωz _ _ z Ωq _ _ q t s
    apply Iso.ext
    apply NatTrans.ext
    funext F
    obtain ⟨X, rfl⟩ :=
      (Localization.Construction.objEquiv (lisseCoefficientCocartesian l Y Q)).surjective F
    dsimp only [Localization.Construction.objEquiv, Equiv.coe_fn_mk]
    simp only [Iso.trans_hom, NatTrans.comp_app]
    rw [algebraicFibrePathIso_component l Y Q i y q (t ≪≫ s) X,
      algebraicFibrePathIso_component l Y Q i y z t X,
      algebraicFibrePathIso_component l Y Q i z q s X,
      (rationalFibrePathFamily l X.base.val Y (i.linear X.base)).composition y z q t s]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]
  conjugation := by
    intro Ωy _ _ y Ωz _ _ z t g
    apply Iso.ext
    apply NatTrans.ext
    funext F
    obtain ⟨X, rfl⟩ :=
      (Localization.Construction.objEquiv (lisseCoefficientCocartesian l Y Q)).surjective F
    dsimp only [Localization.Construction.objEquiv, Equiv.coe_fn_mk]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [algebraicFibrePathIso_component l Y Q i z z (t.conjAut g) X,
      algebraicFibrePathIso_component l Y Q i y y g X,
      algebraicFibrePathIso_component l Y Q i y z t X,
      algebraicFibrePathIso_inv_component l Y Q i y z t X,
      (rationalFibrePathFamily l X.base.val Y (i.linear X.base)).conjugation y z t g]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  «change» := by
    intro Ωy _ _ y Ωz _ _ z t s
    apply Iso.ext
    apply NatTrans.ext
    funext F
    obtain ⟨X, rfl⟩ :=
      (Localization.Construction.objEquiv (lisseCoefficientCocartesian l Y Q)).surjective F
    dsimp only [Localization.Construction.objEquiv, Equiv.coe_fn_mk]
    simp only [Iso.trans_hom, NatTrans.comp_app]
    rw [algebraicFibrePathIso_component l Y Q i y z s X,
      algebraicFibrePathIso_component l Y Q i y z t X,
      algebraicFibrePathIso_component l Y Q i z z (t.symm ≪≫ s) X,
      (rationalFibrePathFamily l X.base.val Y (i.linear X.base)).«change» y z t s]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]

/-- The descended path has the prescribed tensor formula on every displayed model.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-algebraic-fibre-path-construction).
Proof: the localization component is scalar extension of the rational path on the
coefficient pair. Transporting a displayed model to the coefficient category and back
cancels. Naturality of the rational path with that cancellation identifies the component
with its component at the original model. The fibre object transports are the same
object equality transports. Apply extension of scalars to a pure tensor and cancel
the rational fibre object identifications to obtain the displayed formula. -/
theorem algebraicFibrePathFamily_evaluation (E : Padic.FiniteCoefficientFields l Q)
    (F : LisseRationalSheaf l E.val Y) (a : Q)
    (x : (lisseRationalFiberFunctor l E.val Y y).obj F) :
    eqToHom (lisseAlgebraicFiber_ofModel l Y z Q E F)
      (eqToHom (lisseAlgebraicFiberFunctor_obj l Y z Q (lisseAlgebraicOfModel l Y Q E F))
        (((algebraicFibrePathFamily l Y Q i).map y z t).hom.app
          (lisseAlgebraicOfModel l Y Q E F)
          (eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q
              (lisseAlgebraicOfModel l Y Q E F)).symm
            (eqToHom (lisseAlgebraicFiber_ofModel l Y y Q E F).symm
              (a ⊗ₜ[E.val]
                (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F) x)))))) =
      a ⊗ₜ[E.val]
        (eqToHom (lisseRationalFiberFunctor_obj l E.val Y z F)
          (((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t).hom.app F x)) := by
  let X : LisseCoefficientPairs l Y Q := {
    base := E
    fiber := (eqToHom ((lisseCoefficientDiagramData l Y Q).obj_eq E).symm).toFunctor.obj F }
  let H := lisseCoefficientPairModel l Y Q X
  have hX : H = F := by
    dsimp only [H, lisseCoefficientPairModel, X]
    have cancel (C D : Cat.{u + 1, u + 2}) (h : C = D) (F : D) :
        (eqToHom h).toFunctor.obj ((eqToHom h.symm).toFunctor.obj F) = F := by
      cases h
      rfl
    exact cancel ((lisseCoefficientDiagramData l Y Q).diagram.obj ⟨E⟩)
      (Cat.of (LisseRationalSheaf l E.val Y))
      ((lisseCoefficientDiagramData l Y Q).obj_eq E) F
  let hy := (lisseAlgebraicFiberFunctor_obj l Y y Q (lisseAlgebraicOfModel l Y Q E F)).trans
    (lisseAlgebraicFiber_ofModel l Y y Q E F)
  let hz := (lisseAlgebraicFiberFunctor_obj l Y z Q (lisseAlgebraicOfModel l Y Q E F)).trans
    (lisseAlgebraicFiber_ofModel l Y z Q E F)
  have cast_y (v : ModuleCat.of Q
      (Q ⊗[E.val] (lisseRationalFiber l E.val Y y F))) :
      eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q (lisseAlgebraicOfModel l Y Q E F)).symm
        (eqToHom (lisseAlgebraicFiber_ofModel l Y y Q E F).symm v) = eqToHom hy.symm v := by
    exact ConcreteCategory.congr_hom (eqToHom_trans _ _) v
  have cast_z (v : (lisseAlgebraicFiberFunctor l Y z Q).obj
      (lisseAlgebraicOfModel l Y Q E F)) :
      eqToHom (lisseAlgebraicFiber_ofModel l Y z Q E F)
        (eqToHom (lisseAlgebraicFiberFunctor_obj l Y z Q
          (lisseAlgebraicOfModel l Y Q E F)) v) = eqToHom hz v := by
    exact ConcreteCategory.congr_hom (eqToHom_trans _ _) v
  rw [cast_y, cast_z]
  change eqToHom hz ((algebraicFibrePathIso l Y Q i y z t).hom.app
    ((lisseCoefficientCocartesian l Y Q).Q.obj X)
    (eqToHom hy.symm (a ⊗ₜ[E.val]
      (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F) x)))) = _
  rw [algebraicFibrePathIso_component l Y Q i y z t X]
  with_unfolding_all
    exact scalarTensorObjEq E.val (lisseRationalFiberFunctor l E.val Y y)
      (lisseRationalFiberFunctor l E.val Y z)
      ((rationalFibrePathFamily l E.val Y (i.linear E)).map y z t) hX
      (lisseRationalFiberFunctor_obj l E.val Y y F)
      (lisseRationalFiberFunctor_obj l E.val Y z F) hy hz a x

end AlgebraicGeometry.Scheme
