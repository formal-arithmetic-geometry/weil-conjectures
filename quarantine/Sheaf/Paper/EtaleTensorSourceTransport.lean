/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Etale source transport of a tensor comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
(blueprint: lem-pur-etale-tensor-source-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open FiniteEtaleNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- Transport a tensor comparison through a further etale source arrow.
Source: thm-pur-composition-coherence.proof.md, Step 1; the refinement of
lem-pur-etale-cartesian-tower-tensor-comparison, Step 6.

Proof: Use the etale-source cocycle on (H,qQ,G p), then postcompose with the
H-pullback of E_J,qp. The specified composite law hcomp identifies its output
with E_HJ,qp, after the associativity and square congruences. Pull hsecond
back along H. Naturality of the tensor comparison moves this equality through
the two tensor inputs. Functoriality combines E_H,qQ with H-pullback of x.
Monoidality of the pullback compositor identifies the result with HJ-pullback
of sigma_q,p; pullback associativity gives the two displayed input compositors.
Only commutativity w is used, so the outer square need not be Cartesian.
Identity arrows and empty schemes satisfy these same equations.
(blueprint: lem-pur-etale-tensor-source-transport). -/
theorem etale_tensor_source_transport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B T A Q R : Scheme.{u}}
    [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [A.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (A ↘ Spec (.of P.field.k))]
    [QuasiCompact (A ↘ Spec (.of P.field.k))]
    [Q.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Q ↘ Spec (.of P.field.k))]
    [QuasiCompact (Q ↘ Spec (.of P.field.k))]
    [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    (q : A ⟶ T) [q.IsOver (Spec (.of P.field.k))]
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (p : T ⟶ B) [p.IsOver (Spec (.of P.field.k))]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (G : Q ⟶ T) [G.IsOver (Spec (.of P.field.k))]
    [IsSeparated G] [LocallyOfFiniteType G] [QuasiCompact G]
    [Etale G]
    (qQ : R ⟶ Q) [qQ.IsOver (Spec (.of P.field.k))]
    [IsSeparated qQ] [LocallyOfFiniteType qQ] [QuasiCompact qQ]
    (J : R ⟶ A) [J.IsOver (Spec (.of P.field.k))]
    [IsSeparated J] [LocallyOfFiniteType J] [QuasiCompact J]
    [Etale J]
    (dq dp : ℕ) [SmoothOfRelativeDimension dq q] [SmoothOfRelativeDimension dp p]
    [SmoothOfRelativeDimension dq qQ]
    (w : J ≫ q = qQ ≫ G)
    (x : omega P qQ ⟶ (pull P J).obj (omega P q))
    {W : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    (H : W ⟶ R) [H.IsOver (Spec (.of P.field.k))]
    [IsSeparated H] [LocallyOfFiniteType H] [QuasiCompact H]
    [Etale H]
    (hsecond : sigma (ModuleCat.{u + 1} P.Coefficient) (qQ) (G ≫ p)
        (cf := compactification P (qQ)) (cg := compactification P (G ≫ p))
        (cfg := compactification P ((qQ) ≫ (G ≫ p))) (comp P (qQ) (G ≫ p)) ≫
      (FiniteEtaleNormalization.congr P ((qQ) ≫ (G ≫ p)) ((J) ≫ (q ≫ p))
        ((Category.assoc qQ G p).symm.trans
          ((congrArg (fun f ↦ f ≫ p) w.symm).trans (Category.assoc J q p)))).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
      (sourceEtale P (J) (q ≫ p)).hom =
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) _).map (x)).app
        ((pull P (qQ)).obj (omega P (G ≫ p))) ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) _).obj
        ((pull P (J)).obj (omega P q))).map ((pull P qQ).map (sourceEtale P G p).hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) qQ G).inv.app
          (omega P p) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) J q
          (qQ ≫ G) w.symm).hom.app
          (omega P p)) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) (J) (omega P q)
        ((pull P q).obj (omega P p))).inv ≫
      (pull P (J)).map (sigma (ModuleCat.{u + 1} P.Coefficient) q p
        (cf := compactification P q) (cg := compactification P p)
        (cfg := compactification P (q ≫ p)) (comp P q p)))
    (hcomp : (sourceEtale P (H ≫ J) (q ≫ p)).hom =
      (FiniteEtaleNormalization.congr P ((H ≫ J) ≫ (q ≫ p))
        (H ≫ J ≫ (q ≫ p)) (Category.assoc H J (q ≫ p))).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
      (sourceEtale P H (J ≫ (q ≫ p))).hom ≫
      (pull P H).map (sourceEtale P J (q ≫ p)).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app (omega P (q
        ≫ p))) :
    sigma (ModuleCat.{u + 1} P.Coefficient) (H ≫ qQ) (G ≫ p)
        (cf := compactification P (H ≫ qQ)) (cg := compactification P (G ≫ p))
        (cfg := compactification P ((H ≫ qQ) ≫ (G ≫ p))) (comp P (H ≫ qQ) (G ≫ p)) ≫
      (FiniteEtaleNormalization.congr P ((H ≫ qQ) ≫ (G ≫ p)) ((H ≫ J) ≫ (q ≫ p))
        ((Category.assoc (H ≫ qQ) G p).symm.trans
          ((congrArg (fun f ↦ f ≫ p)
            ((Category.assoc H qQ G).trans
              ((congrArg (fun f ↦ H ≫ f) w.symm).trans
                (Category.assoc H J q).symm))).trans
            (Category.assoc (H ≫ J) q p)))).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
      (sourceEtale P (H ≫ J) (q ≫ p)).hom =
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) _).map ((sourceEtale P H qQ).hom ≫
          (pull P H).map x ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
            (omega P q))).app
        ((pull P (H ≫ qQ)).obj (omega P (G ≫ p))) ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) _).obj
        ((pull P (H ≫ J)).obj (omega P q))).map ((pull P (H ≫ qQ)).map (sourceEtale P G p).hom ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) (H ≫ qQ) G).inv.app
            (omega P p) ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
            (H ≫ J) q ((H ≫ qQ) ≫ G)
            ((Category.assoc H qQ G).trans
              ((congrArg (fun f ↦ H ≫ f) w.symm).trans
                (Category.assoc H J q).symm))).hom.app (omega P p)) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) (H ≫ J) (omega P q)
        ((pull P q).obj (omega P p))).inv ≫
      (pull P (H ≫ J)).map (sigma (ModuleCat.{u + 1} P.Coefficient) q p
        (cf := compactification P q) (cg := compactification P p)
        (cfg := compactification P (q ≫ p)) (comp P q p)) := by sorry

end AlgebraicGeometry.ProEtale
