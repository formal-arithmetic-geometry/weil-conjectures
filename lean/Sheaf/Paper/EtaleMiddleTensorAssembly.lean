/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Eliminating the etale middle factor

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
(blueprint: lem-pur-etale-middle-tensor-assembly).
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

/-- Eliminate an etale middle arrow in a smooth tensor cocycle, and then use an
etale source comparison across a commutative square. No Cartesian hypothesis is needed.
Source: thm-pur-composition-coherence.proof.md, Step 1; the refinement of
lem-pur-etale-cartesian-tower-tensor-comparison, Steps 3--4.

Proof: Apply the threefold sigma cocycle to (qQ,G,p). Replace sigma_G,p followed
by E_G,p by the normalized eta_G tensor identity. The right unitor and the
monoidality of qQ-pullback remove omega_G. Cancel the resulting invertible
input comparison. Apply the etale-source cocycle to (J,q,p), transport qQ G
across w, and substitute hfirst. Tensor functoriality combines its first factor
with qQ-pullback of E_G,p; naturality of the pullback compositor supplies the
second factor displayed here. Empty schemes, identity etale maps, and relative
dimension zero require the same cancellations and impose no extra hypotheses.
(blueprint: lem-pur-etale-middle-tensor-assembly). -/
theorem etale_middle_tensor_assembly
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
    (hfirst : (targetUnit (ModuleCat.{u + 1} P.Coefficient) qQ G (cf := compactification P qQ)
        (ce := compactification P G) (rho P G)).inv ≫
      sigma (ModuleCat.{u + 1} P.Coefficient) qQ G (cf := compactification P qQ)
        (cg := compactification P G) (cfg := compactification P (qQ ≫ G)) (comp P qQ G) ≫
      (FiniteEtaleNormalization.congr P (qQ ≫ G) (J ≫ q) w.symm).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) T) ≫ (sourceEtale P J q).hom = x) :
    sigma (ModuleCat.{u + 1} P.Coefficient) (qQ) (G ≫ p)
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
        (cfg := compactification P (q ≫ p)) (comp P q p)) := by sorry

end AlgebraicGeometry.ProEtale
