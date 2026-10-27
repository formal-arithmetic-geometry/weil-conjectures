/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Dualizing tensor associativity and normalized etale source compatibility

Source: thm-pur-composition-coherence, proof Step 1, and the indicated steps
of lem-pur-dualizing-sigma-cocycle-locality. The statement expands the existing
locality predicates to keep this proof dependency independent of its consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DualizingLocality
open FiniteEtaleNormalization

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- For a smooth triple the canonical sigma maps satisfy the cocycle, and for
an etale first arrow the cocycle induces the normalized source-etale identity.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
lem-pur-dualizing-sigma-cocycle-locality, proof Steps 1--3.

Proof: Write G_f = Rf! and c for the specified exceptional compositor.
Transport compact-support associativity through the adjunction conjugation
bijection and mate pasting. This identifies the two maps from omega_fgh to
G_f G_g omega_h. Apply composition_tensor_mate at K = omega_h; its finite-Tor
domain clauses justify this input. After postcomposition with the common
threefold exceptional compositor, its tensor identity is exactly the left
cocycle route. For the right route use naturality of theta_f with respect to
c_g,h at the coefficient unit. Substitute c sigma = theta with the prescribed
symmetry. The two routes then coincide by the same tensor-mate identity;
the canonical reassociations are supplied by smooth exceptional tensor pasting.
Cancel the common isomorphism to obtain the first assertion. If f is etale,
postcompose this cocycle with E_f,gh and substitute the finite-etale
normalization equations E_f,k sigma_f,k = eta_f tensor identity, for k = g
and k = gh. Naturality of the tensor unit and the pullback tensor comparison
move eta_f past the right route. Cancel sigma_f,g tensor identity, which is
invertible by the smooth tensor formula. The result is exactly the second
assertion, including its displayed pullback compositor and inverse tensor
comparison. Identity arrows, relative dimension zero, and empty schemes use
the same equations and cancellation; no nonemptiness assumption is needed.
(blueprint: lem-pur-dualizing-cocycle-source-etale). -/
theorem dualizing_cocycle_source_etale
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h],
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        ((FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) (𝟙 ((pull P (f ≫ g)).obj (omega P h))) ≫
      (FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
        (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
          (Category.assoc f g h)).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) S
      (omega P f) ((pull P f).obj (omega P g))
        ((pull P (f ≫ g)).obj (omega P h))).hom ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) S).obj (omega P f)).map
      (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 _)
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
            (omega P h)) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
          (omega P g) ((pull P g).obj (omega P h))).inv ≫
        (pull P f).map ((FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) ≫
      (FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      f (g ≫ h) (cf := compactification P f)
      (cg := compactification P (g ≫ h))
      (cfg := compactification P (f ≫ (g ≫ h)))
      (comp P f (g ≫ h)))) ∧
    (∀
    {S X Y Z : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    [Etale f],
    (FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      (f ≫ g) h (cf := compactification P (f ≫ g))
      (cg := compactification P h)
      (cfg := compactification P ((f ≫ g) ≫ h))
      (comp P (f ≫ g) h)) ≫
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ h) (f ≫ g ≫ h)
        (Category.assoc f g h)).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
      (sourceEtale P f (g ≫ h)).hom =
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        (sourceEtale P f g).hom
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).hom.app
          (omega P h)) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f
        (omega P g) ((pull P g).obj (omega P h))).inv ≫
      (pull P f).map ((FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      g h (cf := compactification P g)
      (cg := compactification P h)
      (cfg := compactification P (g ≫ h))
      (comp P g h)))) := by sorry

end AlgebraicGeometry.ProEtale.DualizingLocality
