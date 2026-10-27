/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Primitive dualizing maps under compatible open restrictions

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

/-- The actual sigma, E and beta maps commute with compatible open restrictions.
The four restriction squares in the beta clause need only commute; only its
front and back base-change squares are assumed Cartesian.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
lem-pur-dualizing-sigma-cocycle-locality, proof Step 6, using Steps 1--5.

Proof: First restrict only the target. This is a Cartesian open base change;
apply the sigma tower identity of smoothExceptionalTowerPasting. Its base
pasting and identity clauses handle iterated target restriction. Restriction
only at the source is precomposition with the open immersion. Apply the
normalized source-etale identity for sigma. For beta, apply that same tower
identity with an etale first arrow, postcompose with E on the restricted
arrow, and use E sigma = eta tensor identity and eta base change from finite
etale normalization. Cancel the pulled-back sigma isomorphism. This keeps the
original lower arrow v in the square for the composite. For successive source
opens a and e substitute E = rho c; compositor associativity rewrites the two
c factors, naturality moves c past rho_a, and the composition law for rho
identifies the remaining factors with rho_ea. Thus successive E comparisons
compose with the canonical pullback compositor. A general compatible open
restriction factors through the target fibre product followed by the induced
source-open inclusion. Apply the target and source identities just proved to
these factors, and use rho composition and the canonical tensor/pullback
coherence to identify the composite comparison with the explicitly displayed
rho-c-eta expression. This proves the sigma and E clauses. Apply Cartesian
exchange pasting followed by the source-beta identity to the corresponding
factorization of the open cube to obtain the beta clause; the commuting cube
faces identify both factorizations. No arbitrary open square is declared
Cartesian. Identity opens, empty opens, and successive opens satisfy the same
identities and require no extra smoothness or separatedness hypotheses.
(blueprint: lem-pur-dualizing-primitive-open-restriction). -/
theorem dualizing_primitive_open_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqf : CommSq a f₀ f b) (sqg : CommSq b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      (((sourceEtale P a (f ≫ g)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (f ≫ g)) ((f₀ ≫ g₀) ≫ c) ((sqf.vert_comp sqg)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (f₀ ≫ g₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (f₀ ≫ g₀)).mapIso (eta P c))).hom =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (((sourceEtale P a f).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ f) (f₀ ≫ b) (sqf).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P f₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P f₀).mapIso (eta P b))).hom
      ((((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a f (f₀ ≫ b) (sqf).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b)).hom.app (omega P
        g) ≫
        (pull P f₀).map (((sourceEtale P b g).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ g) (g₀ ≫ c) (sqg).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P g₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P g₀).mapIso (eta P c))).hom) ≫
      (FiniteEtaleNormalization.sigma (ModuleCat.{u + 1} P.Coefficient)
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀))) ∧
    (∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (e₀ : X₀ ⟶ Y₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (h₀ : Y₀ ⟶ Z₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqe : CommSq a e₀ e b) (sqh : CommSq b h₀ h c),
    (pull P a).map (sourceEtale P e h).hom ≫
      (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a e (e₀ ≫ b) (sqe).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e₀ b)).hom.app (omega P
        h) ≫
      (pull P e₀).map (((sourceEtale P b h).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ h) (h₀ ≫ c) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P c))).hom =
    (((sourceEtale P a (e ≫ h)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (e ≫ h)) ((e₀ ≫ h₀) ≫ c) ((sqe.vert_comp sqh)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (e₀ ≫ h₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (e₀ ≫ h₀)).mapIso (eta P c))).hom ≫
      (sourceEtale P e₀ h₀).hom) ∧
    (∀
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [X₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
    (dh₁₀ : ℕ) [SmoothOfRelativeDimension dh₁₀ h₁₀]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [IsOpenImmersion a₁]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsOpenImmersion b₁]
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (_sqv : CommSq b₁ v₀ v b),
    (pull P a₁).map (beta P h h₁ v u sq) ≫
      (((sourceEtale P a₁ h₁).symm ≪≫
        (FiniteEtaleNormalization.congr P (a₁ ≫ h₁) (h₁₀ ≫ b₁) (sqh₁).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₁₀ b₁).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₁₀).mapIso (eta P b₁))).hom =
    (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a₁ u (u₀ ≫ a) (squ).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) u₀ a)).hom.app (omega P
        h) ≫
      (pull P u₀).map (((sourceEtale P a h).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ h) (h₀ ≫ b) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P b))).hom ≫
      beta P h₀ h₁₀ v₀ u₀ sq₀) := by sorry

end AlgebraicGeometry.ProEtale.DualizingLocality
