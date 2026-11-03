/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence

import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportComparisonAgreement

/-!
# Identity evaluation of the specified finite exceptional Hom chain

Source: current blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 4,
the normalized finite counit paragraph
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation).

The positive coefficient level is n+1. All arrows are in the ordinary fixed-scalar
pro-etale derived category. The retained origin below is the standard right-adjoint
representative after the fixedExceptionalIso identification; compact support is
transported by the published origin comparison, with its direction displayed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f) (n : ℕ)

/-- The standard bounded-below etale representative H of the exceptional inverse image.
It is the existing etale right adjoint applied to R-nu-star L, using c only to supply
compactifiability. No representative is selected from a bare existence assertion.
Source: current blueprint finite reduction of purity, Step 4, identity evaluation
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation). -/
def finiteCounitEtaleOrigin
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
  letI := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  ⟨(Etale.rightDerivedUpperShriek
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) f).obj
        ((ProEtale.comparisonLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))) Y).rightDerivedFunctor.obj L.obj),
    ProEtale.plus_etaleRightDerivedUpperShriek_obj f L.property⟩

/-- The comparison pullback C H, with its derived bounded-below structure retained.
Source: current blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation). -/
def finiteCounitSource
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))) :
    DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategoryPlus.obj
        (finiteCounitEtaleOrigin l E D f c n L)

/-- The literal retained pair (H,id), in the dependency's witness structure.
Source: current blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation). -/
def finiteCounitOriginWitness
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))) :
    FixedEtaleOriginWitness X
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
        (finiteCounitSource l E D f c n L) :=
  ⟨finiteCounitEtaleOrigin l E D f c n L, Iso.refl _⟩

/-- The published bounded-below counit, expressed at c by the inverse of the published
compactification origin comparison. This is an actual composite of the named maps.
Source: current blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation). -/
def finitePublishedCounitAt
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))) :
    (ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      (finiteCounitSource l E D f c n L).obj ⟶ L.obj :=
  letI := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  (ProEtale.rightDerivedLowerShriekCompactificationIso
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).inv.app
        (finiteCounitEtaleOrigin l E D f c n L) ≫
    ProEtale.rightDerivedUpperShriekCounit f L.obj L.property

set_option maxHeartbeats 1600000 in
-- Inverting the six Hom factors requires reduction across the derived-category inclusions.
include hl Xbase Ybase Xft Xqc Yft Yqc Xsep Ysep fbase fsep fft fqc in
/-- Identity evaluation of the six-factor chain, after the fixedExceptionalIso
right-adjoint comparison, is the published counit under the canonical compact-support
identification. The equality precedes every constructible or finite-Tor restriction.

Source: current blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 4,
normalized finite counit paragraph
(blueprint: lem-route-finite-exceptional-hom-counit-evaluation).

Proof: (1) R-nu-star preserves a lower bound. The standard ordinary etale right adjoint
preserves a lower bound on the quasi-compact target; right-adjoint uniqueness transfers
this to the specified right adjoint at c. Exact comparison pullback preserves D+.
(2) For the retained pair (M_e,id), the witness factors are identities and full
faithfulness sends id to id. The inverse ordinary adjunction factor sends id to its
counit. The inverse comparison adjunction appends its counit, and the inverse support
factor prepends fixedCompactSupportComparisonIso. Thus the raw inverse image is
kappa_c(M_e);C_Y(epsilon_c);epsilon_nu.
(3) Write H for the standard etale right-adjoint representative. The etale
rightAdjointUniq underlying fixedExceptionalIso identifies H with M_e and respects
counits. (4) Naturality of kappa_c moves this identification across compact support,
leaving kappa_c(H);C_Y(tau_H);C_Y(epsilon_0);epsilon_nu.
(5) lem-route-finite-compact-support-comparison-agreement identifies the first two
factors with the published compactification origin comparison followed by the
published rightDerivedLowerShriekComparisonIso at H. The last two factors are exactly
the remaining factors of rightDerivedUpperShriekCounit. (6) In fixedHom, the inverse
fixedExceptionalIso cancels the preceding right-adjoint comparison, so the forward
image of this arrow is id and its inverse image of id is the displayed arrow.
For the standing compactification the compact-support identification is the identity.
Zero objects, empty schemes, and the first positive coefficient level are included. -/
theorem finiteExceptionalHom_counit
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))) :
    (fixedHom l E D f c n (finiteCounitSource l E D f c n L)
      (finiteCounitOriginWitness l E D f c n L) L).symm
        (𝟙 (finiteCounitSource l E D f c n L).obj) =
      finitePublishedCounitAt l E D f c n L := by
  let := c.hasCompactification
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let N := finiteCounitEtaleOrigin l E D f c n L
  let c₀ := HasCompactification.compactification f
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  have ht : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c c₀).hom.app N =
      (Etale.rightDerivedLowerShriekIso A c).hom.app N.obj := by
    have h := Etale.unboundedEtaleCompactSupport_comparison_plus A f c c₀ N
    apply (cancel_epi
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app N)).1
    simpa only [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc,
      Etale.rightDerivedLowerShriekIso, c₀, Functor.comp_obj,
      DerivedCategory.Plus.ι, ObjectProperty.ι_obj] using h
  have hk := (ProEtale.finiteCompactSupportComparisonAgreement D.k
    (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) f A c c₀).1
  have hi : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c).inv.app N =
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c c₀).hom.app N := by
    change ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c).symm).hom.app N = _
    simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_symm,
      Functor.isoWhiskerRight_symm, Iso.symm_symm_eq,
      Etale.rightDerivedLowerShriekOfCompactificationPlusIso_symm, Iso.trans_assoc]
  have hs : (ProEtale.rightDerivedLowerShriekCompactificationIso A c).inv.app N ≫
      (ProEtale.rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} A) f).hom.app N =
      (ProEtale.fixedCompactSupportComparisonIso A c).hom.app N ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekIso A c).hom.app N.obj) := by
    simp only [ProEtale.rightDerivedLowerShriekCompactificationIso,
      ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso,
      ProEtale.rightDerivedLowerShriekComparisonIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
      Category.assoc]
    rw [show (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
      (HasCompactification.compactification f) c).inv.app N =
        (Etale.rightDerivedLowerShriekIso A c).hom.app N.obj from hi.trans ht, hk]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  simp only [fixedHom, Equiv.symm_trans_apply, Iso.homToEquiv_symm_apply,
    fixedExceptionalIso, Iso.app_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ProEtale.specifiedExceptionalHomEquiv, finiteCounitOriginWitness,
    Iso.homFromEquiv_symm_apply, Iso.symm_hom, Functor.mapIso_refl,
    Iso.refl_inv, Category.id_comp]
  erw [Category.id_comp, Iso.homFromEquiv_symm_apply, Iso.homFromEquiv_symm_apply,
    Iso.refl_hom, Category.id_comp]
  change (ProEtale.fixedCompactSupportComparisonIso A c).hom.app N ≫
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ _).symm
      (((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)).homEquiv
        _ _).symm ((Equiv.ofBijective _ _).symm
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
            (((Etale.rightDerivedUpperShriekAdjunctionOfCompactification A c).rightAdjointUniq
              (Adjunction.ofIsLeftAdjoint
                (Etale.rightDerivedLowerShriekOfCompactification
                  (ModuleCat.{u + 1} A) c))).hom.app _)))) = _
  erw [Equiv.ofBijective_symm_apply_apply,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_symm_apply,
    Etale.rightDerivedUpperShriekAdjunctionOfCompactification,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_inv, Functor.map_comp, Category.assoc]
  have h := congrArg (fun a ↦ a ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.obj L.obj)) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app L.obj) hs.symm
  simpa only [finitePublishedCounitAt, ProEtale.rightDerivedUpperShriekCounit,
    Category.assoc, Functor.id_obj, Iso.app_hom, N, finiteCounitEtaleOrigin, A] using h

end WeilConjectures.FiniteExceptional
