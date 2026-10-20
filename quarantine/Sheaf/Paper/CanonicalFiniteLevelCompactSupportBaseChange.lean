/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.SecSmoothPurity.CanonicalShriekExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Compact-support base change in fixed module coordinates

Source: blueprint main-20261015, thm-cbc-finite-level-proetale
(blueprint: thm-cbc-finite-level-proetale).

The original global compactification theorem is reexported unchanged. The additional
clause identifies its invertible transported exchange with the actual proper/open
mate on fixed module sheaves, at the same retained etale-origin witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Invertibility of the actual auxiliary exchange at the retained origin.
Source: blueprint thm-cbc-finite-level-proetale, the specified transported exchange;
its identification in pur9-cs-def-bc (blueprint: thm-cbc-finite-level-proetale).

Proof: apply thm-cbc-finite-level-proetale to the supplied compactification and W.
Its proper input is j_!M, with antecedent j-et_!W.complex, transported by the exact
open-extension comparison and j_!W.iso. Properness of both proper factors gives qcqs.
The lemma lem-weil-pbc-transport-identifies-exchange identifies the proper factor:
both raw and transported maps are the derived unit-square-counit mate of the same
composition isomorphism. The open factor is identified by the termwise exact
extension-zero comparison; the two identifications restrict to the same map on the
open, hence agree by the open-extension adjunction. Thus the auxiliary exchange is
exactly the isomorphism of thm-cbc-finite-level-proetale, after the canonical coefficient
realization and the exact-pullback/left-derived-pullback comparisons. -/
theorem isIso_csAuxiliaryExchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : ChosenCartesianSquare g' f' f g) (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))
    (_W : Scheme.FixedEtaleOriginWitness X
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) M) :
    IsIso ((canonicalFiniteCoefficientCompactSupportExchange l E n hn sq c).app M.obj) := by
  let Λ := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have : Finite Λ :=
    Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  let hsq : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M.obj := by
    refine ⟨_W.complex.obj, _W.complex.property, ⟨_W.iso⟩⟩
  have : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (c.isPullback_g_ofIsPullback hsq).flip.toCommSq).app
        (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj M.obj)) :=
    isIso_derivedBaseChangeMap_app_openImmersionLowerShriek_of_compactification
      Λ hsq c M.obj hM
  apply NatTrans.isIso_app_comp_whiskerLeft_comp

end AlgebraicGeometry.ProEtale
