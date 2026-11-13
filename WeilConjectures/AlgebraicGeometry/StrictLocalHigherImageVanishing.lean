/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StalkFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Detecting higher-direct-image vanishing on strict-local pullbacks

Higher direct images vanish when they vanish after pullback to the strict localizations
at geometric points.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A higher direct image vanishes exactly when the corresponding absolute cohomology
groups of all strict-local pullbacks vanish. -/
theorem isZero_rightDerived_lowerStar_iff_strict_local_ext
    (B : Type (u + 1)) [CommRing B] {Y S : Scheme.{u}} (f : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℕ) :
    IsZero (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Subsingleton (Abelian.Ext.{u + 1}
          (SemiSimplicialObject.constSheaf.{u, u + 1}
            (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology B)
          ((upperStar (ModuleCat.{u + 1} B)
            (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj M) q) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} B) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let F := lowerStar (ModuleCat.{u + 1} B) f
  let eD : (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) ≅
      higherDirectImage B f q M :=
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
  constructor
  · intro h Ω _ _ s
    have := (Scheme.pointSmallEtale s).sheafFiber_additive
      (A := ModuleCat.{u + 1} B)
    obtain ⟨e⟩ := nonempty_geometricStalk_higherDirectImage_addEquiv B f s M q
    have hz : IsZero ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} B)).obj
        (higherDirectImage B f q M)) :=
      Functor.map_isZero (Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} B))
      (h.of_iso eD.symm)
    let := ModuleCat.subsingleton_of_isZero hz
    exact e.symm.toEquiv.subsingleton
  · intro h
    have hz : IsZero (higherDirectImage B f q M) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
        (A := ModuleCat.{u + 1} B)
      intro x
      have := (Scheme.pointSmallEtale (S.algClosurePoint x)).sheafFiber_additive
        (A := ModuleCat.{u + 1} B)
      obtain ⟨e⟩ := nonempty_geometricStalk_higherDirectImage_addEquiv B f
        (S.algClosurePoint x) M q
      let := h _ (S.algClosurePoint x)
      let := e.toEquiv.subsingleton
      ext t
      exact Subsingleton.elim _ _
    exact hz.of_iso eD

end AlgebraicGeometry.Etale
