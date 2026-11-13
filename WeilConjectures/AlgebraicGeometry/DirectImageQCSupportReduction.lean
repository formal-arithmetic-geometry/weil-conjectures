/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian

/-!
# Quasi-compact reduction for a proper-support complex

Source: Stacks Project, Tag 08EV.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Derived restriction and composition expand large localization and scalar-restriction terms.
-- Coherence is redundant because proper-support hypotheses already include closedness.
set_option linter.unusedVariables false in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A quasi-compact open containing every cohomological support preserves the derived
 direct image via the adjunction unit and the canonical composition comparison.
(Stacks, Tag 08EV) -/
theorem directImage_qc_support_reduction
    {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsNoetherian S]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E))
    (hcoherent : ∀ n : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E))
    (hsupport : ∀ n : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E)) :
    ∃ U : X.Opens,
      IsCompact (U : Set X) ∧ QuasiCompact U.ι ∧
      QuasiCompact (U.ι ≫ f) ∧ QuasiSeparated (U.ι ≫ f) ∧
      (∀ (n : ℤ) (x : X),
        ¬ Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x) →
        x ∈ U) ∧
      ∃ (_ : (Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)).Additive),
      ∃ adj :
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι,
      ∃ c : schemeDerivedDirectImage U.ι ⋙ schemeDerivedDirectImage f ≅
          schemeDerivedDirectImage (U.ι ≫ f),
        (∀ K : HomotopyCategory
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (ComplexShape.up ℤ),
          (RingedSpace.moduleDirectImage (U.ι ≫ f).toLRSHom.toShHom).rightDerivedFunctorUnit.app
              K ≫ c.inv.app (DerivedCategory.Qh.obj K) =
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
                (((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj K) ≫
              (schemeDerivedDirectImage f).map
                ((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerivedFunctorUnit.app
                  K)) ∧
        IsIso ((schemeDerivedDirectImage f).map (adj.unit.app E) ≫
          c.hom.app
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
              Equivalence.functor
                (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E)) ∧
        Nonempty ((schemeDerivedDirectImage (U.ι ≫ f)).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
              Equivalence.functor
                (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E) ≅
          (schemeDerivedDirectImage f).obj E) := by
  classical
  let a := hbounded.choose
  let b := hbounded.choose_spec.choose
  have hab := hbounded.choose_spec.choose_spec
  choose Z hZ hpZ using hsupport
  let I := {n : ℤ // n ∈ Finset.Icc a b}
  let e := Fintype.equivFin I
  let W : Fin (Fintype.card I) → TopologicalSpace.Closeds X :=
    fun i ↦ Z (e.symm i).val
  let T : TopologicalSpace.Closeds X := ⨆ i, W i
  have hpT : Scheme.IsClosedSubsetProperOver f T :=
    (Scheme.isClosedSubsetProperOver_union_preimage f).1 _ W (fun i ↦ hpZ _)
  have hsT (n : ℤ) (x : X)
      (hx : ¬ Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x)) :
      x ∈ T := by
    by_cases hn : n ∈ Finset.Icc a b
    · have hxZ : x ∈ Z n := by
        change x ∈ (Z n : Set X)
        rw [hZ n]
        exact hx
      have hi := le_iSup W (e ⟨n, hn⟩)
      apply hi
      simpa [W] using hxZ
    · have hn' : n < a ∨ b < n := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hn
      have h₁ := (SheafOfModules.forget (moduleRings X.toRingedSpace)).map_isZero
        (hab n hn')
      have h₂ := (PresheafOfModules.toPresheaf
        (moduleRings X.toRingedSpace).obj).map_isZero h₁
      exact (hx (AddCommGrpCat.subsingleton_of_isZero
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_isZero h₂))).elim
  let i := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  have : IsProper (i ≫ f) := hpT
  let : CompactSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ f)
  have hshrink := i.exists_isCompact_isClosedImmersion
  let U := hshrink.choose
  let g := hshrink.choose_spec.choose
  have hUc := hshrink.choose_spec.choose_spec.1
  have hg := hshrink.choose_spec.choose_spec.2.1
  have hgi := hshrink.choose_spec.choose_spec.2.2
  have hTU : (T : Set X) ⊆ (U : Set X) := by
    have hi : Set.range i = (T : Set X) := by simp [i]
    rw [← hi]
    rintro x ⟨y, rfl⟩
    rw [← hgi]
    exact (g y).property
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have hUqc : QuasiCompact U.ι := inferInstance
  have hfqc : QuasiCompact (U.ι ≫ f) := inferInstance
  have hfqs : QuasiSeparated (U.ι ≫ f) := inferInstance
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let adj0 : (schemeOpenRestriction X U) ⊣
      RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  let adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣
      schemeDerivedDirectImage U.ι := adj0.mapDerivedCategoryRightDerivedAdjunction
  let hO := Classical.choice (nonempty_derivedOpenLocalization X)
  let := hO
  let hOU := Classical.choice (nonempty_derivedOpenLocalization U.toScheme)
  let := hOU
  have hunit : IsIso (adj.unit.app E) :=
    (Scheme.supported_open_pushforward X U T T.isClosed hTU).2.1 adj E (by
      intro n x hx
      by_contra h
      exact hx (hsT n x h))
  have hcomp := RingedSpace.exists_derivedModuleDirectImageComposition
    U.ι.toLRSHom.toShHom f.toLRSHom.toShHom
  let c := hcomp.choose
  have hc := hcomp.choose_spec
  refine ⟨U, hUc, hUqc, hfqc, hfqs, (fun n x hx ↦ hTU (hsT n x hx)),
    inferInstance, adj, c, hc, ?_, ?_⟩
  · infer_instance
  · exact ⟨(asIso ((schemeDerivedDirectImage f).map (adj.unit.app E) ≫
      c.hom.app ((schemeOpenRestriction X U).mapDerivedCategory.obj E))).symm⟩

end AlgebraicGeometry
