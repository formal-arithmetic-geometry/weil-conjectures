/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport
import Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian

/-! # Restriction compatibility for the proper-flat right adjoint

Source: literature/stacks-project/duality.tex, Tag 0E4J (Lemma 48.12.2), part (2)
(blueprint: lem-sc-proper-flat-right-adjoint-restriction-open).
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Exact restriction commutes with homology; sheaf sections are detected by their germs.
private theorem restriction_zero_iff_stalks
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) (K : schemeDerivedCategory X) :
    IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ↔
      ∀ (n : ℤ) (x : X), x ∈ U →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x)) :=
  set_option synthInstance.maxSize 2048 in by
  let : Zero (schemeDerivedCategory U.toScheme) := HasZeroObject.zero' _
  let L := schemeOpenRestriction X U
  constructor
  · intro hK n x hx
    let H := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
    have hLH : IsZero (L.obj H) :=
      ((DerivedCategory.homologyFunctor _ n).map_isZero hK).of_iso
        ((L.mapDerivedCategoryHomologyFunctorIso n).app K)
    let e : L.obj H ≅ (Scheme.Modules.restrictFunctor U.ι).obj H :=
      (Scheme.Modules.overFunctorEquiv U).app H
    have hRH := hLH.of_iso e.symm
    let F := Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : U)
    have : (Scheme.Modules.toPresheaf U.toScheme).Additive := ⟨by intros; rfl⟩
    have : F.Additive := by dsimp [F]; infer_instance
    have hz := F.map_isZero hRH
    let eStalk := (Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U)).app H
    exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso eStalk.symm)
  · intro hK
    have hz (n : ℤ) : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj
          (L.mapDerivedCategory.obj K)) := by
      let H := (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
      have hR : IsZero ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).obj H) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        ext V z
        change z = 0
        apply TopCat.Presheaf.section_ext
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj H)
        intro x hx
        change TopCat.Presheaf.germ H.val.presheaf _ x hx _ =
          TopCat.Presheaf.germ H.val.presheaf _ x hx _
        exact (hK n x (leOfHom V.unop.hom hx)).elim _ _
      have hLH : IsZero (L.obj H) :=
        (Scheme.Modules.overEquiv U).functor.map_isZero hR
      exact hLH.of_iso ((L.mapDerivedCategoryHomologyFunctorIso n).app K).symm
    have hi : IsIso (0 : L.mapDerivedCategory.obj K ⟶ 0) :=
      (DerivedCategory.isIso_iff _ _).mpr (fun n ↦
        IsZero.isIso (hz n) ((DerivedCategory.homologyFunctor _ n).map_isZero
          (isZero_zero _)) _)
    exact (isZero_zero _).of_iso (asIso (0 : L.mapDerivedCategory.obj K ⟶ 0))

-- Apply all three clauses of the support criterion to the canonical lift of Rf_*.
private theorem restriction_unit_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (V : Y.Opens) (hV : IsCompact (V : Set Y))
    (adjV : (schemeOpenRestriction Y V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (hopen : ∀ K : schemeDerivedQCohCategory Y, schemeDerivedQCohProperty Y
      ((schemeDerivedDirectImage V.ι).obj
        ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj)))
    (K : schemeDerivedQCohCategory Y) :
    IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.map
      ((schemeDerivedQCohProperty X).ι.map (a.map (ObjectProperty.homMk (X := K)
        (Y := ⟨(schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj), hopen K⟩)
        (adjV.unit.app K.obj))))) := set_option synthInstance.maxSize 2048 in by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  -- The supplied identification already gives quasi-coherence of the ambient image.
  let hpush : ∀ E : schemeDerivedQCohCategory X, schemeDerivedQCohProperty Y
      ((schemeDerivedDirectImage f).obj E.obj) :=
    fun E n ↦ (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso (hF.app E)) ((F.obj E).property n)
  let F₀ := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush
  let e : F ≅ F₀ := Functor.fullyFaithfulCancelRight (schemeDerivedQCohProperty Y).ι
    (hF ≪≫ ((schemeDerivedQCohProperty Y).liftCompιIso _ hpush).symm)
  let adj₀ : F₀ ⊣ a := adj.ofNatIsoLeft e
  -- Transport only the left adjoint: the functor a and its open-unit map stay fixed.
  have hc := rightAdjoint_open_support_criterion f V hV (f ⁻¹ᵁ V) rfl
    hpush a adj₀ adjV hopen
  have hs := proper_flat_rightAdjoint_preservesDirectSums f F hF a adj
  apply (hc.2.2 hs).mp
  apply hc.1.mpr
  intro Q _ hQ
  apply (restriction_zero_iff_stalks X (f ⁻¹ᵁ V) (a.obj Q).obj).mpr
  exact proper_flat_rightAdjoint_open_support f F hF a adj V hV Q
    ((restriction_zero_iff_stalks Y V Q.obj).mp hQ)

/-- For a proper, flat, finitely presented morphism `f : X ⟶ Y` of a qcqs base and its base
change `f' = pullback.snd f g` along `g : Y' ⟶ Y`, the right adjoints `a`, `a'` of the derived
direct images on `D_QCoh` are compatible with restriction to every quasi-compact open of
either base. `F` (resp. `F'`) is `Rf_*` (resp. `Rf'_*`) on `D_QCoh`, identified with the
recorded ambient direct image by `hF` (resp. `hF'`). The canonical open-square map
`j_U^* a(K) ⟶ a_V(Lj^* K)` (Stacks, duality.tex, equation-sheafy) is an isomorphism exactly
when the restriction to `U = f⁻¹(V)` of `a(K ⟶ Rj_* j^* K)` (the unit of `adjV`) is one;
the statement says the latter for every `K` in `D_QCoh(Y)`, in the form of
`rightAdjoint_open_support_criterion` (lem-sc-right-adjoint-open-support-criterion).
`hV` records that `Rj_* j^* K` is quasi-coherent, so that `a` applies to it.
Source: literature/stacks-project/duality.tex, Tag 0E4J (Lemma 48.12.2), part (2)
(blueprint: lem-sc-proper-flat-right-adjoint-restriction-open).

Proof:
1. The open-support criterion (lem-sc-right-adjoint-open-support-criterion), together with
   direct-sum preservation (lem-sc-proper-flat-right-adjoint-direct-sums), reduces the claim
   to support preservation for bounded-below complexes.
2. Proper-flat support preservation (lem-sc-proper-flat-right-adjoint-open-support) gives
   the required isomorphism over a quasi-compact open.
3. Properness, flatness, and finite presentation are stable under base change, so the same
   argument applies to the cartesian base-change morphism and to opens in the second base.
-/
theorem proper_flat_rightAdjoint_restriction_open
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (F' : schemeDerivedQCohCategory (pullback f g) ⥤ schemeDerivedQCohCategory Y')
    (hF' : F' ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y') ≅
      ObjectProperty.ι (schemeDerivedQCohProperty (pullback f g)) ⋙
        schemeDerivedDirectImage (pullback.snd f g))
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adj' : F' ⊣ a') :
    (∀ (V : Y.Opens) (_ : IsCompact (V : Set Y))
      (adjV : (schemeOpenRestriction Y V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (hV : ∀ K : schemeDerivedQCohCategory Y, schemeDerivedQCohProperty Y
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj)))
      (K : schemeDerivedQCohCategory Y),
      IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.map
        ((schemeDerivedQCohProperty X).ι.map (a.map (ObjectProperty.homMk (X := K)
          (Y := ⟨(schemeDerivedDirectImage V.ι).obj
            ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj), hV K⟩)
          (adjV.unit.app K.obj)))))) ∧
    (∀ (V' : Y'.Opens) (_ : IsCompact (V' : Set Y'))
      (adjV' : (schemeOpenRestriction Y' V').mapDerivedCategory ⊣
        schemeDerivedDirectImage V'.ι)
      (hV' : ∀ K' : schemeDerivedQCohCategory Y', schemeDerivedQCohProperty Y'
        ((schemeDerivedDirectImage V'.ι).obj
          ((schemeOpenRestriction Y' V').mapDerivedCategory.obj K'.obj)))
      (K' : schemeDerivedQCohCategory Y'),
      IsIso ((schemeOpenRestriction (pullback f g)
          ((pullback.snd f g) ⁻¹ᵁ V')).mapDerivedCategory.map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map (a'.map (ObjectProperty.homMk
          (X := K')
          (Y := ⟨(schemeDerivedDirectImage V'.ι).obj
            ((schemeOpenRestriction Y' V').mapDerivedCategory.obj K'.obj), hV' K'⟩)
          (adjV'.unit.app K'.obj)))))) := by
  constructor
  · intro V hV adjV hV' K
    exact restriction_unit_isIso f F hF a adj V hV adjV hV' K
  · intro V' hV' adjV' hV'' K'
    exact restriction_unit_isIso (pullback.snd f g) F' hF' a' adj'
      V' hV' adjV' hV'' K'

end AlgebraicGeometry
