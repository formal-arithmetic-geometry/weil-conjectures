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

/-! # Restriction compatibility for the proper-flat right adjoint

Source: literature/stacks-project/duality.tex, Tag 0E4J (Lemma 48.12.2), part (2)
(blueprint: lem-sc-proper-flat-right-adjoint-restriction-open).
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
