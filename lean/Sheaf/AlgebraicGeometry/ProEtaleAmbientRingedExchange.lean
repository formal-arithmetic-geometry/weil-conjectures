/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Ambient ringed pro-etale exchange

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-ambient-ringed-exchange.md
(blueprint: def-weil-pbc-ambient-ringed-exchange).

## Main definitions

- `proEtaleCanonicalDerivedPullbackComparison`: composition comparison with its
  normalized ordinary and K-flat representative characterizations retained.
- `proEtaleAmbientRingedExchange`: the mate of the comparison around the square.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Canonical derived pullback comparison extracted from the composition interface.
Source: Stacks Project, Lemma 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange).
The recorded composition theorem supplies this comparison together with its K-flat
normalization; this definition retains that characterization when selecting the comparison.
The adjunctions are fixed by their tensor units, the ordinary direct-image comparison
by its section formula, its pullback conjugate by the adjunctions, and the complex
comparison degreewise. The final witness retains the K-flat representative equation;
K-flat resolutions determine the comparison on every derived object.
-/
noncomputable def proEtaleCanonicalDerivedPullbackComparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z) :
    proEtaleRingDerivedPullback (h ≫ k) R_V R_Z
        (proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h) ≅
      proEtaleRingDerivedPullback k R_V R_W c_k ⋙
        proEtaleRingDerivedPullback h R_W R_Z c_h := by
  let c_hk := proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h
  have hex : ∃ (c : proEtaleRingDerivedPullback (h ≫ k) R_V R_Z c_hk ≅
                proEtaleRingDerivedPullback k R_V R_W c_k ⋙
                  proEtaleRingDerivedPullback h R_W R_Z c_h),
    ∃ (adj_k : proEtaleRingModulePullback k R_V R_W c_k ⊣
          proEtaleRingModuleDirectImage k R_V R_W c_k)
      (adj_h : proEtaleRingModulePullback h R_W R_Z c_h ⊣
          proEtaleRingModuleDirectImage h R_W R_Z c_h)
      (adj_hk : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ⊣
          proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
      proEtaleRingModuleAdjunctionNormalized k R_V R_W c_k adj_k ∧
      proEtaleRingModuleAdjunctionNormalized h R_W R_Z c_h adj_h ∧
      proEtaleRingModuleAdjunctionNormalized (h ≫ k) R_V R_Z c_hk adj_hk ∧
      ∃ (d : proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k ≅
              proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
        (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
            (m : ((proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) ∧
        ∃ (a : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ≅
              proEtaleRingModulePullback k R_V R_W c_k ⋙
                proEtaleRingModulePullback h R_W R_Z c_h),
          conjugateIsoEquiv (adj_k.comp adj_h) adj_hk a = d ∧
          ∃ (b : (proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                (ComplexShape.up ℤ) ⋙
              (proEtaleRingModulePullback h R_W R_Z c_h).mapHomologicalComplex
                (ComplexShape.up ℤ)),
            (∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ) (n : ℤ),
              (b.hom.app K).f n = a.hom.app (K.X n)) ∧
              ∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ),
                CochainComplex.IsAcyclicTensorKFlat K →
                (∀ n : ℤ,
                  SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R_V) (K.X n)) →
                CochainComplex.IsAcyclicTensorKFlat
                  (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K) ∧
                (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R_W)
                  ((((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K).X n)) ∧
                (proEtaleRingDerivedPullbackFactors (h ≫ k) R_V R_Z c_hk).hom.app K ≫
                    DerivedCategory.Q.map (b.hom.app K) =
                  c.hom.app (DerivedCategory.Q.obj K) ≫
                    (proEtaleRingDerivedPullback h R_W R_Z c_h).map
                      ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
                    (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
                      (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K) := by
    have H := proEtaleRingDerivedPullbackComposition h k R_V R_W R_Z c_k c_h c_hk rfl
    rcases H with ⟨adj_k, adj_h, adj_hk, nk, nh, nhk, d, hd, a, ha, b, hb, c, hc⟩
    exact ⟨c, adj_k, adj_h, adj_hk, nk, nh, nhk, d, hd, a, ha, b, hb, hc⟩
  exact hex.choose

/-- The canonical pullback comparison around the coefficient-compatible square.
Source: Stacks Tags 07A7 and 0D6D (blueprint: def-weil-pbc-ambient-ringed-exchange).
This exposes the exact comparison whose mate defines ambient exchange. -/
noncomputable def proEtaleAmbientRingedPullbackComparison
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'))
    : proEtaleRingDerivedPullback g R_Y R_Y' c_g ⋙
        proEtaleRingDerivedPullback f' R_Y' R_X' c_f' ≅
      proEtaleRingDerivedPullback f R_Y R_X c_f ⋙
        proEtaleRingDerivedPullback g' R_X R_X' c_g' := by
  let theta_left :=
    (proEtaleCanonicalDerivedPullbackComparison f' g R_Y R_Y' R_X' c_g c_f').symm
  let theta_right :=
    proEtaleCanonicalDerivedPullbackComparison g' f R_Y R_X R_X' c_f c_g'
  let c_fg : (proEtaleSheafInverseImage (f' ≫ g) CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'
  let P : Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    ⟨f' ≫ g, c_fg⟩
  let Q : Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    ⟨g' ≫ f, proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g'⟩
  have hPQ : P = Q := by
    apply Sigma.ext sq.toCommSq.w.symm
    exact hcoeff.symm
  let F := fun z : (Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X') ↦
    proEtaleRingDerivedPullback z.1 R_Y R_X' z.2
  have hfun := congrArg F hPQ
  let theta_left' :
      proEtaleRingDerivedPullback g R_Y R_Y' c_g ⋙
          proEtaleRingDerivedPullback f' R_Y' R_X' c_f' ≅
        proEtaleRingDerivedPullback (g' ≫ f) R_Y R_X'
          (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g') :=
    theta_left ≪≫ eqToIso hfun
  exact theta_left' ≪≫ theta_right

/-- The ambient exchange map for a cartesian square of ringed pro-etale sites.

The four coefficient isomorphisms give the identified coefficient sheaves on the
corners, and `hcoeff` records that the two composite identifications agree.  The
canonical comparison is selected from the derived pullback composition interface,
then transported across the square commutativity and coefficient compatibility.
The resulting exchange is the mate of that comparison under the two derived
pullback/direct image adjunctions.  Explicitly, its transpose is the comparison
followed by `Lg'^*` of the counit of `Lf^* ⊣ Rf_*`; the mate construction inserts
the unit of `Lf'^* ⊣ Rf'_*`.  This is the construction in Stacks, Remark 07A7
(blueprint: def-weil-pbc-ambient-ringed-exchange), before completeness or
constructibility conditions.
-/
noncomputable def proEtaleAmbientRingedExchange
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'))
    :
    proEtaleRingDerivedDirectImage f R_Y R_X c_f ⋙
          proEtaleRingDerivedPullback g R_Y R_Y' c_g ⟶
        proEtaleRingDerivedPullback g' R_X R_X' c_g' ⋙
          proEtaleRingDerivedDirectImage f' R_Y' R_X' c_f' :=
  (mateEquiv (proEtaleRingDerivedAdjunction f R_Y R_X c_f)
    (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f')
    (TwoSquare.mk _ _ _ _
      (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
        c_f c_g c_g' c_f' hcoeff).hom)).natTrans

end AlgebraicGeometry.Scheme
