/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NB and W3
-/
module

public import Sheaf.Paper.RingedLocalizationModels
import Sheaf.Paper.RingedModelCurryingCoherence
import Sheaf.Paper.RingedLocalizationCurrying
import Sheaf.Paper.RingedLocalizationRestriction

/-! # Localization and derived internal Hom

Source: Stacks Project, Tags 08J9, 08JB and 0996.
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Restriction and currying for bounded localization complexes, with simultaneous
naturality and compatibility with every further slice restriction. The data e and s
are the ordinary derived internal-Hom restriction comparisons. The maps l and t identify
restricted coefficient localizations and their ordinary tensor complexes. The final
square says that restricting currying equals currying after restriction.

Source: Stacks 08J9, 08JB; Algebraization of Formal Spaces 0996
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
Proof:
1. Choose a K-injective representative I of N (prop-pur-kinjective-resolutions-exist).
   It stays K-injective on slices (lem-pur-kinjective-restrict-localized). On W over U,
   the Hom complexes before and after restriction have identical factors and differential
   d_I phi - (-1)^n phi d_P (def-pur-hom-complex). This gives e and s.
2. Apply ringedLocalization_kflat_models. Both the restricted P and the coefficient
   in degree zero are K-flat, and P_f is their ordinary total tensor.
3. Hom(P|U,I|U) is K-injective by lem-pur-hom-kflat-into-kinjective. Thus the two sides
   of currying are represented by Hom(S[0],Hom(P|U,I|U)) and Hom(P_f,I|U).
4. Apply lem-sc-derived-hom-tensor-total: the map evaluates phi(s)(p), with inverse
   currying. Since S is in degree zero, its differential is precisely the displayed Hom
   differential on both sides. Localizing gives c.
5. Precomposition in P and postcomposition in I commute with evaluation. Functorial
   resolutions and def-pur-derived-internal-hom descend this to every derived morphism
   of N, yielding the naturality equation.
6. Fraction maps identify the coefficient localizations under further slice restriction;
   tensoring identifies their complexes. On W over V both comparison routes evaluate
   the identical expression phi(s)(p); relocalization is the identity on the same section
   families (def-pur-localized-ringed-site). This proves the last square. The analogous
   identity for e and s is ringedInternalHom_restriction. No bound on N is used. -/
theorem ringedLocalizationRHom_calculus (R : Sheaf J CommRingCat.{u}) :
    ∃ (e : ∀ U : C,
      localizationRHom R ⋙ localizationDerivedRestriction R U ≅
        ((localizationDerivedRestriction R U).op.prod
          (localizationDerivedRestriction R U)) ⋙ localizationRHom (R.over U))
      (s : ∀ (U V : C) (a : V ⟶ U),
        localizationRHom (R.over U) ⋙ localizationDerivedOverMap R a ≅
          ((localizationDerivedOverMap R a).op.prod (localizationDerivedOverMap R a)) ⋙
            localizationRHom (R.over V))
      (c : ∀ (U : C) (f : R.obj.obj (op U))
        (P : CochainComplex (localizationModules R) ℤ), IsBoundedLocalizationComplex R P →
        ∀ N : localizationDerived R,
        (localizationRHom (R.over U)).obj
          (op (localizationSliceDerivedCoefficient R U f),
            (localizationRHom (R.over U)).obj
              (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                (localizationDerivedRestriction R U).obj N)) ≅
        (localizationRHom (R.over U)).obj
          (op ((localizationQ (R.over U)).obj ((localizationSliceComplex R U f).obj P)),
            (localizationDerivedRestriction R U).obj N)),
      (∀ (U V : C) (a : V ⟶ U) (L M : localizationDerived R),
        (localizationDerivedOverMap R a).map ((e U).hom.app (op L, M)) ≫
          (s U V a).hom.app
            (op ((localizationDerivedRestriction R U).obj L),
              (localizationDerivedRestriction R U).obj M) ≫
          (localizationRHom (R.over V)).map
            (X := (op ((localizationDerivedOverMap R a).obj
              ((localizationDerivedRestriction R U).obj L)),
              (localizationDerivedOverMap R a).obj
                ((localizationDerivedRestriction R U).obj M)))
            (Y := (op ((localizationDerivedRestriction R V).obj L),
              (localizationDerivedRestriction R V).obj M))
            (((localizationRestrictionCompIso R a).inv.app L).op,
              (localizationRestrictionCompIso R a).hom.app M) =
        (localizationRestrictionCompIso R a).hom.app
          ((localizationRHom R).obj (op L, M)) ≫ (e V).hom.app (op L, M)) ∧
      (∀ (U : C) (f : R.obj.obj (op U))
        (P P' : CochainComplex (localizationModules R) ℤ)
        (hP : IsBoundedLocalizationComplex R P) (hP' : IsBoundedLocalizationComplex R P')
        (a : P' ⟶ P) (N N' : localizationDerived R) (b : N ⟶ N'),
        (c U f P hP N).hom ≫ (localizationRHom (R.over U)).map
          (((localizationQ (R.over U)).map ((localizationSliceComplex R U f).map a)).op,
            (localizationDerivedRestriction R U).map b) =
        (localizationRHom (R.over U)).map
          (𝟙 (op (localizationSliceDerivedCoefficient R U f)),
            (localizationRHom (R.over U)).map
              (((localizationDerivedRestriction R U).map ((localizationQ R).map a)).op,
                (localizationDerivedRestriction R U).map b)) ≫ (c U f P' hP' N').hom) ∧
      ∀ (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)),
        ∃ (l : (localizationDerivedOverMap R a).obj
              (localizationSliceDerivedCoefficient R U f) ≅
            localizationSliceDerivedCoefficient R V (R.obj.map a.op f))
          (t : localizationSliceComplex R U f ⋙ localizationQ (R.over U) ⋙
              localizationDerivedOverMap R a ≅
            localizationSliceComplex R V (R.obj.map a.op f) ⋙ localizationQ (R.over V)),
          ∀ (P : CochainComplex (localizationModules R) ℤ)
            (hP : IsBoundedLocalizationComplex R P) (N : localizationDerived R),
          (localizationDerivedOverMap R a).map ((c U f P hP N).hom) ≫
            (s U V a).hom.app
              (op ((localizationQ (R.over U)).obj ((localizationSliceComplex R U f).obj P)),
                (localizationDerivedRestriction R U).obj N) ≫
            (localizationRHom (R.over V)).map
              (X := (op ((localizationDerivedOverMap R a).obj
                ((localizationQ (R.over U)).obj ((localizationSliceComplex R U f).obj P))),
                (localizationDerivedOverMap R a).obj
                  ((localizationDerivedRestriction R U).obj N)))
              (Y := (op ((localizationQ (R.over V)).obj
                ((localizationSliceComplex R V (R.obj.map a.op f)).obj P)),
                (localizationDerivedRestriction R V).obj N))
              ((t.inv.app P).op, (localizationRestrictionCompIso R a).hom.app N) =
          (s U V a).hom.app
            (op (localizationSliceDerivedCoefficient R U f),
              (localizationRHom (R.over U)).obj
                (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                  (localizationDerivedRestriction R U).obj N)) ≫
            (localizationRHom (R.over V)).map
              (X := (op ((localizationDerivedOverMap R a).obj
                (localizationSliceDerivedCoefficient R U f)),
                (localizationDerivedOverMap R a).obj ((localizationRHom (R.over U)).obj
                  (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R U).obj N))))
              (Y := (op (localizationSliceDerivedCoefficient R V (R.obj.map a.op f)),
                (localizationRHom (R.over V)).obj
                  (op ((localizationDerivedRestriction R V).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R V).obj N)))
              (l.inv.op,
                (s U V a).hom.app
                  (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R U).obj N) ≫
                (localizationRHom (R.over V)).map
                  (X := (op ((localizationDerivedOverMap R a).obj
                    ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P))),
                    (localizationDerivedOverMap R a).obj
                      ((localizationDerivedRestriction R U).obj N)))
                  (Y := (op ((localizationDerivedRestriction R V).obj ((localizationQ R).obj P)),
                    (localizationDerivedRestriction R V).obj N))
                  (((localizationRestrictionCompIso R a).inv.app ((localizationQ R).obj P)).op,
                    (localizationRestrictionCompIso R a).hom.app N)) ≫
            (c V (R.obj.map a.op f) P hP N).hom := by
  obtain ⟨e, s, he, hs⟩ := LocalizationRHom.modelCurrying_restriction R
  refine ⟨e, s, LocalizationRHom.curryIso R, he, ?_, ?_⟩
  · exact LocalizationRHom.curryIso_natural R
  · intro U V a f
    let S := localizationSliceCoefficient R U f
    let T := localizationSliceCoefficient R V (R.obj.map a.op f)
    let ξ := LocalizationRHom.coefficientSheafIso R a f
    refine ⟨LocalizationRHom.derivedCoefficientIso R a S T ξ,
      LocalizationRHom.coefficientDerivedComplexIso R a S T ξ, ?_⟩
    intro P hP N
    simpa only [LocalizationRHom.curryIso_eq_model] using
      hs U V a S T ξ (localizationSliceCoefficient_kflat R U f)
        (localizationSliceCoefficient_kflat R V (R.obj.map a.op f)) P
        (ringedLocalization_kflat_models R P hP U f).1
        (ringedLocalization_kflat_models R P hP V (R.obj.map a.op f)).1 N

end CategoryTheory
