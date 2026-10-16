/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-!
# Localization complexes and derived internal Hom on a ringed site

Source: Stacks Project, Cohomology on Sites, Tags 08J9 and 08JB;
Algebraization of Formal Spaces, Tag 0996
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

/-- Transparent size convention for the existing module category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The existing unbounded derived category, at its standard localization size.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerived (R : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The existing localization functor with the same size convention.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationQ (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (localizationModules R) ℤ ⥤ localizationDerived R :=
  @DerivedCategory.Q (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The recorded derived internal Hom; this is only an explicit universe specialization.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationRHom (R : Sheaf J CommRingCat.{u}) :
    (localizationDerived R)ᵒᵖ × localizationDerived R ⥤ localizationDerived R :=
  @derivedInternalHom C _ J R (HasDerivedCategory.standard (localizationModules R))

/-- Termwise slice restriction using the recorded exact restriction functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationComplexRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex (.up ℤ)

/-- The induced exact functor on derived categories, with explicit standard sizes.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    localizationDerived R ⥤ localizationDerived (R.over U) :=
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  @Functor.mapDerivedCategory
    (localizationModules R) _ _ (HasDerivedCategory.standard (localizationModules R))
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) _ _ _

/-- A bounded complex with finite localization sums in every degree. The empty sum is allowed.
Source: Stacks 0996, localization specialization of 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def IsBoundedLocalizationComplex (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    ∀ n : ℤ, ∃ (k : ℕ) (g : Fin k → (R.obj ⋙ forget CommRingCat.{u}).sections),
      Nonempty (P.X n ≅ ∐ (fun i : Fin k ↦ ringedSectionLocalization R (g i)))

/-- Ordinary tensor by a sheaf in degree zero: terms and differentials are tensorized.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationTensorComplex (R : Sheaf J CommRingCat.{u}) (S : localizationModules R) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules R) ℤ :=
  haveI := SheafOfModules.monoidalCategory R
  haveI := Classical.choice (SheafOfModules.tensorClosed R).1
  (@tensorLeft (localizationModules R) _
    (SheafOfModules.monoidalCategory R) S).mapHomologicalComplex
    (.up ℤ)

/-- The actual coefficient localization on the slice, using the recorded fraction presheaf.
Source: Stacks 0996 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationModules (R.over U) :=
  ringedSectionLocalization (R.over U) (ringedSliceSection R U f)

/-- The ordinary localized complex P_f, including its tensor differential.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceComplex (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  localizationComplexRestriction R U ⋙
    localizationTensorComplex (R.over U) (localizationSliceCoefficient R U f)

/-- The coefficient localization regarded as an object of the unbounded derived category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceDerivedCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationDerived (R.over U) :=
  (localizationQ (R.over U)).obj
    ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
      (localizationSliceCoefficient R U f))

/-- Further slice restriction on the same existing derived categories.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedOverMap (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerived (R.over U) ⥤ localizationDerived (R.over V) :=
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  @Functor.mapDerivedCategory
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (localizationModules (R.over V)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _

/-- The canonical relocalization comparison, induced by the sectionwise identity.
Source: Stacks 08JB, Modules on Sites 04IX
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationRestrictionCompIso (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerivedRestriction R U ⋙ localizationDerivedOverMap R a ≅
      localizationDerivedRestriction R V :=
  haveI := HasDerivedCategory.standard (localizationModules R)
  haveI := HasDerivedCategory.standard (localizationModules (R.over U))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  haveI := HasDerivedCategory.standard (localizationModules (R.over V))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  haveI := ringedSite_overFunctor_additive J R V
  haveI := ringedSite_overFunctor_limits J R V
  haveI := ringedSite_overFunctor_colimits J R V
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  (@Functor.mapDerivedCategoryCompIso
    (localizationModules R) (localizationModules (R.over U)) (localizationModules (R.over V))
    _ _ _ _ _ _
    (HasDerivedCategory.standard (localizationModules R))
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _ _ _ _).symm ≪≫
    @Functor.mapDerivedCategoryNatIso
      (localizationModules R) (localizationModules (R.over V)) _ _ _ _
      (HasDerivedCategory.standard (localizationModules R))
      (HasDerivedCategory.standard (localizationModules (R.over V))) _ _ _ _ _ _ _ _
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a)

/-- Bounded localization complexes and their coefficient localizations admit identity
K-flat replacements. The ordinary tensor complex is the total tensor with the coefficient
in degree zero, so it represents the derived tensor specified in the node.

Source: Stacks 08J9 and 0996
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
Proof:
1. Sectionwise localization is flat (lem-weil-pbc-localization-flat). Exact module
   sheafification and its tensor comparison preserve this flatness.
2. Finite sums are flat, including the empty sum. Slice restriction preserves flatness
   (lem-weil-pbc-slice-restriction-flat). Bounded-above flat complexes are K-flat
   (lem-pc-bounded-above-flat-kflat-site).
3. The degree-zero coefficient complex is K-flat for the same reason. Its total tensor
   with restricted P has only the summand with first degree zero. The summand inclusions
   identify the differential with 1 tensor d_P (def-pc-tensor-complex-sheaves).
4. Consequently the identity K-flat replacement computes the stated derived tensor.
No bound on the target complex occurs. -/
theorem ringedLocalization_kflat_models (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) (hP : IsBoundedLocalizationComplex R P)
    (U : C) (f : R.obj.obj (op U)) :
    CochainComplex.IsAcyclicTensorKFlat ((localizationComplexRestriction R U).obj P) ∧
    CochainComplex.IsAcyclicTensorKFlat
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
        (localizationSliceCoefficient R U f)) ∧
    Nonempty (CochainComplex.mapBifunctor
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
        (localizationSliceCoefficient R U f))
      ((localizationComplexRestriction R U).obj P)
      (@curriedTensor (localizationModules (R.over U)) _
        (SheafOfModules.monoidalCategory (R.over U))) ≅
      (localizationSliceComplex R U f).obj P) := by
  sorry

/-- Tensoring two coefficient localizations multiplies the denominators.
Source: Stacks 0996, proof of (3)
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
Proof: the sectionwise forward map sends (a/f^r) tensor (b/g^s) to
ab f^(k-r) g^(k-s)/(fg)^k for k at least r,s. The inverse sends c/(fg)^n to
(1/f^n) tensor (c/g^n). Moving scalars across the tensor proves the composites are
identities. These fraction formulas commute with all restriction ring maps. Sheafify
and apply lem-pc-sites-module-sheafification-tensor. Tensor distributes over each finite
sum because it is a left adjoint (lem-pc-sheaf-modules-tensor-closed). -/
theorem ringedLocalization_tensor_product (R : Sheaf J CommRingCat.{u}) (U : C)
    (f g : R.obj.obj (op U)) :
    Nonempty ((SheafOfModules.monoidalCategory (R.over U)).tensorObj
      (localizationSliceCoefficient R U f) (localizationSliceCoefficient R U g) ≅
      localizationSliceCoefficient R U (f * g)) := by
  sorry

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
  sorry

end CategoryTheory
