/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels
import WeilConjectures.AlgebraicGeometry.IntegralReductionKoszulModel
import WeilConjectures.AlgebraicGeometry.KInjectivePrincipalTensor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Separate tensor representatives of integral reduction towers

Source: the finite-free quotient resolution in the first paragraph of the current
blueprint `lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures.IntegralHom

attribute [local irreducible] derivedInternalHomOfUniverses totalTensor
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard

private theorem homTower_representatives
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (K : Derived.{t, u} Y R) (A : CochainComplex (Modules.{t, u} Y R) ℤ)
    (eA : DerivedCategory.Q.obj A ≅ K)
    (S : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ n, (S.obj n).IsKInjective) :
    Nonempty (S ⋙ DerivedCategory.Q ⋙ (Functor.curry.obj (hom.{t, u} Y R)).obj (op K) ≅
      S ⋙ (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R)).obj (op A) ⋙ DerivedCategory.Q) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let M := Modules.{t, u} Y R
  let : IsGrothendieckAbelian.{max u (t + 1)} M :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J R).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} M
  let η := CochainComplex.toKInjectiveResolution.{max u (t + 1)} M
  let HA := (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R)).obj (op A)
  obtain ⟨c⟩ := derivedInternalHomOfUniverses_comparison.{t + 1, t, u} J R I₀ η
    (fun N ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app
      M N).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M N⟩)
  let b : S ⋙ HA ⋙ DerivedCategory.Q ⟶ S ⋙ I₀ ⋙ HA ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (Functor.whiskerLeft S η) (HA ⋙ DerivedCategory.Q)
  have hb : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    let : (S.obj n).IsKInjective := hS n
    have : (I₀.obj (S.obj n)).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M (S.obj n)
    have : QuasiIso (η.app (S.obj n)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app M (S.obj n)).2
    change IsIso (DerivedCategory.Q.map (HA.map (η.app (S.obj n))))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    simpa [HA] using quasiIso_homComplex_mapOfUniverses.{t + 1, t, u}
      (J := J) (R := R) (I' := S.obj n) (I := I₀.obj (S.obj n))
      (L' := A) (L := A) (η.app (S.obj n)) (𝟙 A)
  let cS : S ⋙ DerivedCategory.Q ⋙
      (Functor.curry.obj (hom.{t, u} Y R)).obj (op (DerivedCategory.Q.obj A)) ≅
      S ⋙ I₀ ⋙ HA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun n ↦ c.app (op A, S.obj n)) (by
      intro n m f
      simpa [HA, hom] using c.hom.naturality
        (X := (op A, S.obj n)) (Y := (op A, S.obj m)) (𝟙 (op A), S.map f))
  exact ⟨Functor.isoWhiskerLeft (S ⋙ DerivedCategory.Q)
    ((Functor.curry.obj (hom.{t, u} Y R)).mapIso eA.op) ≪≫ cS ≪≫ (asIso b).symm⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Both reduction towers have tensor representatives using the same two-term
coefficient tower. The two isomorphisms identify the towers separately; no
comparison between Hom tensor Q and Hom into a tensor is asserted here.

Source: the first paragraph of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`, the free resolution of the quotient;
Stacks Tags 06YY, 08J7, 07A6 and 08TC
(blueprint: lem-sf-integral-hom-tower-tensor-models).

Proof: let R be the completed coefficient sheaf and pi its constant uniformizer.
Use Q_n=[R --pi^(n+1)--> R] in degrees -1 and zero. The maps (pi,id) give a
strict coefficient tower Q. Its augmentation to the actual finite quotient is
a quasi-isomorphism: pi is regular on the completed coefficient sheaf and its
cokernel is the specified quotient. Choose a K-flat representative A of K and
a K-injective representative I of Q(G). Tensoring with the bounded free Q_n
computes derived reduction of any complex. In particular Hom(A,I) tensor Q_n
computes reduction of Hom(K,Q(G)); transport along e and the canonical
K-flat computation for q' gives the second displayed tower isomorphism.
For the first, I tensor Q_n is K-injective: it is a finite cone of shifts of
I, and Hom from any acyclic complex into that cone is acyclic. Thus
Hom(A,I tensor Q_n) represents Hom(K,Res_n(F_n Q(G))). Compute the latter
reductions on q. These identifications are natural for the actual quotient
maps because (pi,id) lifts the quotient transition. Their augmentations and
resolution comparisons commute on pure tensors, by the derived scalar
extension counit and resolution independence. If a strict tensor calculation
requires flat terms, first use flat-term K-flat refinements of q and q', then
transport back by the canonical resolution-independent tower comparison. They assemble into
isomorphisms of towers. The two computations do not use the signed exchange
map, its invertibility, products or completeness. All powers are positive,
including n=0; zero inputs and the empty scheme are allowed. -/
theorem reductionTower_tensor_models
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let H := (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
    ∃ (A I : CochainComplex (Modules.{t, u} Y R) ℤ)
      (Q : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ),
      (∀ n : ℕ,
        (∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero ((Q.obj (op n)).X k)) ∧
        Nonempty ((Q.obj (op n)).X (-1) ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))) ∧
        Nonempty ((Q.obj (op n)).X 0 ≅ (show Modules.{t, u} Y R from
          SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))) ∧
      Nonempty (integralReductionTower l E Y D hl P ⋙ H ≅
        Q ⋙ (totalTensor.{t, u} Y R).obj I ⋙
          (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := R)).obj (op A) ⋙ DerivedCategory.Q) ∧
      Nonempty (integralReductionTower l E Y D hl P' ≅
        Q ⋙ (totalTensor.{t, u} Y R).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I) ⋙
            DerivedCategory.Q) := by
  classical
  let R := completedIntegralCommRingSheaf l E Y D hl
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let M := Modules.{t, u} Y R
  let H := (Functor.curry.obj (hom.{t, u} Y R)).obj (op K)
  let A : CochainComplex M ℤ := DerivedCategory.Q.objPreimage K
  let eA : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let : IsGrothendieckAbelian.{max u (t + 1)} M :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J R).1
  let I := (CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} M).obj G
  let : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M G
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} M).app G) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app M G).2
  let eI : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj G :=
    (asIso (DerivedCategory.Q.map
      ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} M).app G))).symm
  let a := PrincipalKoszulStrictReplacement.uniformizer l E Y
  let Q := principalKoszulTower R a
  obtain ⟨r⟩ := integralReductionTower_koszul_model l E Y D hl P G I q hq eI
  obtain ⟨h⟩ := homTower_representatives Y R K A eA
    (Q ⋙ (totalTensor.{t, u} Y R).obj I)
    (fun n ↦ isKInjective_tensor_principalKoszul Y R a I n.unop)
  obtain ⟨c⟩ := derivedInternalHomOfUniverses_obj_iso.{t + 1, t, u} J R
    K (DerivedCategory.Q.obj G) A I eA eI
  obtain ⟨r'⟩ := integralReductionTower_koszul_model l E Y D hl P' G'
    (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) A I)
    q' hq' (c.symm ≪≫ e.symm)
  refine ⟨A, I, Q, ?_, ⟨Functor.isoWhiskerRight r H ≪≫ h⟩, ⟨r'⟩⟩
  intro n
  let U := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)
  let f := principalKoszulScalarComplex R a n
  constructor
  · intro k hk₁ hk₀
    apply (CochainComplex.mappingCone.isZero_X_iff f k).2
    exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U _ (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U k hk₀⟩
  · constructor
    · exact ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod f (-1) 0 (by decide) ≪≫
        (isoBiprodZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U (-1)
          (by decide))).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 U⟩
    · exact ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod f 0 1 (by decide) ≪≫
        (isoZeroBiprod (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U 1
          (by decide))).symm ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 U⟩

end WeilConjectures.IntegralHom
