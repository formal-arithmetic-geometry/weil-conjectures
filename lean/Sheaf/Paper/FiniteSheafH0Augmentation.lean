module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Finite sheaf degree-zero augmentation

Source: Stacks Project, derived.tex, Tags 013K, 05TD, 070J, 013P and 070Y;
current blueprint, cohomological finiteness, constant-coefficient paragraph
(blueprint: lem-pod-finite-sheaf-h0-augmentation).

The index n denotes exponent n+1, hence includes every positive coefficient level.
Sections are evaluated on the base change of the final object of Spec k. The canonical
`overPullbackObjMkIdIso` identifies this object with the final object Y, so these are F(Y).
No connectedness or nonemptiness assumption occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]

/-- The actual section functor F ↦ (f_*F)(s) = F(Y), with constant coefficient scalars.
The final-object identification is `overPullbackObjMkIdIso (Y ↘ Spec (.of D.k))`.
Source: Stacks 03D6 and 03CW
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafSections (n : ℕ) :=
  proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))

/-- The canonical comparison from H⁰(C_F) to sections of R⁰f_*F. It is the exact
point-sections comparison followed by the normalized K-injective/injective comparison.
Source: Stacks 05TD, 070J and 070Y
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafH0Comparison (n : ℕ)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (n + 1)))) :
    finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
        ((DerivedCategory.singleFunctor _ 0).obj F) 0 ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        (((proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
          (Padic.coefficientExtensionRing l E (n + 1))).rightDerived 0).obj F) := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y)
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))).1
  let T := proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  exact (G.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 2, u + 2} 0).symm.app _ ≪≫
    G.mapIso (T.homologyRightDerivedFunctorObjSingleFunctorIso F 0)

/-- The section augmentation is the inverse degree-zero left-exactness comparison,
followed by the inverse normalized comparison to H⁰(C_F). All data come from the
nonnegative injective-resolution augmentation, not an arbitrary isomorphism.
Source: Stacks 013K, 05TD and 070Y
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafH0AugmentationIso (n : ℕ)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (n + 1)))) :
    (finiteSheafSections D l E Y n).obj F ≅
      finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
        ((DerivedCategory.singleFunctor _ 0).obj F) 0 := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y)
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))).1
  let T := proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  letI : PreservesFiniteLimits T :=
    (proEtaleConstantModuleDirectImage_additive_leftExact _ _).2
  exact G.mapIso (T.rightDerivedZeroIsoSelf.app F).symm ≪≫
    (finiteSheafH0Comparison D l E Y n F).symm

/-- The augmentation class computed using any nonnegative injective resolution.
The cycle factorization is Mathlib's `toRightDerivedZero'`, and `isoRightDerivedObj`
is the normalized change-of-resolution comparison. This definition retains the map,
not just the existence of an abstract isomorphism.
Source: Stacks 013K, 05TD, 070J and 070Y
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafResolutionClass (n : ℕ)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y
      (Padic.coefficientExtensionRing l E (n + 1)))) (I : InjectiveResolution F)
    (x : (finiteSheafSections D l E Y n).obj F) :
    finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
      ((DerivedCategory.singleFunctor _ 0).obj F) 0 := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y)
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))).1
  let T := proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  exact (finiteSheafH0Comparison D l E Y n F).inv
    ((G.map (I.toRightDerivedZero' T ≫ (CochainComplex.isoHomologyπ₀ _).hom ≫
      (I.isoRightDerivedObj T 0).inv)) x)

/-- The constant section a, obtained from the constant-presheaf sheafification unit.
Evaluation is at the base change of s, canonically the final object of Y's site.
Source: Stacks 0H7J and 03D6
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafConstantSection (n : ℕ) (a : Padic.coefficientExtensionRing l E (n + 1)) :
    (finiteSheafSections D l E Y n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  ((toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))).app
        ((proEtaleBaseChange (Y ↘ Spec (.of D.k))).op.obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))) (ULift.up a)

/-- The definitional identification of regular-sheaf cohomology with the recorded
constant coefficient object, removing only its positive-level predecessor cast.
Source: blueprint ordinary-cohomology coefficient-object paragraph
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafConstantCohomologyIso (n : ℕ) :
    finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))) 0 ≅
      finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
        (finiteCohomologyCoefficient l E Y (n + 1) (Nat.succ_pos n)) 0 :=
  eqToIso (by simp [finiteCohomologyCoefficient, finiteConstantCoefficientObject])

/-- The constant coefficient class defined by the actual injective-resolution augmentation.
In particular a=1 is the unit class. No identification of all sections with A is made.
Source: Stacks 05TD; blueprint cohomological finiteness, constant-coefficient paragraph
(blueprint: lem-pod-finite-sheaf-h0-augmentation). -/
def finiteSheafConstantAugmentationClass (n : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1)) :
    finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
      (finiteCohomologyCoefficient l E Y (n + 1) (Nat.succ_pos n)) 0 := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y)
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))).1
  exact (finiteSheafConstantCohomologyIso D l E Y n).hom
    (finiteSheafResolutionClass D l E Y n _ (injectiveResolution _)
      (finiteSheafConstantSection D l E Y n a))

/-- Finite-level cohomology of an arbitrary module sheaf has its natural canonical
section augmentation, no negative cohomology, and the prescribed constant/unit classes.
Source: Stacks derived.tex, Tags 013K, 05TD, 070J, 013P and 070Y; current blueprint,
cohomological finiteness, constant-coefficient paragraph
(blueprint: lem-pod-finite-sheaf-h0-augmentation).

Proof (the six steps of the node):
1. The small ringed site is Grothendieck abelian and has enough injectives. Choose
   a nonnegative injective resolution of F using 013K; it is K-injective by 070J.
2. K-injective derived-map computation identifies the specified Rf_* with the
   sectionwise direct image of this resolution. Exact point sections identify C_F
   with its section complex, with the normalized comparison used above.
3. Direct image and point sections are left exact. The augmentation therefore
   identifies F(Y) with degree-zero cycles, hence H⁰, by 05TD. The cycle map,
   homology projection and all comparisons are coefficient-linear. The formula in
   `finiteSheafResolutionClass` is the class of the degree-zero augmented section.
4. The section complex is zero in all negative degrees, so its negative homology
   is zero. This transfers to the recorded finiteOrdinaryCohomology.
5. Lift every sheaf map to a map of injective resolutions (013P). Its degree-zero
   augmentation square commutes. The K-injective derived-map computation identifies
   its derived action with that sectionwise map. This proves naturality; applying
   it to identity maps between any two resolutions proves the resolution formula
   for every I and thus independence of choices.
6. For the regular constant sheaf, the coefficient-object definition identifies
   the result with recorded H⁰(Y,A). The sheafification unit gives a_Y; the formula
   in step 3 sends it to its same augmentation class. Taking a=1 gives the unit.
   None of these steps requires connectedness or nonemptiness of Y. -/
theorem finite_sheaf_h0_augmentation (_hl : l ≠ D.p)
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] (n : ℕ) :
    (∀ (F : proEtaleRingModules Y (proEtaleConstantRing Y
        (Padic.coefficientExtensionRing l E (n + 1)))) (I : InjectiveResolution F)
        (x : (finiteSheafSections D l E Y n).obj F),
      (finiteSheafH0AugmentationIso D l E Y n F).hom x =
        finiteSheafResolutionClass D l E Y n F I x) ∧
    (∀ (F : proEtaleRingModules Y (proEtaleConstantRing Y
        (Padic.coefficientExtensionRing l E (n + 1)))) (j : ℤ), j < 0 →
      IsZero (finiteOrdinaryCohomology D l E Y (n + 1) (Nat.succ_pos n)
        ((DerivedCategory.singleFunctor _ 0).obj F) j)) ∧
    (∀ (F G : proEtaleRingModules Y (proEtaleConstantRing Y
        (Padic.coefficientExtensionRing l E (n + 1)))) (h : F ⟶ G),
      (finiteSheafSections D l E Y n).map h ≫
          (finiteSheafH0AugmentationIso D l E Y n G).hom =
        (finiteSheafH0AugmentationIso D l E Y n F).hom ≫
          (DerivedCategory.homologyFunctor _ 0).map
            ((pointFiniteSections D.k
              (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
                ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k))
                  (Padic.coefficientExtensionRing l E (n + 1))).map
                    ((DerivedCategory.singleFunctor _ 0).map h)))) ∧
    (∀ a : Padic.coefficientExtensionRing l E (n + 1),
      (finiteSheafConstantCohomologyIso D l E Y n).hom
          ((finiteSheafH0AugmentationIso D l E Y n _).hom
            (finiteSheafConstantSection D l E Y n a)) =
        finiteSheafConstantAugmentationClass D l E Y n a) ∧
    (finiteSheafConstantCohomologyIso D l E Y n).hom
        ((finiteSheafH0AugmentationIso D l E Y n _).hom
          (finiteSheafConstantSection D l E Y n 1)) =
      finiteSheafConstantAugmentationClass D l E Y n 1 := by
  sorry

end WeilConjectures
