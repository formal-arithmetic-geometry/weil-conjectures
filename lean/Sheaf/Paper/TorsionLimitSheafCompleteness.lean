/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Paper.LocalHomTowerCriterion
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Completeness of limits of power-torsion pro-etale sheaves

Source: Stacks Project, Tags 099P and 099Q (1), (4), (5)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness).

We use the existing coefficient-sized small model of the unchanged small pro-etale site.
It is equivalent via AsSmall.down to X.ProEt; its topology is the induced topology.
Thus this changes sizes only, not objects, covers, slices, or coefficient sheaves up to
canonical equivalence. Local completeness is the existing slice internal-Hom definition.
The extended ideal is constructed as the kernel of the constant quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf on the recorded small model.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (constantSheaf (coefficientProEtaleModelTopology.{t, u} X)
    CommRingCat.{max u (t + 1)}).obj (CommRingCat.of (ULift.{t + 1} A))

/-- Forget commutativity of the constant ring sheaf, retaining the actual ring sheaf.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionModuleRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (torsionCompletionRing X A)

/-- The module-sheaf category on this model is precisely the recorded ringed-site category.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev TorsionCompletionModules (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  ringedSiteModules.{max u (t + 1)} (torsionCompletionModuleRing X A)

/-- The constant quotient morphism, obtained by sheafifying the actual quotient ring map.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotient (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    torsionCompletionModuleRing X A ⟶ torsionCompletionModuleRing X (A ⧸ I) :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))

/-- The quotient ring as a module over the constant original ring.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionQuotientModule (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :=
  (SheafOfModules.restrictScalars (torsionCompletionQuotient X I)).obj
    (SheafOfModules.unit (torsionCompletionModuleRing X (A ⧸ I)))

/-- The unit sections of the quotient ring form a global section of its module sheaf.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotientOne (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) : (torsionCompletionQuotientModule X I).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (1 : (torsionCompletionModuleRing X (A ⧸ I)).obj.obj U))
    (fun {_ _} f ↦ ((torsionCompletionModuleRing X (A ⧸ I)).obj.map f).hom.map_one)

/-- The quotient map on modules sends the unit generator to one, hence sends a to its
quotient image. No arbitrary map is chosen.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotientMap (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    SheafOfModules.unit (torsionCompletionModuleRing X A) ⟶
      torsionCompletionQuotientModule X I :=
  (SheafOfModules.unitHomEquiv _).symm (torsionCompletionQuotientOne X I)

/-- The extended ideal I A is the kernel of A → A/I as module sheaves. Constant
sheafification is exact, so this is the ideal generated locally by the constants in I.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionIdeal (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    TorsionCompletionModules X A :=
  kernel (torsionCompletionQuotientMap X I)

/-- The canonical ideal inclusion, not a separately chosen embedding.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionIdealInclusion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :
    torsionCompletionIdeal X I ⟶ SheafOfModules.unit (torsionCompletionModuleRing X A) :=
  kernel.ι (torsionCompletionQuotientMap X I)

/-- Sheafification of abelian coefficients on the coefficient-sized small model.
This invokes the general small-site theorem, avoiding successor-universe inference.
Source: Stacks Tags 03DA, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
instance (priority := 20000) torsionCompletionSheafify (X : Scheme.{t}) :
    HasSheafify (coefficientProEtaleModelTopology.{t, u} X)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The same abelian sheafification on each slice of the unchanged model site.
Source: Stacks Tags 03DA, 03DJ, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
instance (priority := 20000) torsionCompletionSliceSheafify (X : Scheme.{t})
    (U : coefficientProEtaleSiteModel.{t, u} X) :
    HasSheafify ((coefficientProEtaleModelTopology.{t, u} X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- Use the standard localization at quasi-isomorphisms for the module-sheaf category.
Source: Stacks Tags 05RU, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev TorsionCompletionDerived (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  @DerivedCategory (TorsionCompletionModules X A) _ _ (HasDerivedCategory.standard _)

/-- The localization functor for this choice of derived-category universe.
Source: Stacks Tags 05RU, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionLocalization (X : Scheme.{t}) (A : Type u) [CommRing A] :
    CochainComplex (TorsionCompletionModules X A) ℤ ⥤ TorsionCompletionDerived X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Derived completeness is the recorded vanishing condition on every slice and for
 every section of the extended ideal. The standard derived categories are chosen on
 all slices as well; no additional existence hypothesis is imposed.
Source: Stacks Tags 0999, 099F, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsTorsionCompletionComplete (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (K : TorsionCompletionDerived X A) : Prop :=
  letI := HasDerivedCategory.standard (TorsionCompletionModules X A)
  letI : ∀ U : coefficientProEtaleSiteModel.{t, u} X,
      HasDerivedCategory.{max u (t + 1) + 1} (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((torsionCompletionRing X A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  IsLocallyDerivedRingedIdealComplete (torsionCompletionRing X A)
    (torsionCompletionIdeal X I) (torsionCompletionIdealInclusion X I) K

/-- Degree-zero derived completeness of a sheaf.
Source: Stacks Tag 099Q (1)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsTorsionCompletionCompleteSheaf (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : TorsionCompletionModules X A) : Prop :=
  IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- An ideal subsheaf annihilates a module if every one of its local sections acts by zero.
This expresses sheaf annihilation, with no section-finiteness hypothesis.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsAnnihilatedByModuleIdeal {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
    (M : SheafOfModules.{v} R)
    (ι : M ⟶ SheafOfModules.unit R) (F : SheafOfModules.{v} R) : Prop :=
  ∀ (U : C) (y : M.val.obj (op U)) (x : F.val.obj (op U)),
    ι.val.app (op U) y • x = 0

/-- Locally F is an ordinary countable inverse limit, with level n indexed by the
positive exponent n+1. The covering sieve condition includes every object and arbitrary
further slices. Transition maps have no epimorphism condition.
Source: Stacks Tags 099P, 099Q (4)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsLocallyPowerTorsionLimit (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (F : TorsionCompletionModules X A) : Prop :=
  ∀ U : coefficientProEtaleSiteModel.{t, u} X,
    ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{t, u} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{t, u} X) (f : V ⟶ U), S f →
        ∃ (G : ℕ → SheafOfModules.{max u (t + 1)}
            ((torsionCompletionModuleRing X A).over V))
          (g : ∀ n : ℕ, G (n + 1) ⟶ G n),
          (∀ n : ℕ, IsAnnihilatedByModuleIdeal
            ((torsionCompletionModuleRing X A).over V)
            ((torsionCompletionIdeal X (I ^ (n + 1))).over V)
            ((torsionCompletionIdealInclusion X (I ^ (n + 1))).over V) (G n)) ∧
          Nonempty (F.over V ≅ limit (Functor.ofOpSequence g))

/-- Complete sheaves are a weak Serre class, are closed under ordinary countable inverse
limits, include all power-torsion sheaves, and therefore include locally power-torsion
limits and bounded complexes of these sheaves.
Source: Stacks Tags 099P and 099Q (1), (4), (5)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness).

Proof:
1. On every slice use weakly-etale localization and exact restriction. Exact countable
products represent derived products (lem-weil-proetale-countable-products-exact and
lem-weil-derived-limit-products-core). The local Hom/tower criterion identifies
completeness of F[0] with invertibility of Delta_f on its countable product, where
Delta_f(x)_j = x_j - f x_(j+1). This tests all local ideal sections.
2. Apply exact products to the five-term exact sequence. The four outside Delta maps
are invertible. Injectivity of the middle map follows by lifting into the second term
and correcting by a lift from the first; surjectivity follows by lifting the inverse
image in the fourth term and correcting the error from the second term. Local lifts
and their unique inverses glue. This gives the weak Serre assertion.
3. Products and restriction are sectionwise. Exchange the two compatible-family
conditions for products and inverse limits. The inverses of Delta at each level commute
with every transition, since Delta does. They give an inverse on the ordinary limit,
without surjective transitions or exactness of inverse limits.
4. If I^n F = 0, the shift s_f satisfies s_f^n = 0 on every slice for f in the ideal.
The finite sum 1+s_f+...+s_f^(n-1) inverts 1-s_f. Thus power-torsion sheaves are complete.
5. Delta and its cone commute with slice restriction. Local inverses glue, or equivalently
vanishing of the cone cohomology is local. Apply steps 3 and 4 to every local tower.
6. For the bounded complex, Delta is a chain isomorphism term by term by step 5.
Its inverse commutes with the differentials by linearity. Its cone is contractible,
with h(b,a) = (0,Delta^(-1)b). The product representation and local Hom/tower criterion
then give the required derived internal-Hom vanishing. -/
theorem torsionLimitSheaf_completeness (X : Scheme.{t}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (_hI : I.FG) :
    (∀ (F₁ F₂ F₃ F₄ F₅ : TorsionCompletionModules X A)
      (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (d : F₄ ⟶ F₅)
      (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0),
      (ShortComplex.mk a b hab).Exact → (ShortComplex.mk b c hbc).Exact →
      (ShortComplex.mk c d hcd).Exact →
      IsTorsionCompletionCompleteSheaf X I F₁ → IsTorsionCompletionCompleteSheaf X I F₂ →
      IsTorsionCompletionCompleteSheaf X I F₄ → IsTorsionCompletionCompleteSheaf X I F₅ →
      IsTorsionCompletionCompleteSheaf X I F₃) ∧
    (∀ (F : ℕ → TorsionCompletionModules X A) (f : ∀ n : ℕ, F (n + 1) ⟶ F n),
      (∀ n : ℕ, IsTorsionCompletionCompleteSheaf X I (F n)) →
      IsTorsionCompletionCompleteSheaf X I (limit (Functor.ofOpSequence f))) ∧
    (∀ (F : TorsionCompletionModules X A) (n : ℕ), 1 ≤ n →
      IsAnnihilatedByModuleIdeal (torsionCompletionModuleRing X A)
        (torsionCompletionIdeal X (I ^ n)) (torsionCompletionIdealInclusion X (I ^ n)) F →
      IsTorsionCompletionCompleteSheaf X I F) ∧
    (∀ F : TorsionCompletionModules X A, IsLocallyPowerTorsionLimit X I F →
      IsTorsionCompletionCompleteSheaf X I F) ∧
    (∀ K : CochainComplex (TorsionCompletionModules X A) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) →
      (∀ i : ℤ, IsLocallyPowerTorsionLimit X I (K.X i)) →
      IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
