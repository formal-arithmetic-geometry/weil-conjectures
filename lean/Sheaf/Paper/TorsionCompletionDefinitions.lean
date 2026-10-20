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

/-! # Constant coefficients and local power-torsion towers

Source: Stacks Project, Tags 099P and 099Q (1), (4), (5)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model).

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
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (constantSheaf (coefficientProEtaleModelTopology.{t, u} X)
    CommRingCat.{max u (t + 1)}).obj (CommRingCat.of (ULift.{t + 1} A))

/-- Forget commutativity of the constant ring sheaf, retaining the actual ring sheaf.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionModuleRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (torsionCompletionRing X A)

/-- The module-sheaf category on this model is precisely the recorded ringed-site category.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev TorsionCompletionModules (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  ringedSiteModules.{max u (t + 1)} (torsionCompletionModuleRing X A)

/-- The constant quotient morphism, obtained by sheafifying the actual quotient ring map.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotient (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    torsionCompletionModuleRing X A ⟶ torsionCompletionModuleRing X (A ⧸ I) :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))

/-- The quotient ring as a module over the constant original ring.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionQuotientModule (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :=
  (SheafOfModules.restrictScalars (torsionCompletionQuotient X I)).obj
    (SheafOfModules.unit (torsionCompletionModuleRing X (A ⧸ I)))

/-- The unit sections of the quotient ring form a global section of its module sheaf.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotientOne (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) : (torsionCompletionQuotientModule X I).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (1 : (torsionCompletionModuleRing X (A ⧸ I)).obj.obj U))
    (fun {_ _} f ↦ ((torsionCompletionModuleRing X (A ⧸ I)).obj.map f).hom.map_one)

/-- The quotient map on modules sends the unit generator to one, hence sends a to its
quotient image. No arbitrary map is chosen.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotientMap (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    SheafOfModules.unit (torsionCompletionModuleRing X A) ⟶
      torsionCompletionQuotientModule X I :=
  (SheafOfModules.unitHomEquiv _).symm (torsionCompletionQuotientOne X I)

/-- The extended ideal I A is the kernel of A → A/I as module sheaves. Constant
sheafification is exact, so this is the ideal generated locally by the constants in I.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionIdeal (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    TorsionCompletionModules X A :=
  kernel (torsionCompletionQuotientMap X I)

/-- The canonical ideal inclusion, not a separately chosen embedding.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionIdealInclusion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :
    torsionCompletionIdeal X I ⟶ SheafOfModules.unit (torsionCompletionModuleRing X A) :=
  kernel.ι (torsionCompletionQuotientMap X I)

/-- Sheafification of abelian coefficients on the coefficient-sized small model.
This invokes the general small-site theorem, avoiding successor-universe inference.
Source: Stacks Tags 03DA, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
instance (priority := 20000) torsionCompletionSheafify (X : Scheme.{t}) :
    HasSheafify (coefficientProEtaleModelTopology.{t, u} X)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The same abelian sheafification on each slice of the unchanged model site.
Source: Stacks Tags 03DA, 03DJ, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
instance (priority := 20000) torsionCompletionSliceSheafify (X : Scheme.{t})
    (U : coefficientProEtaleSiteModel.{t, u} X) :
    HasSheafify ((coefficientProEtaleModelTopology.{t, u} X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- Use the standard localization at quasi-isomorphisms for the module-sheaf category.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev TorsionCompletionDerived (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  @DerivedCategory (TorsionCompletionModules X A) _ _ (HasDerivedCategory.standard _)

/-- The localization functor for this choice of derived-category universe.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionLocalization (X : Scheme.{t}) (A : Type u) [CommRing A] :
    CochainComplex (TorsionCompletionModules X A) ℤ ⥤ TorsionCompletionDerived X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Derived completeness is the recorded vanishing condition on every slice and for
 every section of the extended ideal. The standard derived categories are chosen on
 all slices as well; no additional existence hypothesis is imposed.
Source: Stacks Tags 0999, 099F, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
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
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsTorsionCompletionCompleteSheaf (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : TorsionCompletionModules X A) : Prop :=
  IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- An ideal subsheaf annihilates a module if every one of its local sections acts by zero.
This expresses sheaf annihilation, with no section-finiteness hypothesis.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
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
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
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

end AlgebraicGeometry.Scheme
