/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Ordinary finite-coefficient cup products

Source: Milne, Lectures on Etale Cohomology, Section 22, p.135; Stacks 03FD and 0FPJ.
(blueprint: def-wf-finite-coefficient-cup)

The constant-coefficient cup is expressed in shifted Yoneda composition with its
Koszul sign.
The coefficient-forgetting map is explicitly induced by the unit Z → Z/N; its inverse
is determined by bijectivity, rather than by a choice of an arbitrary comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Forget module coefficients. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupForget (X : Scheme.{u}) (N : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) AddCommGrpCat)

/-- Forgetting a module sheaf is additive. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup)
Proof: addition of sheaf morphisms and coefficient forgetting are both sectionwise;
the forgetful functor sends a sum of linear maps to its underlying additive sum. -/
@[instance] theorem finiteCupForget_additive (X : Scheme.{u}) (N : ℕ) :
    (finiteCupForget X N).Additive := by
  sorry

/-- Forgetting module sheaves preserves finite limits. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup)
Proof: finite limits of module sheaves are computed sectionwise, and forgetting
modules preserves these sectionwise finite limits. -/
@[instance] theorem finiteCupForget_limits (X : Scheme.{u}) (N : ℕ) :
    PreservesFiniteLimits (finiteCupForget X N) := by
  sorry

/-- Forgetting module sheaves preserves finite colimits. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup)
Proof: a cokernel is the sheafification of the sectionwise cokernel. The abelian
sheaf cokernel has the induced unique module action, so this construction is also
the cokernel in module sheaves. Finite sums are sectionwise; together these compute
all finite colimits in the two abelian categories. -/
@[instance] theorem finiteCupForget_colimits (X : Scheme.{u}) (N : ℕ) :
    PreservesFiniteColimits (finiteCupForget X N) := by
  sorry

/-- Forgetting module coefficients commutes with sheafification. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup)
Proof: the plus construction sheafifies a module presheaf using matching families
and local identifications. The module operations descend uniquely through these
identifications, and its underlying abelian plus construction is identical.
Iterating plus therefore gives the claimed preservation of sheafification. -/
@[instance] theorem finiteCupForget_sheafification (X : Scheme.{u}) (N : ℕ) :
    X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) AddCommGrpCat) := by
  sorry

/-- The rank-one constant module. Source: Milne Section 22.
(blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupUnit (X : Scheme.{u}) (N : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))).obj
    (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N)))

/-- The underlying constant coefficient identification. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupUnitIso (X : Scheme.{u}) (N : ℕ) :
    (finiteCupForget X N).obj (finiteCupUnit X N) ≅ X.constantZMod N :=
  (constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) AddCommGrpCat)).app _

/-- The coefficient-forgetting comparison, with the integer unit precomposition.
Source: Stacks 03FD. (blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupComparison (X : Scheme.{u}) (N : ℕ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))) (q : ℕ) :
    Abelian.Ext.{u + 1} (finiteCupUnit X N) M q →
      Sheaf.H ((finiteCupForget X N).obj M) q :=
  fun x ↦ (Abelian.Ext.mk₀
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.ofHom
        (RingHom.ulift (Int.castRingHom (ZMod N))).toAddMonoidHom) ≫
          (finiteCupUnitIso X N).inv)).comp
    (x.mapExactFunctor (finiteCupForget X N)) (zero_add q)

/-- The comparison is bijective. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup)
Proof: in degree zero the constant-sheaf adjunction identifies both sides with
module sections, and the displayed map is evaluation at one. An injective module
sheaf is acyclic for abelian global sections by the injective Cech argument of
03FD. Apply an injective resolution in module sheaves; coefficient forgetting is
exact and its resolution computes the same derived global sections. This proves
bijectivity in all nonnegative degrees, naturally in the coefficient module. -/
theorem finiteCupComparison_bijective (X : Scheme.{u}) (N : ℕ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))) (q : ℕ) :
    Function.Bijective (finiteCupComparison X N M q) := by
  sorry

/-- The uniquely determined inverse comparison. Source: Stacks 03FD.
(blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupComparisonEquiv (X : Scheme.{u}) (N : ℕ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))) (q : ℕ) :
    Abelian.Ext.{u + 1} (finiteCupUnit X N) M q ≃
      Sheaf.H ((finiteCupForget X N).obj M) q :=
  Equiv.ofBijective _ (finiteCupComparison_bijective X N M q)

/-- The root module presheaf satisfies descent. Source: Stacks 03PK.
(blueprint: def-wf-finite-coefficient-cup)
Proof: its underlying abelian presheaf is exactly the existing roots-of-unity
sheaf. The module forgetful functor reflects limits, so the underlying sheaf
condition is the module-valued sheaf condition. -/
theorem finiteCupRoots_isSheaf (X : Scheme.{u}) (N : ℕ) :
    Presheaf.IsSheaf X.smallEtaleTopology (kummerRootModulePresheaf X N) := by
  sorry

/-- The unique exponent action on the existing roots-of-unity sheaf.
Source: Stacks 03PK. (blueprint: def-wf-finite-coefficient-cup) -/
def finiteCupRoots (X : Scheme.{u}) (N : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) :=
  ⟨kummerRootModulePresheaf X N, finiteCupRoots_isSheaf X N⟩

/-- Canonical finite constant/roots cup, expressed by Yoneda composition.
Source: Milne Section 22, p.135; Stacks 0FPJ.
(blueprint: def-wf-finite-coefficient-cup)
Under the unit-cohomology identification, composition is the derived tensor cup
followed by evaluation: tensor a unit class with a module class and use the
unitors. The factor (-1)^(p*q) converts the left-then-right shifted Yoneda convention
to the unsigned Cech front/back convention of Milne Section 22 (the Koszul
interchange of the two shifts). -/
def finiteCoefficientCup (X : Scheme.{u}) (N p q r : ℕ) (hpq : p + q = r)
    (x : Sheaf.H (X.constantZMod N) p) (y : Sheaf.H (X.rootsOfUnitySheaf N) q) :
    Sheaf.H (X.rootsOfUnitySheaf N) r :=
  (-1 : ℤ) ^ (p * q) • finiteCupComparison X N (finiteCupRoots X N) r
    (((finiteCupComparisonEquiv X N (finiteCupUnit X N) p).symm
      (Sheaf.H.map (finiteCupUnitIso X N).inv p x)).comp
        ((finiteCupComparisonEquiv X N (finiteCupRoots X N) q).symm y) hpq)

end AlgebraicGeometry.Scheme
