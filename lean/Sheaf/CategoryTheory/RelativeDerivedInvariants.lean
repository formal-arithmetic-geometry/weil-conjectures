/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedProductActionInflation
public import Mathlib.Algebra.Homology.DerivedCategory.Plus


/-! # RelativeDerivedInvariants

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-derived-invariants)

## Main definitions and statements

The primary declaration is `invariants`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
/-- The discrete additive integers, written multiplicatively and lifted to the site universe.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
abbrev Z := Multiplicative (ULift.{u} ℤ)

/-- The specified positive cyclic generator.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def generator : Z.{u} := Multiplicative.ofAdd ⟨1⟩

variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Use the recorded small-Hom localization uniformly for scalar and relative modules.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance (priority := 2000) smallModulesDerived : HasDerivedCategory.{u + 1} (Modules A) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (Modules A)

/-- The recorded action-site localization has morphisms in the coefficient universe.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance (priority := 2000) smallActionDerived : HasDerivedCategory.{u + 1} (Equivariant A G) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (Equivariant A G)

/-- The standard larger localization used by the recorded lattice and bar models.
It is transported canonically to the small-Hom localization where required.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
@[instance_reducible]
def largeModulesDerived : HasDerivedCategory.{u + 2} (Modules A) :=
  HasDerivedCategory.standard _

/-- Forget the first action by restricting to the second factor, on the same internal module.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def forgetResidual : Equivariant A (G × J) ⥤ Equivariant A J :=
  inflate (ContinuousMonoidHom.inr G J)

/-- Forget the second action, retaining the residual first action.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def retainResidual : Equivariant A (G × J) ⥤ Equivariant A G :=
  inflate (ContinuousMonoidHom.inl G J)

/-- Addition is unchanged by forgetting the residual factor.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance forgetResidualAdditive : (forgetResidual A G J).Additive :=
  CondensedDerivedRestriction.restrictionAdditive (A := A) (ContinuousMonoidHom.inr G J)

/-- Kernels are unchanged by forgetting the residual factor.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance forgetResidualLimits : PreservesFiniteLimits (forgetResidual A G J) :=
  CondensedDerivedRestriction.restrictionLimits (A := A) (ContinuousMonoidHom.inr G J)

/-- Cokernels are unchanged by forgetting the residual factor.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance forgetResidualColimits : PreservesFiniteColimits (forgetResidual A G J) :=
  CondensedDerivedRestriction.restrictionColimits (A := A) (ContinuousMonoidHom.inr G J)

/-- Retaining the residual action preserves the addition of the original maps.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance retainResidualAdditive : (retainResidual A G J).Additive :=
  CondensedDerivedRestriction.restrictionAdditive (A := A) (ContinuousMonoidHom.inl G J)

/-- Fixed sections give the normalized product invariants even for the discrete group.
Source: paragraph (3), steps 1--2
(blueprint: def-sfb-relative-derived-invariants).
Proof: use the action-site presentation to form the subsheaf of sections fixed after
all base changes. Commuting first-factor actions preserve it. Restrict codomains of maps
from projection inflation; composing with its inclusion is the inverse transpose.
These formulas uniquely determine the functor and its inclusion up to unique isomorphism. -/
theorem productInvariantsExist : Nonempty (ProductInvariants A.toMon G J) := by
  sorry

/-- Relative invariants selected by their invariant-inclusion universal property.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def invariants : ProductInvariants A.toMon G J :=
  Classical.choice (productInvariantsExist A G J)

/-- The normalized product invariant functor is additive.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance invariantsAdditive : (invariants A G J).functor.Additive :=
  (invariants A G J).additive

/-- Ordinary right derivation in the full action categories, with no continuity replacement.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def derived : DerivedCategory.{u + 1} (Equivariant A (G × J)) ⥤
    DerivedCategory.{u + 1} (Equivariant A G) :=
  (invariants A G J).functor.rightDerivedFunctor

/-- Canonical shift on relative ordinary derived invariants.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance derivedShift : (derived A G J).CommShift ℤ :=
  inferInstanceAs ((invariants A G J).functor.rightDerivedFunctor.CommShift ℤ)

/-- Relative ordinary derived invariants preserve distinguished triangles.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance derivedTriangulated : (derived A G J).IsTriangulated :=
  inferInstanceAs ((invariants A G J).functor.rightDerivedFunctor.IsTriangulated)

/-- The actual relative computation unit, with its derived endpoints kept explicit.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def unit (N : CochainComplex (Equivariant A (G × J)) ℤ) :
    DerivedCategory.Q.obj (((invariants A G J).functor.mapHomologicalComplex (.up ℤ)).obj N) ⟶
      (derived A G J).obj (DerivedCategory.Q.obj N) :=
  (invariants A G J).functor.rightDerivedFunctorUnitQ N

/-- The recorded scalar computation unit, with the same explicit endpoint convention.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def scalarUnit (N : CochainComplex (Equivariant A G) ℤ) :
    DerivedCategory.Q.obj
        (((CondensedDerivedRestriction.invariants A G).functor.mapHomologicalComplex
          (.up ℤ)).obj N) ⟶
      (CondensedDerivedRestriction.derived A G).obj (DerivedCategory.Q.obj N) :=
  (CondensedDerivedRestriction.invariants A G).functor.rightDerivedFunctorUnitQ N

/-- Exact forgetting preserves kernels, as recorded by the scalar action calculus.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance forgetLimits :
    PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) :=
  (CondensedDerivedRestriction.forgetExact (A := A) (G := G)).1

/-- Exact forgetting preserves cokernels, as recorded by the scalar action calculus.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
instance forgetColimits :
    PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) :=
  (CondensedDerivedRestriction.forgetExact (A := A) (G := G)).2.1

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Forgetting the residual action is exact and conservative, as is its ordinary derived
functor, without a boundedness restriction. The same holds when all actions are forgotten.
Source: paragraph (3), steps 3--4
(blueprint: def-sfb-relative-derived-invariants).
Proof: kernels and cokernels are created on underlying modules by the action-site
presentation. The inverse of an invertible equivariant map is equivariant. Exactness
commutes with cohomology, so vanishing of the forgotten cone detects isomorphisms in D.
Free induction R[G] tensor - is an exact left adjoint, by flatness of represented free
modules (03EV); hence forgetting also preserves injectives. -/
theorem forgettingProperties :
    (forgetResidual A G J).ReflectsIsomorphisms ∧
    (forgetResidual A G J).mapDerivedCategory.ReflectsIsomorphisms ∧
    PreservesFiniteLimits (forgetResidual A G J) ∧
    PreservesFiniteColimits (forgetResidual A G J) ∧
    (forgetResidual A G J).PreservesInjectiveObjects ∧
    (CondensedBar.forgetAction (A := A) (G := G)).ReflectsIsomorphisms ∧
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.ReflectsIsomorphisms ∧
    (CondensedBar.forgetAction (A := A) (G := G)).PreservesInjectiveObjects := by
  sorry

variable {A G J}
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The standard larger localization needed to read the recorded bar model. This does not
identify the site and coefficient universes or change the scalar small-Hom localization.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
@[instance_reducible]
def largeActionDerived : HasDerivedCategory.{u + 2} (Equivariant A H) :=
  HasDerivedCategory.standard _

/-- Restriction along the identity on the residual factor and the given group map.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def productMap (v : J →ₜ* H) : G × J →ₜ* G × H :=
  (ContinuousMonoidHom.fst G J).prod (v.comp (ContinuousMonoidHom.snd G J))

/-- The unique relative invariant inclusion for restriction, pinned before derivation.
Source: paragraph (3), step 5
(blueprint: def-sfb-relative-derived-invariants).
Proof: an H-fixed section is J-fixed after precomposition. The target invariant inclusion
is injective on all sections, so restricting its codomain gives the unique natural map. -/
theorem invariantRestrictionExist (v : J →ₜ* H) :
    ∃! b : (invariants A G H).functor ⟶
        inflate (R := A.toMon) (productMap (G := G) v) ⋙ (invariants A G J).functor,
      ∀ N, (b.app N).val ≫
          (invariants A G J).inclusion.app ((inflate (productMap (G := G) v)).obj N) =
        (invariants A G H).inclusion.app N := by
  sorry

/-- The actual natural inclusion of invariant submodules.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def invariantRestriction (v : J →ₜ* H) : (invariants A G H).functor ⟶
    inflate (R := A.toMon) (productMap (G := G) v) ⋙ (invariants A G J).functor :=
  Classical.choose (invariantRestrictionExist (A := A) (G := G) v)

/-- Derive the inclusion along exact restriction; this is the canonical derived mate.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def beta (v : J →ₜ* H) : derived A G H ⟶
    (inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory ⋙ derived A G J :=
  Functor.rightDerivedPullback
    (F := (invariants A G H).functor) (F' := (invariants A G J).functor)
    (inflate (productMap (G := G) v)) (invariantRestriction (A := A) (G := G) v)

/-- The sectionwise positive cyclic generator is an internal equivariant module map.
Source: paragraph (3), step 7
(blueprint: def-sfb-relative-derived-invariants).
Proof: the action of (1,1_Z) commutes with every residual G section, all restriction maps
and scalar multiplication. The fully faithful section-module equivalence assembles
these maps, and faithfulness proves uniqueness. -/
theorem generatorEndExist (N : Equivariant A (G × Z.{u})) :
    ∃! t : (retainResidual A G Z).obj N ⟶ (retainResidual A G Z).obj N,
      ∀ (S : Profinite.{u}) (x : Profinite.CondensedAction.sectionModule A.toMon N.module S),
        (t.val.hom.hom.app (op S)) x =
          (N.act S (ContinuousMap.const S (1, generator))).toFun x := by
  sorry

/-- The internal map T fixed by its generalized-section action.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def generatorEnd (N : Equivariant A (G × Z.{u})) :=
  Classical.choose (generatorEndExist N)

/-- The invariant inclusion with the residual action retained.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def invariantInclusion (N : Equivariant A (G × Z.{u})) :
    (invariants A G Z).functor.obj N ⟶ (retainResidual A G Z).obj N :=
  ⟨(invariants A G Z).inclusion.app N,
    fun S g x ↦ (invariants A G Z).residual N S g x⟩






/-- Relative restriction has the invariant-inclusion normalization on all complexes.
In particular H-zero on a module is precisely the original invariant-submodule inclusion.
Source: paragraph (3), step 5
(blueprint: def-sfb-relative-derived-invariants).
Proof: apply the derived-mate model equation with exact restriction and the identity
square of projection inflations. The defining underived mate is invariantRestriction. -/
theorem betaNormalization (v : J →ₜ* H) (N : CochainComplex (Equivariant A (G × H)) ℤ) :
    (unit A G H) N ≫
        (beta (A := A) (G := G) v).app (DerivedCategory.Q.obj N) ≫
        (derived A G J).map
          ((inflate (productMap (G := G) v)).mapDerivedCategoryFactors.hom.app N) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (invariantRestriction (A := A) (G := G) v) (.up ℤ)).app N) ≫
        (unit A G J)
          (((inflate (productMap (G := G) v)).mapHomologicalComplex (.up ℤ)).obj N) := by
  sorry

/-- The normalized restriction is compatible with shifts and thus triangle boundaries.
Source: paragraph (3), step 5
(blueprint: def-sfb-relative-derived-invariants).
Proof: restriction is the mate of the identity inflation square. The canonical derived
adjunction units and counits commute with shifts, so their composite mate does too. -/
theorem betaShift (v : J →ₜ* H) : NatTrans.CommShift (beta (A := A) (G := G) v) ℤ := by
  sorry

/-- The actual degree-zero computation unit under the single-complex identifications.
Its value is the ordinary unit transported by the canonical single/homology isomorphisms.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def degreeZeroUnit (N : Equivariant A (G × J)) :
    (invariants A G J).functor.obj N ⟶
      (DerivedCategory.homologyFunctor (Equivariant A G) 0).obj
        ((derived A G J).obj ((DerivedCategory.singleFunctor _ 0).obj N)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (Equivariant A G) 0).inv.app
      ((invariants A G J).functor.obj N) ≫
    (DerivedCategory.homologyFunctor (Equivariant A G) 0).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (invariants A G J).functor
          (.up ℤ) 0).inv.app N)) ≫
    (DerivedCategory.homologyFunctor (Equivariant A G) 0).map
      (unit A G J ((HomologicalComplex.single _ (.up ℤ) 0).obj N))

/-- H-zero of relative derived invariants is the original invariant functor, with its
identification fixed by the canonical right-derived computation unit.
Source: paragraph (3), step 5
(blueprint: def-sfb-relative-derived-invariants).
Proof: invariants are right adjoint to exact inflation and therefore left exact. In a
nonnegative injective resolution the kernel of its first invariant differential is the
original invariant submodule. This isomorphism carries the unit to its degree-zero
inclusion, and that equation determines it uniquely. -/
theorem degreeZeroExist :
    ∃! e : (DerivedCategory.singleFunctor (Equivariant A (G × J)) 0 ⋙ derived A G J) ⋙
        DerivedCategory.homologyFunctor (Equivariant A G) 0 ≅ (invariants A G J).functor,
      ∀ N, degreeZeroUnit N ≫ e.hom.app N = 𝟙 _ := by
  sorry

/-- The computation-unit-normalized relative degree-zero identification.
Source: paragraph (3) (blueprint: def-sfb-relative-derived-invariants). -/
def degreeZeroIso :
    (DerivedCategory.singleFunctor (Equivariant A (G × J)) 0 ⋙ derived A G J) ⋙
      DerivedCategory.homologyFunctor (Equivariant A G) 0 ≅ (invariants A G J).functor :=
  Classical.choose (degreeZeroExist (A := A) (G := G) (J := J))

/-- The actual H-zero restriction map is the inclusion of relative invariant submodules.
Source: paragraph (3), step 5
(blueprint: def-sfb-relative-derived-invariants).
Proof: apply H-zero to betaNormalization on the single complex and substitute the
normalization equations of degreeZeroIso on both sides. The two degree-zero computation
units are invertible by left exactness; cancel them to get precisely invariantRestriction. -/
theorem betaDegreeZero (v : J →ₜ* H) (N : Equivariant A (G × H)) :
    (DerivedCategory.homologyFunctor (Equivariant A G) 0).map
        ((beta (A := A) (G := G) v).app ((DerivedCategory.singleFunctor _ 0).obj N) ≫
          (derived A G J).map
            (((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategorySingleFunctor
              0).hom.app N)) ≫
      (degreeZeroIso (A := A) (G := G) (J := J)).hom.app
        ((inflate (R := A.toMon) (productMap (G := G) v)).obj N) =
    (degreeZeroIso (A := A) (G := G) (J := H)).hom.app N ≫
      (invariantRestriction (A := A) (G := G) v).app N := by
  sorry

end CategoryTheory.RelativeCyclic
