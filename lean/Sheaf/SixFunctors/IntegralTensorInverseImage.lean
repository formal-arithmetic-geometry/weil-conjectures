/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.IntegralTensorProduct
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.IntegralTensorShriek

/-!
# Integral inverse image and uncompleted tensor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor/_section.md;
Stacks Project, Tags 09BP, 09BM and 09AA (blueprint: sk-lem-int-tensor).

The completed inverse-image comparison is expressed by its canonical derived-limit
triangle. We use powers of ell, cofinal with powers of a uniformizer of the finite
extension E. Finite reductions are mapping cones of multiplication by ell^(n+1)
on a complex representing K. The flat two-term resolution of O_E/ell^(n+1)
identifies these with ordinary derived reductions. The product leg is specified
by the cone inclusions. Thus no arbitrary comparison isomorphism is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- As in the upstream bounded-constructible module, keep internal Hom constructions opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- A concrete model of the uncompleted derived reduction of a complex P.
The two-term flat resolution [O_E --ell^(n+1)--> O_E] of O_E/ell^(n+1)
shows that this cone represents P tensor^L O_E/ell^(n+1), without any flatness
assumption on P. Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
abbrev integralFiniteComplex (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (ℓ ^ (n + 1) • 𝟙 P)

/-- The canonical finite reduction map, given by the inclusion into the mapping cone.
Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
def integralFiniteComplexQuotient (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :
    P ⟶ integralFiniteComplex ℓ E X P n :=
  CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 P)

/-- The finite-reduction transition is induced by the square with multiplication
by ell on the source and the identity on the target of the multiplication maps.
Source: Stacks 099M and 099N (blueprint: sk-lem-int-tensor). -/
def integralFiniteComplexTransition (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :
    integralFiniteComplex ℓ E X P (n + 1) ⟶ integralFiniteComplex ℓ E X P n :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    (ℓ ^ (n + 1 + 1) • 𝟙 P) (ℓ ^ (n + 1) • 𝟙 P)
    (fun j : ℤ ↦ ⟨j - 1, by simp⟩)
    { left := ℓ • 𝟙 P
      right := 𝟙 P
      w := by simp [pow_succ, mul_smul] }

/-- The canonical completion comparison is invertible precisely when its prescribed
product leg participates in the derived-limit triangle. A representing complex P
and its identification with K specify the canonical quotient maps; no arbitrary
comparison map is supplied. Finite terms are inverse images of the cone reductions,
which compute K tensor^L O_E/ell^(n+1). Exact restriction of scalars preserves
products and triangles and detects isomorphisms, so this is precisely the Stacks
completed inverse image after restriction to constant O_E.
Source: Stacks 099M and 099N(5) (blueprint: sk-lem-int-tensor). -/
def IntegralPullbackIsCompleted {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))) : Prop :=
  ∃ (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (c : Fan (fun n : ℕ ↦
      ((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj
        (DerivedCategory.Q.obj (integralFiniteComplex ℓ E Y P n)))) (hc : IsLimit c),
    ∃ δ : c.pt ⟶
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K)
          ⟦(1 : ℤ)⟧,
      Triangle.mk
        (hc.lift (Fan.mk _ (fun n ↦
          ((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).map
            (e.inv ≫ DerivedCategory.Q.map (integralFiniteComplexQuotient ℓ E Y P n)))))
        (𝟙 c.pt - @id (c.pt ⟶ c.pt) (hc.lift (Fan.mk c.pt (fun n ↦ c.π.app ⟨n + 1⟩ ≫
          ((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).map
            (DerivedCategory.Q.map (integralFiniteComplexTransition ℓ E Y P n))))))
        δ ∈ distTriang _

/-- Integral inverse image, its completed comparison, uncompleted tensor, extension by
zero for a quasi-compact open immersion, and closed direct image preserve Dbc.

Source: blueprint main-20261015, sk-lem-int-tensor; Stacks 09BP, 09BM and 09AA
(blueprint: sk-lem-int-tensor).

Proof:
1. Apply det-lem-int-tensor-shriek, part (1), to the open and closed immersions.
Its proof checks derived completeness as well as constructibility on each stratum.
Its part (2) gives finite open-closed devissage into locally perfect constant models.
2. Apply det-lem-int-tensor-pullback, parts (1)--(2). The first part preserves Dbc.
The second identifies the canonical comparison after restriction to constant O_E
with the derived limit of the inverse images of the finite reductions. Replace
uniformizer powers by the cofinal ell-power sequence. The defining quotient maps
are represented by integralFiniteComplexQuotient; the derived-limit triangle is the
one recorded by IntegralPullbackIsCompleted.
3. Apply the first paragraph of det-lem-int-tensor-product to K and L. This is the
ambient, uncompleted tensor defined by sk-def-sfb-derived-tensor-hom. The moreover
clause gives dualizability of the local models, so tensoring with them preserves
products, derived inverse limits and completeness. Finite devissage from step 1
therefore proves the tensor assertion without replacing it by completed tensor.
-/
theorem integralTensorInverseImage (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
          (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K) ∧
        IntegralPullbackIsCompleted ℓ E g K) ∧
    (∀ K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) L →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj L)) ∧
    (∀ (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E.val) j).mapDerivedCategory).obj K)) ∧
    (∀ (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
