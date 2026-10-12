/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The termwise coproduct representative has the coproduct universal property in the
derived category. This is the localization and coproduct part of the direct-sums lemma.
Source: Stacks Project, Injectives, Lemma 07D9 (1)-(2).
(blueprint: lem-pc-derived-ambient-direct-sums-cofan)

Proof: Sheaves of modules form a Grothendieck abelian category, so every complex
has a K-injective resolution. Given any target in the derived category, choose such a
resolution J. Morphisms into Q(J) are chain maps modulo homotopy. A chain map from
the termwise coproduct to J is uniquely specified by a family of chain maps K(i) to J:
the degreewise coproduct property assembles their components, and the chain-map
identities follow by precomposing with each coprojection. The same property assembles
a family of homotopies degreewise, so two assembled maps are homotopic exactly when
all their restrictions are homotopic. Consequently restriction is a bijection from
Hom(Q(∐ K), Q(J)) to the product of Hom(Q(K(i)), Q(J)). Transport the target along
its K-injective resolution and each source along e(i); the resulting restriction maps
are composition with the displayed legs from E(i) to Q(∐ K). These natural bijections
give the required colimit. For an empty family the product of Hom sets is a singleton;
for a singleton this construction gives the usual representative isomorphism. -/
theorem derivedAmbientDirectSumsCofan (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (K : I → CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : ∀ i : I, DerivedCategory.Q.obj (K i) ≅ E i) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ (e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  sorry

end AlgebraicGeometry
