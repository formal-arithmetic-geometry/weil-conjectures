/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison

/-! # Evaluation of a localized cocycle on the cohomology sheaf

Source: Stacks Project, Tag 03Q8, computation with an injective complex.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

/-- The homology section of a cocycle, evaluated at the free generator.
This construction uses the actual cycle map and transports homology along `r`.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-weil-pbc-source-localized-cocycle-homology). -/
noncomputable def sourceCocycleHomologySection {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    ((DerivedCategory.Plus.homologyFunctor _ n).obj K).obj.obj (op W) :=
  sourceFreeSectionsEquiv W _
    (L.liftCycles f (n + 1) (by simp) hf ≫ L.homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors _ n).inv.app L ≫
      (DerivedCategory.homologyFunctor _ n).map r.inv)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a localized single-source cocycle is its actual homology section.
This is a comparison on the base site, before taking stalks or restricting to any scheme.

Source: Stacks Project, Tag 03Q8, injective-complex computation.
(blueprint: lem-weil-pbc-source-localized-cocycle-homology).

Proof: the localization isomorphism sends the class of the single-source cocycle to
its chain map into the shifted complex, then applies the quotient and shift comparison.
Degree-zero homology of that map is the map on cycles followed by the homology quotient.
The single-complex homology identification removes the source single complex. The homology
shift comparison identifies the target with degree n homology of L. Naturality of the
localization factorization and the homology shift comparison transports this equality
along r inverse. Evaluation of the resulting sheaf morphism at the free generator is
sourceFreeSectionsEquiv, giving the displayed section. This works for every integer n;
zero cocycles give zero sections and boundaries give zero homology sections. -/
theorem sourceLocalizedCocycleHomology {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    (strictLocalCohomologyGermMap K n).app (op W)
      ((sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)
        K L r n).inv
        ((sourceClassDerivedHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)
          L n).hom (CohomologyClass.mk
            (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)))) =
      sourceCocycleHomologySection K L r n W f hf := by sorry

end AlgebraicGeometry.Etale
