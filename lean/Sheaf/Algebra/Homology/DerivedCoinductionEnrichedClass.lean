/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction

/-! # Global classes of the enriched coinduction comparison

Source: Stacks Project, dualizing.tex, Tags 0A70 and 0A71
(blueprint: lem-trf-derived-coinduction-enriched-class).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace ModuleCat

variable {S B : Type u} [CommRing S] [CommRing B]
  [HasDerivedCategory.{u} (ModuleCat.{u} S)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)]

/-- The normalized comparison determined on K-injective models by evaluation at one.
Source: Stacks 0A70 and 0A71
(blueprint: lem-trf-derived-coinduction-enriched-class). -/
def coinductionEnrichedHomIso (f : S →+* B) :
    coinductionHomLeft f ≅ coinductionHomRight f :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (algebraicShriek_derivedHom_adjunction f)))))

/-- The scalar map S[0] → U(B[0]), with the native unit and single-functor comparisons.
Source: Stacks 0A70 and 0A71
(blueprint: lem-trf-derived-coinduction-enriched-class). -/
def coinductionScalarUnit (f : S →+* B) :
    𝟙_ (DerivedCategory (ModuleCat.{u} S)) ⟶
      (restrictScalars f).mapDerivedCategory.obj (𝟙_ (DerivedCategory (ModuleCat.{u} B))) :=
  (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} S)).inv ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).map
      (ModuleCat.ofHom (Y := (restrictScalars f).obj (ModuleCat.of B B))
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun s t ↦ f.map_mul s t }) ≫
    ((restrictScalars f).mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of B B) ≫
    (restrictScalars f).mapDerivedCategory.map
      (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} B)).hom

/-- The normalized enriched coinduction comparison induces evaluation at one on global
classes: the identity corresponds to the counit. This concerns coinduction alone.
The displayed scalar map is the canonical S[0] → U(B[0]). The isomorphism is the
specific comparison characterized on K-injective models by
`algebraicShriek_derivedHom_adjunction`. The canonical comparison and scalar unit have
named definitions so applying this equation does not unfold the localization construction.

Source: Stacks Project, dualizing.tex, Tags 0A70 (lemma-right-adjoint) and
0A71 (lemma-RHom-ext), with the Hom-complex normalization of
lem-trf-algebraic-shriek-derived-hom-adjunction
(blueprint: lem-trf-derived-coinduction-enriched-class).

Proof:
Choose a K-injective S-complex I representing V. Its coinduction J is B-K-injective
by algebraicShriek_derivedHom_adjunction. Represent C(V) by J and its identity
by the identity chain map of J. The comparison on these representatives is the T
supplied by the same theorem. Its coordinate formula sends the degree-zero
identity cocycle to x ↦ x(1). A degree-zero cocycle gives
its class by the map from the single free rank-one module; the scalar map S → B
sends 1 to 1. Thus restricting the B-linear class and precomposing with this map
is exactly the S-linear class of the same cocycle, evaluated at one. The canonical
Hom-model comparisons are transposes of signed evaluation; degree-zero classes
have sign one, so their global-class maps are precisely curry'. Finally the
restriction/coinduction adjunction is the derived ordinary adjunction and its
inverse on these representatives also sends h to x ↦ h(x)(1). These two chain
maps are equal, not merely homotopic. The K-injective localization comparisons
therefore give the displayed equality. Naturality in the comparison isomorphisms
transports it back to V. Zero complexes, the identity ring map, the zero ring,
and non-flat ring maps require no additional hypotheses. -/
theorem derived_coinduction_enriched_class (f : S →+* B) :
    ∀ V : DerivedCategory (ModuleCat.{u} S),
      coinductionScalarUnit f ≫ (restrictScalars f).mapDerivedCategory.map
          (MonoidalClosed.curry' (𝟙 ((derivedCoinduction f).obj V))) ≫
        (coinductionEnrichedHomIso f).hom.app (op ((derivedCoinduction f).obj V), V) =
      MonoidalClosed.curry' ((derivedCoinductionAdjunction f).counit.app V) := by
  sorry

end ModuleCat
