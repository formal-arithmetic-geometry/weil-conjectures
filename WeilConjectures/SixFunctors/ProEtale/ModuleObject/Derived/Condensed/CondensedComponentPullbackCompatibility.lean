/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPointMonoidalFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentDerivedSymmetry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentLisseEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFinalScalarComparison

/-! # Component pullback and scalar compatibility on contractible affine schemes

Source: Hemo--Richarz--Scholbach, (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The component inverse image is coefficient compatible and gives the scalar
comparison square and lisse equivalence of HRS Proposition 4.3(3).

Source: Hemo--Richarz--Scholbach, (4.1), Proposition 4.3(3), and Remark 3.2
(blueprint: lem-zl-condensed-component-pullback-compatibility).

Proof: the universal property of the relative profinite test functor gives the
component site morphism and identifies its composite with restriction from the
condensed point. Take the adjunction mate of this identification and lift it to
abelian sheaves; uniqueness makes it monoidal. Applying it to the coefficient
ring gives alpha and beta with their displayed equality. Inverse image is exact
and commutes with the ordinary tensor product, so its termwise derived functor
is triangulated and symmetric monoidal and preserves the coefficient unit.
The finite-clopen refinement of covers makes the terminal pro-etale object
weakly contractible. The point-basis evaluation formula therefore identifies
its section ring with Lambda(pi_0 T), compatibly with constant sections.
In particular the composite R to Lambda(pi_0 T) to the section ring on T sends r to
`affineScalarSection`: represent r by the map from the constant abelian unit at the
point, pull it along the monoidal factorization beta, and evaluate on the image of 1.
Naturality of beta and its monoidal unit equation give exactly this formula, including
the specified sheafification-unit representative of 1. This is the scalar normalization
required of the section-ring isomorphism in `componentComparisons`. On
flat-term K-flat complexes, the ordinary pullback comparison and associativity
of balanced scalar tensors identify the two section-ring realization functors.
The inverse chain maps send b tensor (a tensor p) to ba tensor p and back to
b tensor (1 tensor p); these maps commute with differentials and chain maps.
K-flat tensor descent gives the natural square on unbounded derived categories.
Apply the contractible evaluation equivalences on the profinite component space
and on T. The square identifies component pullback on lisse objects with scalar
transport along the section-ring isomorphism, hence it is an equivalence.
Finally the same inverse-image factorization identifies the realizations from
the scalar ring at the point. Compose it with the scalar associativity square
to obtain the last displayed comparison in `componentComparisons`. The empty
scheme and the zero coefficient ring are included: all these module categories
and comparisons reduce to their zero objects. -/
theorem condensed_component_pullback_compatibility
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
    [(componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)]
    [(componentInverse T).Braided]
    [PreservesFiniteLimits (componentInverse T)]
    [PreservesFiniteColimits (componentInverse T)] :
    ∃ α : (componentInverse T).mapMon.obj
        (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
        Mon.mk (condensedRingObj Λ.X T),
      (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
            (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
        NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ.X) ∧
      componentComparisons Λ.X T α := by
  obtain ⟨β, hβ⟩ := component_point_monoidal_factorization T
  let := hβ
  let q := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} (affineComponentSpace T)
  let α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T) :=
    (Functor.mapMonCompIso (F := q) (G := componentInverse T)).symm.app (Mon.mk Λ.X) ≪≫
      (Functor.mapMonNatIso β).app (Mon.mk Λ.X)
  have hα : α.hom.hom = β.hom.app Λ.X := by
    change 𝟙 _ ≫ β.hom.app Λ.X = β.hom.app Λ.X
    exact Category.id_comp _
  refine ⟨α, ⟨β, hβ, hα⟩, ?_⟩
  obtain ⟨a, ha, ⟨square⟩, ⟨point⟩⟩ := component_section_realization Λ T α β hβ hα
  obtain ⟨braided⟩ := component_derived_symmetry Λ T α
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      (profiniteCoefficient Λ.X (affineComponentSpace T)))
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
  let := braided
  have htri : ∃ (_ : (componentDerived Λ.X T α).CommShift ℤ),
      (componentDerived Λ.X T α).IsTriangulated := by
    dsimp [componentDerived]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨htri, ⟨braided⟩, ⟨(Functor.Monoidal.εIso (componentDerived Λ.X T α)).symm⟩,
    ?_, a, ha, ⟨square⟩, ⟨point⟩, ?_⟩
  · obtain ⟨e, he⟩ := component_lisse_equivalence Λ.X T α a ⟨square⟩
    exact ⟨e, he⟩
  · exact component_final_scalar_comparison Λ.X T α a ⟨square⟩ ⟨point⟩


end AlgebraicGeometry.ProEtale.CondensedRing
