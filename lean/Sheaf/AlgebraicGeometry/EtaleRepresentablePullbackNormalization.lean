/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Yoneda

/-!
# Normalized pullback of representable small étale sheaves

Source: Stacks Project, Étale Cohomology, Tag 03Q1 (4), the displayed
adjunction/Yoneda proof; Sites and Sheaves, Tag 04D3
(blueprint: lem-asd-etale-representable-pullback-normalization).

Representable sheaves use Mathlib's `uliftYoneda` into `Type (u + 1)`,
matching the recorded inverse-image functor. The representing object is the
existing small-site base change. Its underlying scheme is `P.left ×[Y] X`,
the chosen fibre product with its projection to `X`.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The natural map `h_P ⟶ f_* h_{P'}` sends each arrow to its base change.
It is the existing `uliftYonedaMap`, viewed in the full category of sheaves.
Source: Stacks Project, Tag 03Q1 (4), displayed adjunction/Yoneda proof
(blueprint: lem-asd-etale-representable-pullback-normalization). -/
noncomputable def etaleRepresentableBaseChangeMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.Etale) :
    Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj P ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale)).obj
          (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P)) :=
  ObjectProperty.homMk
    (uliftYonedaMap.{u + 1} (MorphismProperty.Over.pullback @Etale ⊤ f) P)

/-- The canonical comparison is the adjunct of the map sending arrows to their base changes.
Source: Stacks Project, Tag 03Q1 (4), displayed adjunction/Yoneda proof
(blueprint: lem-asd-etale-representable-pullback-normalization). -/
noncomputable def etaleRepresentablePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.Etale) :
    (Scheme.etaleSetPullback f).obj (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj P) ⟶
      X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).homEquiv _ _).symm
      (etaleRepresentableBaseChangeMap f P)

/-- The natural Hom-bijection: apply the adjunction, evaluate at `id_P`, then apply
inverse Yoneda evaluation at the base-changed object. No arbitrary isomorphism is chosen.
Source: Stacks Project, Tag 03Q1 (4), the full displayed chain of Hom-bijections
(blueprint: lem-asd-etale-representable-pullback-normalization). -/
noncomputable def etaleRepresentablePullbackHomEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.Etale) (H : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((Scheme.etaleSetPullback f).obj (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj P) ⟶ H) ≃
      (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P) ⟶ H) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).homEquiv _ H).trans
      ((Y.smallEtaleTopology.uliftYonedaEquiv.{u + 1}).trans
        (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}).symm)

/-- The specified comparison is invertible, the Hom-bijection is natural in `H`, it sends
this comparison to the identity, the identity-section condition uniquely characterizes
this comparison, and the comparisons are natural in the representing étale object.

Source: Stacks Project, Tag 03Q1 (4), displayed adjunction/Yoneda proof; Tag 04D3
(blueprint: lem-asd-etale-representable-pullback-normalization).

Proof:
1. By lem-weil-pbc-etale-base-change-finite-limits, base change is a functor on the
   small étale sites. The representables are sheaves by
   lem-weil-pbc-small-etale-representable-presheaf-sheaf. Functoriality makes the
   sectionwise base-change map natural.
2. Compose the set adjunction of lem-weil-pbc-etale-inverse-image-algebraic-structures
   with the two Yoneda bijections of lem-galois-yoneda-hom-bijection. This is precisely
   etaleRepresentablePullbackHomEquiv; all three factors are natural in the sheaf.
3. The adjunct of the specified comparison is etaleRepresentableBaseChangeMap.
   At id_P it has value b_f(id_P) = id_{P'}. Injectivity of Yoneda evaluation gives
   the identity normalization; injectivity of adjunction followed by evaluation
   gives uniqueness with this identity-section condition.
4. By lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection, the natural Hom-bijection is
   composition with an isomorphism theta : h_{P'} ⟶ f⁻¹ h_P. The normalization says
   theta followed by the specified comparison is the identity, so that comparison
   is theta's inverse.
5. For t : P ⟶ Q, functoriality of base change gives commutativity of the square
   of the two adjuncts. Naturality and injectivity of the adjunction transfer it
   to the square of the comparisons. -/
theorem etaleRepresentablePullbackNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.Etale) :
    IsIso (etaleRepresentablePullbackComparison f P) ∧
      (∀ (H H' : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (a : (Scheme.etaleSetPullback f).obj (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj P) ⟶ H)
        (g : H ⟶ H'),
        etaleRepresentablePullbackHomEquiv f P H' (a ≫ g) =
          etaleRepresentablePullbackHomEquiv f P H a ≫ g) ∧
      etaleRepresentablePullbackHomEquiv f P
        (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P))
        (etaleRepresentablePullbackComparison f P) =
          𝟙 (X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P)) ∧
      (∀ d : (Scheme.etaleSetPullback f).obj (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj P) ⟶
          X.smallEtaleTopology.uliftYoneda.{u + 1}.obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P),
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (X.smallGrothendieckTopology @Etale)).homEquiv _ _ d).hom.app
            (op P) (ULift.up (𝟙 P)) =
              ULift.up (𝟙 ((MorphismProperty.Over.pullback @Etale ⊤ f).obj P))) ↔
          d = etaleRepresentablePullbackComparison f P) ∧
      (∀ (Q : Y.Etale) (t : P ⟶ Q),
        (Scheme.etaleSetPullback f).map (Y.smallEtaleTopology.uliftYoneda.{u + 1}.map t) ≫
            etaleRepresentablePullbackComparison f Q =
          etaleRepresentablePullbackComparison f P ≫
            X.smallEtaleTopology.uliftYoneda.{u + 1}.map
              ((MorphismProperty.Over.pullback @Etale ⊤ f).map t)) :=
  sorry

end AlgebraicGeometry
