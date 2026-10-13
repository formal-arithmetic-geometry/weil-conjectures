/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Sheaf.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Descent of mixed total tensor rebracketing

Source: Stacks Project, Tag 0BYJ and Section 06Y5.
(blueprint: lem-pc-mixed-total-tensor-associator-descent).
-/

@[expose] public section

universe u wA wR

open CategoryTheory MonoidalCategory HomologicalComplex

namespace DerivedCategory

/-- A natural chain isomorphism between the two mixed total tensor trifunctors descends
through their K-flat models, with compatible natural comparison isomorphisms.
Source: Stacks Project, Tag 0BYJ, independence of K-flat resolutions; Section 06Y5.
(blueprint: lem-pc-mixed-total-tensor-associator-descent)

Proof: restrict Lc and Uc to K-flat triples and follow them by Q. For a
quasi-isomorphism in either A-variable, K-flatness of the other A-complex makes the
ordinary tensor map a quasi-isomorphism. The second clause of
CochainComplex.mixedTensor_kFlat_quasiIso, transported through the signed tensor flip,
then makes its mixed tensor with the K-flat R-complex a quasi-isomorphism. For a
quasi-isomorphism between K-flat R-complexes, the first clause applies to the arbitrary
A-complex given by the ordinary tensor. Thus the restriction of Lc inverts componentwise
quasi-isomorphisms after Q. Naturality of alpha and two-of-three for isomorphisms give
the same property for Uc; this avoids proving K-flatness of a mixed tensor.

For each module category, use ModuleCat.hasFunctorialFlatResolution and
localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions to show
that the K-flat inclusion followed by Q is a localization at quasi-isomorphisms
between K-flat complexes. The product of these localizations is a localization at
componentwise quasi-isomorphisms. Lift the two restricted functors along this product,
obtaining L and U and their lifting isomorphisms betaL and betaU. Full faithfulness of
precomposition with a localization lifts the restricted alpha to a unique gamma;
apply the same argument to its inverse to see that gamma is an isomorphism. The lifting
component equation is exactly the stated comparison. Equivalently one may curry and
use Localization.lift₃NatIso. This uses only K-flatness over the designated rings,
works for unbounded complexes, and preserves the A-action in the mixed tensor. -/
theorem exists_mixedTotalTensorAssociator_descent
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    let CA := CochainComplex (ModuleCat.{u} A) ℤ
    let CR := CochainComplex (ModuleCat.{u} R) ℤ
    let DA := DerivedCategory (ModuleCat.{u} A)
    let DR := DerivedCategory (ModuleCat.{u} R)
    let T := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex
    let S := ModuleCat.mixedTotalTensor (algebraMap R A)
    let Lc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₁₂ T S))
    let Uc := Functor.uncurry.obj (Functor.uncurry.obj (bifunctorComp₂₃ T S))
    let KA := CochainComplex.KFlat (ModuleCat.{u} A)
    let KR := CochainComplex.KFlat (ModuleCat.{u} R)
    let J : ((KA × KA) × KR) ⥤ ((CA × CA) × CR) :=
      ((CochainComplex.ιKFlat (ModuleCat.{u} A)).prod
        (CochainComplex.ιKFlat (ModuleCat.{u} A))).prod
          (CochainComplex.ιKFlat (ModuleCat.{u} R))
    let Qp : ((CA × CA) × CR) ⥤ ((DA × DA) × DR) :=
      ((Q (C := ModuleCat.{u} A)).prod (Q (C := ModuleCat.{u} A))).prod
        (Q (C := ModuleCat.{u} R))
    ∀ α : Lc ≅ Uc,
      ∃ (L U : ((DA × DA) × DR) ⥤ DA)
        (βL : J ⋙ Lc ⋙ Q ≅ J ⋙ Qp ⋙ L)
        (βU : J ⋙ Uc ⋙ Q ≅ J ⋙ Qp ⋙ U) (γ : L ≅ U),
        (∀ X : (KA × KA) × KR,
          (βL.hom.app X) ≫ γ.hom.app (Qp.obj (J.obj X)) =
            Q.map (α.hom.app (J.obj X)) ≫ βU.hom.app X) := by sorry

end DerivedCategory
