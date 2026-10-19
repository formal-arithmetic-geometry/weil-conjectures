/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Higher direct images for quasi-compact quasi-separated morphisms

Source: blueprint `sec-proper-base-change/sk-thm-iff`,
(blueprint: lem-weil-pbc-qcqs-higher-direct-image); Stacks Project, Tags 03Q8, 08BJ and 00WJ.

The cohomology of a complex of presheaves is sectionwise. Thus the presheaf in the second
clause below evaluates at `W` to `H^q(I(W ×_V U))`, with the induced restriction maps.
For a K-injective representative `I` of `K`, this is `H^q(W ×_V U, K|)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images of abelian sheaves are sheafified cohomology presheaves, and the
same description computes every degree of derived direct image using any K-injective
representative. The first presheaf is the cohomology presheaf of the landed
`AlgebraicGeometry.higherDirectImageSheafifiedPresheaf` (right derived evaluation with its
derived restriction maps), precomposed with étale base change: its value at `W` is
`H^q(W ×_V U, F|)`.
The second is the sectionwise cohomology of a K-injective representative, precomposed
with the same base-change functor. No termwise injectivity or strict boundedness of this
representative is required.

Source: blueprint `sec-proper-base-change/sk-thm-iff`,
(blueprint: lem-weil-pbc-qcqs-higher-direct-image); Stacks Project, Lemma 59.51.6 (03Q8).

Proof:
1. The ordinary-sheaf clause is the proved
   `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf`, specialized to `f`.
2. Put `C = f_* I` and let `L` be its underlying presheaf complex. Exact precomposition
   along etale base change identifies the presheaf in the second clause with `H^q(L)`.
3. Exact sheafification commutes with homology. Its counit identifies the sheafification
   of `L` with `C`, giving the sheafification of that presheaf as `H^q(C)`.
4. `Functor.rightDerivedFunctorObjQIso` computes the unbounded right derived functor
   on the given K-injective `I`. Transport along `Q(I) ≅ K.obj` and then along
   `Functor.rightDerivedFunctorPlusCompatibility`. Applying homology identifies
   `H^q(C)` with the bounded-below derived direct-image homology in the conclusion.
No strict bound or termwise injectivity of `I` is used. -/
theorem qcqs_higherDirectImage {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              { obj := fun Z ↦
                  ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                    (evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj Z).rightDerived q).obj F
                map := fun g ↦
                  (NatTrans.rightDerived
                    (Functor.whiskerLeft
                      (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
                      ((evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map g)) q).app F
                map_id := fun Z ↦ by
                  simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                    NatTrans.rightDerived_id, NatTrans.id_app]
                map_comp := fun g h ↦ by
                  simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                    NatTrans.rightDerived_comp, NatTrans.comp_app] }) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))) ∧
    ∀ (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (I : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      I.IsKInjective → Nonempty (DerivedCategory.Q.obj I ≅ K.obj) →
      ∀ q : ℤ, Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I).homology q) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K)) := by
  constructor
  · intro F q
    exact ⟨AlgebraicGeometry.higherDirectImageSheafifiedPresheaf f F q⟩
  · intro K I hI ⟨e⟩ q
    have : I.IsKInjective := hI
    let F := lowerStar AddCommGrpCat.{u + 1} f
    let ι := sheafToPresheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
    let a := presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
    let b := (MorphismProperty.Over.pullback @Etale ⊤ f).op
    let B := (Functor.whiskeringLeft V.Etaleᵒᵖ U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj b
    let J :=
      ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).obj I
    let C := (F.mapHomologicalComplex (.up ℤ)).obj I
    let L := (ι.mapHomologicalComplex (.up ℤ)).obj C
    let eP : b ⋙ J.homology q ≅ L.homology q :=
      ((J.sc q).mapHomologyIso B).symm
    let eC : (a.mapHomologicalComplex (.up ℤ)).obj L ≅ C :=
      (Functor.mapHomologicalComplexCompIso
        (sheafificationNatIso V.smallEtaleTopology AddCommGrpCat.{u + 1}).symm
        (.up ℤ)).app C ≪≫
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app C
    let eD : DerivedCategory.Q.obj C ≅
        (F.rightDerivedFunctorPlus.obj K).obj :=
      (F.rightDerivedFunctorObjQIso I).symm ≪≫ F.rightDerivedFunctor.mapIso e ≪≫
        (F.rightDerivedFunctorPlusCompatibility.app K).symm
    exact ⟨a.mapIso eP ≪≫ ((L.sc q).mapHomologyIso a).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso eC ≪≫
      ((DerivedCategory.homologyFunctorFactors _ q).app C).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eD⟩

end AlgebraicGeometry.Etale
