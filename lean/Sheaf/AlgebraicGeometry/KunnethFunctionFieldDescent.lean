module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

/-! The generic-field descent used by the Kunneth failure witness. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A nonzero cyclic higher direct image on an algebraically closed extension of the
function field descends to the generic fibre over the function field itself.
Source: Stacks Project, Lemma 59.90.3, Tag 0F1D, using Lemma 59.90.2, Tag 0F0B;
blueprint `lem-kun-0f1d` (blueprint: new-kunneth-function-field-descent).

The proof identifies the higher direct image with the sheafification of its cohomology
presheaf on affine etale objects.  For every such object, cohomological pullback along
the algebraically closed extension is bijective by the qcqs constant-coefficient
invariance theorem.  The resulting locally bijective presheaf morphism sheafifies to
an isomorphism, so nonvanishing descends to the generic fibre. -/
theorem exists_functionField_descent_of_algClosedWitness
    {S' X' : Scheme.{u}} {f' : X' ⟶ S'}
    (_hAff : IsAffine S') (_hInt : IsIntegral S')
    (_hNorm : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
    (_hAlg : IsAlgClosed S'.functionField)
    {K : Type u} [_hField : Field K] [_hKAlg : IsAlgClosed K]
    (i : S'.functionField ⟶ CommRingCat.of K) {Y : Scheme.{u}}
    (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X')
    (_hsq : ChosenCartesianSquare h e f' (Spec.map i ≫ S'.fromSpecStalk (genericPoint S')))
    (q : ℕ) (n d : ℕ) (hn : 0 < n) (hd : d ∣ n)
    (hne : ¬ IsZero
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))))))) :
    ∃ (Y₀ : Scheme.{u}) (e₀ : Y₀ ⟶ Spec S'.functionField) (h₀ : Y₀ ⟶ X')
      (_ : ChosenCartesianSquare h₀ e₀ f' (S'.fromSpecStalk (genericPoint S'))),
      ¬ IsZero
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h₀).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf Y₀.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) := by
  sorry

end AlgebraicGeometry.Etale
