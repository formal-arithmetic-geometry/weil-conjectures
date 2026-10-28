module
public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
  (S : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n) S)
  (adj : ∀ K : DerivedCategory
      (Modules.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)),
    (Functor.curry.obj S.tensor).obj K ⊣
      (Functor.curry.obj
        (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
          (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n))).obj (op K))

/-- The finite-level representative evaluation normalization is supplied by the same
closed tensor construction as the generic coefficient theorem.  The proof chooses
K-flat representatives and K-injective targets, then applies the sectionwise
currying calculation; the signs are those of the total-complex tensor.
Source: Stacks Tags 07A4, 07A6 and 08J9; blueprint paragraph 2.
(blueprint: new-sf-integral-hom-reduction-target-evaluation). -/
theorem finite_tensor_presentation_evaluation :
    ∀ (P I S' : CochainComplex (Modules.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) ℤ)
      (hP : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n) P)
      (hS : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n) S'),
      I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := integralCoefficientCommRingSheaf l E Y n) P I,
      ∃ beta : ((totalTensor.{t, u} Y
          (integralCoefficientCommRingSheaf l E Y n)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i + j)).val.app U
              (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
                P S' i j U x s) =
            (i * j).negOnePow • evaluate.{t, u} Y
              (integralCoefficientCommRingSheaf l E Y n) P I j i U
              ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫
              homModelMap.{t, u} Y
                (integralCoefficientCommRingSheaf l E Y n) P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  sorry
end WeilConjectures.IntegralHom
