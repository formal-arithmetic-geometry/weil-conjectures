module
public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
/-! Split-off adjunction field for the integral tensor presentation.
Source: the tensor-Hom adjunction step in the blueprint proof.
(blueprint: lem-sf-integral-hom-models-exist-tensor) -/
@[expose] public section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
variable [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]
/-- Split-off field statement.

Proof: Use the generic closed symmetric monoidal derived structure and transport its
right-tensor adjunction across the symmetric braiding to obtain the required
left-tensor adjunction.
(blueprint: new-sf-integral-hom-models-exist-tensor-adjunction) -/
theorem tensor_presentation_adjunction
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (β : @SymmetricCategory (DerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl))) _ S.monoidal) :
    Nonempty (∀ K : DerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj
          (derivedInternalHomOfUniverses
            (AlgebraicGeometry.Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)) := by sorry
end WeilConjectures.IntegralHom
