module
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Prime-order module case used by finite-group devissage.

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
thm-fin-projective-curve-constant (blueprint: thm-fin-projective-curve-constant).

Proof in words: apply the prime module constructibility theorem and forget coefficients using
the derived comparison. (blueprint: lem-fin-projective-curve-finite-group-prime-cases). -/
theorem finite_group_prime_abelian_case
    (k : Type u) [Field k] (X S : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (f : X ⟶ S) [IsProjective f.left]
    (hdim : ∀ s : S.left,
      topologicalKrullDim (pullback f.left
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.left.residueField s) (AlgebraicClosure (S.left.residueField s)))) ≫
          S.left.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hinv : IsUnit (ℓ : Γ(S.left, ⊤))) (q : ℤ) :
    Scheme.IsConstructibleAbelianSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f.left).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry
end AlgebraicGeometry
