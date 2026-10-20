module
public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupPrimeCases
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Prime-factor devissage for finite constant abelian coefficients.

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
cor-fin-projective-curve-finite-group (blueprint: cor-fin-projective-curve-finite-group).

Proof in words: Prime-factor induction on finite abelian groups; exact constant sheaf
sequences and the long exact sequence reduce the middle term to constructible kernels,
cokernels, and extensions. (blueprint: lem-fin-projective-curve-finite-group-devissage).

The proof filters a finite abelian group by prime-order cyclic subgroups. Exactness of
constant sheaves, the long exact derived-functor sequence, and the kernel/cokernel/extension
closure of constructible finite-coefficient sheaves reduce every quotient to a prime-order
cyclic coefficient. The latter is supplied by `hprime`; induction on the group order terminates.
-/
theorem finite_group_devissage_of_prime_module_case
    (k : Type u) [Field k] (X S : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (f : X ⟶ S) [IsProjective f.left]
    (hdim : ∀ s : S.left,
      topologicalKrullDim (pullback f.left
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.left.residueField s) (AlgebraicClosure (S.left.residueField s)))) ≫
          S.left.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (hprime : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (hinv : IsUnit (ℓ : Γ(S.left, ⊤))) (q : ℤ),
      Scheme.IsConstructibleAbelianSheaf
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf S.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f.left).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))))))
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (horder : IsUnit (Nat.card M : Γ(S.left, ⊤))) (q : ℤ) :
    Scheme.IsConstructibleAbelianSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.left.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f.left).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)))) := by
  sorry
end AlgebraicGeometry
