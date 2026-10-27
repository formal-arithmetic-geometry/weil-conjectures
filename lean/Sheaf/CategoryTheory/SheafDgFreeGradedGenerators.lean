module

public import Sheaf.CategoryTheory.SheafDgGeometricScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.CategoryTheory.Sites.InverseImageFreeModule
import Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Universal tensor flatness of free right dg sheaves

Source: Stacks Project, sdga.tex, Lemma 0FSG and Remark 0FSF
(blueprint: lem-sfb-sheaf-dg-free-graded-generators).

The fibre-family encoding of graded set sheaves retains arbitrary locally varying
integer degrees. The degreewise free-tensor functor is the reduced balanced tensor
formula from the first display of 0FSG. The final assertion identifies every model
of the geometric balanced tensor with the free module on the inverse-image fibres,
by a generator-normalized dg isomorphism. Its unit is natural in the generators.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafDg

/-- The free module on closed homogeneous generators is tensor-flat, tensor-acyclic
and remains so under every geometric scalar change.
Source: Stacks, sdga.tex, 0FSG, with construction in 0FSF
(blueprint: lem-sfb-sheaf-dg-free-graded-generators).

Proof: (1) Local sections of the sheafified direct sums are locally finite sums;
equalities hold locally already in the presheaf. Use the underlying-set
sheafification comparison and local bijectivity of its unit. (2) The maps
(sa) tensor n mapped to s(an) and sn mapped to s tensor n are balanced and inverse.
Extend the bilinear formulas through module sheafification; the differential on
sn is (-1)^degree(s) s dn. (3) For a short exact graded sequence, combine equal
restricted labels in each finite local representative. Kernels lift coefficient
by coefficient; injectivity is checked in the same way. Lift the finitely many
coefficients locally through the epimorphism, and refine the finitely many covers
using covering sieves and transitivity. This proves exactness of freeGradedTensor.
(4) For an acyclic N, the same refinement makes every coefficient of a cycle a
cycle. Lift each to a boundary and multiply its lift by (-1)^degree(s); their sum
bounds the original section. Thus all cohomology sheaves of rightTensor vanish.
(5) Write the degree-n free module as the sum of O[E_k] tensor A^(n-k).
Geometric inverse image preserves sums and fibres, since it is a left adjoint
and left exact. Apply the geometric free-module and tensor comparisons to each
summand; their pure-generator formulas respect the differential and action.
(6) Extend scalars by (sb) tensor b' mapped to s phi(b)b', with inverse
sb' mapped to (s1) tensor b'. The balanced relations and Leibniz signs verify the
inverse dg identities. These formulas give the stated universal property, unit
normalization and naturality. Any other balanced-tensor model has the unique
unit-preserving isomorphism by that universal property. Apply (3)--(4) on the
target site to obtain both tensor assertions there. No boundedness, points or
graded commutativity enter any step. -/
theorem freeRight_universally_tensorFlat
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J CommRingCat.{u}) (A : Algebra S)
    (E : GradedObject ℤ (Sheaf J (Type u))) :
    (∀ Q : ShortComplex (GradedObject ℤ (ringedSiteModules.{u} (rings S))),
      Q.ShortExact → (Q.map (freeGradedTensor S E)).ShortExact) ∧
    (∀ N : LeftModule A,
      ∃ i : rightTensor A (freeRight A E) N ≅ closedGenerators S E ⊗ N.X,
        rightTensorπ A (freeRight A E) N ≫ i.hom =
          (α_ (closedGenerators S E) A.X N.X).hom ≫
            (closedGenerators S E ◁ ModObj.smul (M := A.X) (X := N.X))) ∧
    (∀ N : LeftModule A, N.X.Acyclic → (rightTensor A (freeRight A E) N).Acyclic) ∧
    ∀ {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
      (T : Sheaf K CommRingCat.{u}) (f : RingedToposMorphism (rings T) (rings S))
      (B : Algebra T) (φ : PulledAlgebraMap f.inverse A B),
      (∀ Q : ShortComplex (GradedObject ℤ (ringedSiteModules.{u} (rings T))),
        Q.ShortExact →
          (Q.map (freeGradedTensor T ((pulledGradedSets f.inverse).obj E))).ShortExact) ∧
      (∀ N : LeftModule B, N.X.Acyclic →
        (rightTensor B (freeRight B ((pulledGradedSets f.inverse).obj E)) N).Acyclic) ∧
      ∃ a : ∀ F : GradedObject ℤ (Sheaf J (Type u)),
        PulledFamily f.inverse ((rightUnderlying A).obj (freeRight A F))
          ((rightUnderlying B).obj (freeRight B ((pulledGradedSets f.inverse).obj F))),
        (∀ F : GradedObject ℤ (Sheaf J (Type u)),
          IsGeometricScalarExtension φ (freeRight A F)
            (freeRight B ((pulledGradedSets f.inverse).obj F)) (a F) ∧
          IsFreeBaseChangeUnit F (a F)) ∧
        (∀ (F G : GradedObject ℤ (Sheaf J (Type u))) (e : F ⟶ G),
          pulledPost (a F) ((freeRightFunctor B).map ((pulledGradedSets f.inverse).map e)) =
            pulledPre ((freeRightFunctor A).map e) (a G)) ∧
        ∀ (M : RightModule B)
          (b : PulledFamily f.inverse ((rightUnderlying A).obj (freeRight A E))
            ((rightUnderlying B).obj M)),
          IsGeometricScalarExtension φ (freeRight A E) M b →
            ∃ i : M ≅ freeRight B ((pulledGradedSets f.inverse).obj E),
              pulledPost b i.hom = a E := by
  sorry

end CategoryTheory.SheafDg
