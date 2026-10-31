/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTestProjection

/-! # K-flatness under étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The unbounded K-flat part of étale sum preservation, in the canonical
constant-ring coordinates. Source: Stacks Project, More on Étale Cohomology, Tag
0GKF, and its direct-sum total-tensor expansion
(blueprint: lem-pur-etale-sum-kflat-aux).

Proof: the canonical constant-scalar equivalence preserves the sheafified tensor
product, and being an equivalence preserves and reflects exactness, direct sums,
and acyclicity. It therefore identifies the ringed-site total tensor with the total
tensor of module-valued sheaves, including its differentials. Let B be an acyclic
complex on X. Exact inverse image makes its pullback acyclic. K-flatness of P says
that Tot(f^* B tensor P) is acyclic. The signed symmetry on the summand of bidegree
(p,q), x tensor y mapped to (-1)^(pq) y tensor x, identifies this with
Tot(P tensor f^* B). Both differential composites send x tensor y to
(-1)^(pq)(dy tensor x + (-1)^q y tensor dx). Exact sum extension preserves this
acyclicity. The canonical direct-sum totalization comparison identifies its image
with Tot((f_! P) tensor B); another signed symmetry puts B first. Transporting back
along the constant-scalar equivalence gives the required acyclic tensor test for
every B. Arbitrary integer degrees are allowed, since totalization uses direct
sums and sum extension is a left adjoint. Zero rings and empty sites satisfy the
same universal-property argument. -/
theorem etaleSum_preserves_kflat_aux {U X : Scheme.{u}} (f : U ⟶ X)
    [hf : Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] :
    letI := etaleConstantModuleFunctor_isEquivalence U A
    letI := etaleConstantModuleFunctor_isEquivalence X A
    letI := (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f hf).isLeftAdjoint
    ∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := U.smallEtaleTopology) (R :=
        (constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        (((etaleConstantModuleFunctor U A ⋙
          SheafOfModules.pushforward (F := 𝟭 U.Etale)
            (constantModuleHomRingIso U.smallEtaleTopology A).inv).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) →
      CochainComplex.IsKFlatIndependentCoefficients (J := X.smallEtaleTopology) (R :=
        (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
        (((etaleConstantModuleFunctor X A ⋙
          SheafOfModules.pushforward (F := 𝟭 X.Etale)
            (constantModuleHomRingIso X.smallEtaleTopology A).inv).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
          (((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) := by
  intro P hP B hB
  let Q := (etaleSumTensorTestInverseImageComplex f A).obj B
  have hQ : Q.Acyclic := etaleSumTensorTestInverseImageComplex_acyclic f A B hB
  obtain ⟨e⟩ := etaleSum_tensor_test_comparison f A B P
  have hsource := etaleSumTensorTestComplexExtension_acyclic f hf A
    (etaleSumTensorTestTotal U A Q
      ((etaleSumTensorTestRealizationComplex U A).obj P)) (hP Q hQ)
  intro n
  exact (hsource n).of_iso e.symm

end AlgebraicGeometry.Scheme
