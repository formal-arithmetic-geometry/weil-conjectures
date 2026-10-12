/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import Sheaf.Paper.InverseImageStalkGerm

/-! # Étale cohomology of a finite coproduct of geometric points

Source: literature/stacks-project/etale-cohomology.tex, Theorem 03QT, Lemma 03QU,
Section 03QQ and Lemma 0A5B (blueprint: lem-weil-pbc-finite-geometric-point-coproduct-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- Étale cohomology of a finite coproduct of geometric points.

Source: literature/stacks-project/etale-cohomology.tex, Theorem 03QT, Lemma 03QU,
Section 03QQ and Lemma 0A5B (blueprint: lem-weil-pbc-finite-geometric-point-coproduct-cohomology).

Proof: Restrict the sheaf to each open-and-closed point summand. The étale cohomology
of an algebraically closed geometric point vanishes in positive degrees and degree zero
is its geometric stalk, by `lem-weil-pbc-geometric-point-cohomology`. The étale site of
a finite coproduct is the finite product of the component sites, so global sections and
all derived functors are finite products, by `lem-weil-pbc-finite-coproduct-cohomology-assembly`.
The degree-zero map uses the canonical derived-to-underived comparison, followed by
global-section restriction and the product of the canonical stalk germs.
The stalk of each inverse-image restriction is identified with the original stalk by
`lem-weil-pbc-inverse-image-stalk-germ`.
-/
theorem finite_geometric_point_coproduct_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (I : Type u) [Finite I]
    (F : Sheaf (∐ fun _ : I => Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{u + 1})
    (c : ∀ i : I, Spec (.of k) ⟶ ∐ fun _ : I => Spec (.of k))
    (hc : ∀ i : I, c i = Sigma.ι (fun _ : I => Spec (.of k)) i) :
    (∀ q : ℕ, q > 0 →
      IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} (∐ fun _ : I => Spec (.of k)) (q : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    IsIso
      ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
          (Sheaf.Γ (∐ fun _ : I => Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})
          F 0).hom ≫
        (Functor.rightDerivedZeroIsoSelf
          (Sheaf.Γ (∐ fun _ : I => Spec (.of k)).smallEtaleTopology
            AddCommGrpCat.{u + 1})).hom.app F ≫
        F.ΓRes (op (Scheme.Etale.mk (𝟙 (∐ fun _ : I => Spec (.of k))))) ≫
        Pi.lift (fun i : I =>
          (pointSmallEtale (c i)).toPresheafFiber
            (Scheme.Etale.mk (𝟙 (∐ fun _ : I => Spec (.of k))))
            (Over.homMk (c i) (Category.comp_id (c i))) F.obj)) := by
  sorry

end AlgebraicGeometry
