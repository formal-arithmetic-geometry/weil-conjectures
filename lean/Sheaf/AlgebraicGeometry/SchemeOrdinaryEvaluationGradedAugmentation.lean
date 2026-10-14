/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module
public import Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import Sheaf.Algebra.Homology.HomComplexProjections
/-! # Degreewise ordinary evaluation and coefficient compatibility
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- A small component interface keeps the projection witness out of coproduct rewriting.
def schemeOrdinaryEvaluationGradedComponent {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (p q n : ℤ) (h : q + p = n) :
    letI := SheafOfModules.monoidalCategory R
    (homComplex (R := R) P N).X p ⊗ P.X q ⟶ N.X n :=
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  (β_ ((homComplex (R := R) P N).X p) (P.X q)).hom ≫
    (SheafOfModules.tensorHomEquiv (R := R) (P.X q)
      ((homComplex (R := R) P N).X p) (N.X n)).symm
      ((Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R)))
        P N p q n h)

-- Evaluation into an arbitrary coefficient complex, defined by coproduct descent.
def schemeOrdinaryEvaluationGraded (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (n : ℤ) : (pullbackTensorTotal Y (homComplex (R := Y.sheaf) P N) P).X n ⟶ N.X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := homComplex (R := Y.sheaf) P N) (K₂ := P) (F := curriedTensor _)
    (c := .up ℤ) (j := n) (fun p q h ↦
      schemeOrdinaryEvaluationGradedComponent (C := Opens Y) (J := Opens.grothendieckTopology Y)
        Y.sheaf P N p q n (by change p + q = n at h; omega))

/-- Degreewise ordinary evaluation commutes with a map to the fixed coefficient resolution.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation localization proof step 2.
(blueprint: lem-pc-scheme-ordinary-evaluation-graded-augmentation).

Proof: Fix total degree n. Use coproduct extensionality for the total tensor,
so it suffices to compare the composites from each summand with indices p,q
satisfying p+q=n. The component formula for schemeTensorHomUncurry identifies
the left composite with symmetry followed by inverse tensor-Hom adjunction
of Hom(P,g)^p followed by the projection to Hom(P^q,I^n), where I is the
fixed resolution of N. The coefficient naturality formula for the Hom
projections, applied with the identity of P and g, replaces this composite
by the projection to Hom(P^q,N^n) followed by homObjMap(id,g^n).
Naturality of the tensor-Hom equivalence in its coefficient identifies its
inverse with inverse adjunction of the latter projection followed by g^n.
Associativity and the coproduct descent equation give precisely the right
composite, proving the degreewise equality. This uses no differential
compatibility or monicity; it is an equality of graded maps for arbitrary
P,N and any coefficient map g to the fixed resolution. If either complex
is zero, or the scheme is empty, the same coproduct equations still apply.
The evaluation maps are explicit coproduct descents of the fixed product
projections; no evaluation map is chosen from an existence assertion. -/
theorem schemeOrdinaryEvaluationGraded_augmentation (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (g : N ⟶ (schemeHomKInjectiveResolution Y).obj N) (n : ℤ) :
    (schemeTensorHomUncurry Y (homComplex (R := Y.sheaf) P N) P N
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map g)).f n =
        schemeOrdinaryEvaluationGraded Y P N n ≫ g.f n := by sorry
end AlgebraicGeometry
