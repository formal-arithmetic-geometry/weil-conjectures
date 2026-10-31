/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernNormalization
public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernHomModels

/-! # Unit and Tate endpoints of native derived Hom

These comparisons concern the coefficient objects, independently of a Cartier class.
(blueprint: lem-pur-b3-projective-chern-hom-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedForgetTwoInjective

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The coefficient source of the native Cartier class, before ordinary encoding.
Source: the native Cartier unit (blueprint: lem-pur-b3-projective-chern-hom-endpoints). -/
abbrev projectiveChernHomUnit :=
  (DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)) 0).obj
    (projectiveChernNativeUnit (k₀ := k₀) (l := l) X)

/-- The shifted coefficient target of the native Cartier class.
Source: the positive native Tate line
(blueprint: lem-pur-b3-projective-chern-hom-endpoints). -/
abbrev projectiveChernHomTate :=
  ((DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)) 0).obj
    (projectiveChernNativeTate (k₀ := k₀) (l := l) X))⟦(2 : ℤ)⟧

/-- Unit and inverse-Tate duality identify the two Hom slices with the required endpoints.

Source: the inverse Tate evaluation and shift comparison in the tensor-Chern construction;
Stacks 0A95 and 08J7; the native single-source Hom comparison and constant-twist formulas.
(blueprint: lem-pur-b3-projective-chern-hom-endpoints).

Proof: the specified inverse native encoding takes the descended coefficient unit to
adicConstant, and the descended positive root line to the positive Tate sheaf. This follows
from its Frobenius exchange, which is the same pullback of continuous coefficient functions
and compatible roots. Compute Hom from each degree-zero coefficient on a K-injective target
using the projection to source degree zero. Hom from the unit is the identity. Hom from the
positive Tate line is the negative constant twist; moving its source shift [2] to the target
gives [-2]. The lisse pullback comparison moves that twist through q*. These comparisons
are natural on K-injective representatives and therefore descend to all derived maps.
Transport them to H using its normalized representatives. The target shift on the Hom
complex is functorial in the source, so precomposition commutes with it. The source shift
[2] changes the interchange sign by (-1)^(2*n)=1; hence the two endpoint isomorphisms commute
with the fixed shifts on Tate twist and pullback. No separatedness or constructibility of
intermediate resolutions is used. Zero objects and the empty base use the same formulas. -/
theorem exists_projectiveChernHomEndpoints
    (H : (DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)))ᵒᵖ ×
        DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)) ⥤
          DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)))
    (ρ : Representatives
      (standardHomModel (ProEtaleWeilSheaf.ihomBifunctor k₀ l (ProjectiveLine X))).complex H) :
    let U := (Functor.curry.obj H).obj (op (projectiveChernHomUnit (l := l) X))
    let V := (Functor.curry.obj H).obj (op (projectiveChernHomTate (l := l) X))
    let P := upperStar (k₀ := k₀) (l := l) (ProjectiveLine X ↘ X)
    let I := (objectProperty k₀ l (ProjectiveLine X)).ι
    let T := tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)
    letI : I.CommShift ℤ := by dsimp [I]; infer_instance
    letI : P.CommShift ℤ := by dsimp [P]; infer_instance
    letI : T.CommShift ℤ := by dsimp [T]; infer_instance
    ∃ sU : U.CommShift ℤ, ∃ sV : V.CommShift ℤ,
      letI := sU
      letI := sV
      ∃ (e : (T ⋙ P) ⋙ I ≅ (P ⋙ I) ⋙ V)
        (f : (P ⋙ I) ⋙ U ≅ P ⋙ I),
        NatTrans.CommShift e.hom ℤ ∧ NatTrans.CommShift f.hom ℤ ∧
        ∀ h : projectiveChernHomUnit (l := l) X ⟶ projectiveChernHomTate (l := l) X,
          NatTrans.CommShift ((Functor.curry.obj H).map h.op) ℤ := by sorry

end AlgebraicGeometry.WeilComplex
