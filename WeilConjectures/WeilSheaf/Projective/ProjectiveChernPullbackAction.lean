/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernNormalization
import WeilConjectures.WeilSheaf.Projective.ProjectiveChernHomTensor
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful

/-! # The native tensor action of the projective Cartier class

Source: current blueprint, rank-one Thom Step 1 and the projective-line calculation.
(blueprint: lem-pur-v5-projective-chern-pullback-action).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- Tensoring the native Cartier extension gives a shift-compatible pullback arrow.
This assertion involves no direct image and no calculation of projective cohomology.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, Cartier construction;
thm-pur-rank-one-thom Step 1; top-class node steps 1, 3 and the tensor part of step 8.
(blueprint: lem-pur-v5-projective-chern-pullback-action).

Proof: apply the given Construction to the Cartier ideal of infinity. Its nativeClass
is an arrow from the native unit to the positive root Tate line shifted by two. Use the
specified continuous-coefficient equivalence, with the inverse-image/Frobenius exchange,
to read it in the native category of all pro-etale Weil sheaves. This is an equivariant
construction on complexes, not a lift deduced from invariance of an ordinary arrow.
For K tensor this arrow with q*(K(-1)[-2]); the Cartesian root-line comparison, evaluation
of the inverse Tate line, and shift addition identify the endpoints with q*(K(-1)[-2])
and q*K. Localize the signed total tensor on native K-flat resolutions. Pullback and the
Tate line preserve the relevant quasi-isomorphisms, so the construction is natural in K.
Restrict to bounded constructible objects using the full inclusion. On a sheaf input,
forgetting and the specified encoding carry this arrow to tensor with the ordinary
Cartier arrow pulled from P1/X. The underived coefficient and root comparisons give the
two isomorphisms in ProjectiveChernNormalized, with the stated equality of whole derived
arrows. The tensor shift comparison has sign (-1)^(2*n)=1, so it agrees with the fixed
Tate/pullback shift comparisons. This gives NatTrans.CommShift. For a non-separated base,
use the ambient K-flat tensor construction, with exact open extension by zero to compare
its models on affine opens; do not assume separatedness of X. All constructions apply
to the empty scheme and the zero sheaf as well. -/
theorem exists_projectiveChern_pullback_action
    (C : ProEtale.NativeCartier.Construction k₀ l) :
    ∃ a : (tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) ⋙
          upperStar (ProjectiveLine X ↘ X) ⟶ upperStar (ProjectiveLine X ↘ X),
      NatTrans.CommShift a ℤ ∧ ∀ M : WeilSheaf k₀ l X,
        ProjectiveChernNormalized X C M (a.app (WeilSheaf.toComplex.obj M)) := by
  obtain ⟨H, ⟨ρ⟩⟩ := exists_projectiveChernHomModels (k₀ := k₀) (l := l) (ProjectiveLine X)
  obtain ⟨sU, sV, e, f, he, hf, hh⟩ := exists_projectiveChernHomEndpoints X H ρ
  let := sU
  let := sV
  let := he
  let := hf
  let T := tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)
  let P := upperStar (k₀ := k₀) (l := l) (ProjectiveLine X ↘ X)
  let I := (objectProperty k₀ l (ProjectiveLine X)).ι
  let : I.Faithful := by dsimp [I]; infer_instance
  let : I.CommShift ℤ := by dsimp [I]; infer_instance
  let : P.CommShift ℤ := by dsimp [P]; infer_instance
  let : T.CommShift ℤ := by dsimp [T]; infer_instance
  let h := projectiveChernNativePositiveClass X C
  let c := (Functor.curry.obj H).map h.op
  have : NatTrans.CommShift c ℤ := hh h
  let b : (T ⋙ P) ⋙ I ⟶ P ⋙ I :=
    e.hom ≫ Functor.whiskerLeft (P ⋙ I) c ≫ f.hom
  let a : T ⋙ P ⟶ P :=
    ((objectProperty k₀ l (ProjectiveLine X)).fullyFaithfulι.whiskeringRight _).preimage b
  have hab : Functor.whiskerRight a I = b :=
    ((objectProperty k₀ l (ProjectiveLine X)).fullyFaithfulι.whiskeringRight _).map_preimage b
  have : NatTrans.CommShift b ℤ := by dsimp [b]; infer_instance
  have : NatTrans.CommShift (Functor.whiskerRight a I) ℤ := by
    rw [hab]
    infer_instance
  refine ⟨a, NatTrans.CommShift.of_whiskerRight a I, fun M ↦ ?_⟩
  have ha := NatTrans.congr_app hab (WeilSheaf.toComplex.obj M)
  have hm := projectiveChernHom_normalized X H ρ C M
    (e.app (WeilSheaf.toComplex.obj M)) (f.app (WeilSheaf.toComplex.obj M))
  have heq : a.app (WeilSheaf.toComplex.obj M) =
      ObjectProperty.homMk
        ((e.app (WeilSheaf.toComplex.obj M)).hom ≫
          c.app ((P ⋙ I).obj (WeilSheaf.toComplex.obj M)) ≫
          (f.app (WeilSheaf.toComplex.obj M)).hom) := by
    apply ObjectProperty.hom_ext
    exact ha
  rw [heq]
  exact hm

end AlgebraicGeometry.WeilComplex
