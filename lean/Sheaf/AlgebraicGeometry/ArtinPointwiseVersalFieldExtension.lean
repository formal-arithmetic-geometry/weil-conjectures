/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PointwiseVersalLifting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout

/-! # Pointwise versality after a finite residue-field extension

Source: Stacks Project, artin.tex, Tag 07XG, lemma-versal-change-of-field,
with Tag 07XF, definition-versal
(blueprint: lem-sfb-artin-pointwise-versal-field-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Versality at a finite type point survives every finite residue extension,
including inseparable extensions.

The square-zero hypothesis is written in the total-category form of the canonical
restriction equivalence. A span `a, b` consists of two objects with their specified
identification on the overlap. Its pushout glues these objects and all compatible
arrows. This is equivalent to equivalence of the restriction functor: essential
surjectivity glues objects and full faithfulness glues arrows. The base pushout
allows targets over any scheme, by pulling such a target back to its vertex. Thus
`IsPushout a b c d` imposes exactly the fibrewise condition, not an extra descent
hypothesis. This is the same encoding as algebraicModuliStack_rimSchlessinger,
but here the rings are arbitrary and the kernel is square-zero.

Source: Stacks Project, artin.tex, Tag 07XG, with Tags 07XF and 07WX;
formal-defos.tex, Tags 07W8 and 07WD
(blueprint: lem-sfb-artin-pointwise-versal-field-extension).

Proof:
1. For the given Artinian local surjection B' → B with residue L, put
   C = B ×_L k and C' = B' ×_L k. The residue-restriction lemma
   lem-sfb-artinian-finite-residue-restriction makes these Artinian local with
   residue k and makes C' → C surjective. All maps preserve their R-structures.
   Lem-weil-pbc-artinian-local-noetherian-nilpotent makes the maximal ideals
   of B and B' nilpotent.
2. Lem-sfb-affine-closed-pinching-pushout glues b : Spec B → U and the residue
   point Spec k → U to a_C : Spec C → U. Agreement of the two composites to S
   proves that this is an S-map.
3. For D = B or B', let D_r = D / m^r and C_r = D_r ×_L k. Induct on r to
   identify F(C_r) with the groupoid of compatible objects on k and D_r.
   The first case is the identity. The equality
   C_(r+1) = C_r ×_(D_r) D_(r+1) and the square-zero kernel m^r/m^(r+1)
   allow application of the assumed equivalence. Eliminate the intermediate
   D_r-object using its specified isomorphism. The same elimination on arrows
   proves full faithfulness. At a vanishing exponent this gives the actual
   restriction equivalences E_D, naturally with respect to B' → B.
4. Glue the given object eta over B' with x_u over k using the residue of the
   prescribed isomorphism theta. Essential surjectivity of E_B' gives w' over C'.
   Over C, full faithfulness of E_B lifts the compatible B-component theta
   and the chosen k-component to an isomorphism w'|_C ≅ a_C^*x.
5. Apply the assumed versality at u to C' → C with this exact isomorphism.
   Restrict the resulting lift and isomorphism to B'. Composing with the inverse
   of the identification w'|_B' ≅ eta gives the desired isomorphism; its reduction
   is theta by cancellation and the prescribed B-component in step 4. No
   separability is used. -/
theorem isVersalAtField_finite_residue_extension
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec (.of R)))) (hF : IsFibredInGroupoids F)
    (hRS : ∀ (A B C D : CommRingCat.{u})
      (sA : Spec A ⟶ Spec (.of R)) (sB : Spec B ⟶ Spec (.of R))
      (sC : Spec C ⟶ Spec (.of R)) (sD : Spec D ⟶ Spec (.of R))
      (q : C ⟶ A), Function.Surjective q.hom → (RingHom.ker q.hom) ^ 2 = ⊥ →
      ∀ (i : Over.mk sA ⟶ Over.mk sB) (j : Over.mk sA ⟶ Over.mk sC),
        j.left = Spec.map q →
      ∀ (k : Over.mk sB ⟶ Over.mk sD) (l : Over.mk sC ⟶ Over.mk sD),
        IsPushout i j k l →
      ∀ (x₀ : Functor.Fiber F.p (Over.mk sA))
        (y : Functor.Fiber F.p (Over.mk sB)) (z : Functor.Fiber F.p (Over.mk sC))
        (a : x₀.val ⟶ y.val) (b : x₀.val ⟶ z.val),
        F.p.IsHomLift i a → F.p.IsHomLift j b →
        ∃ (t : Functor.Fiber F.p (Over.mk sD)) (c : y.val ⟶ t.val) (d : z.val ⟶ t.val),
          F.p.IsHomLift k c ∧ F.p.IsHomLift l d ∧ IsPushout a b c d)
    (U : Over (Spec (.of R))) [LocallyOfFiniteType U.hom]
    (x : Functor.Fiber F.p U) (u₀ : U.left)
    (hft : LocallyOfFiniteType (U.left.fromSpecResidueField u₀) ∧
      QuasiCompact (U.left.fromSpecResidueField u₀))
    (hx : IsVersalAtField F x (U.left.residueField u₀) (U.left.fromSpecResidueField u₀))
    (L : Type u) [Field L] [Algebra (U.left.residueField u₀) L]
    [Module.Finite (U.left.residueField u₀) L] :
    IsVersalAtField F x L
      (Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField u₀) L)) ≫
        U.left.fromSpecResidueField u₀) := by
  sorry

end CategoryTheory
