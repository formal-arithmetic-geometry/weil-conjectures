/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernCoefficientSplitting

/-! # Tensoring the coefficient adjunct and changing normalized endpoints

Source: current blueprint, projective-line cohomology and the proper projection formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- Forget Frobenius and encode the coefficient action on the base heart.
Source: the specified native encoding, composed before localization
(blueprint: lem-pur-a3-projective-chern-tensor-factorization). -/
abbrev projectiveChernBaseSheafEncoding :=
  Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
    ProEtale.NativeEncoding.encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber

/-- The exact derived base encoding, restricted to bounded constructible objects.
Source: the specified exact native encoding
(blueprint: lem-pur-a3-projective-chern-tensor-factorization). -/
abbrev projectiveChernBaseEncoding :=
  (objectProperty k₀ l X).ι ⋙
    (projectiveChernBaseSheafEncoding (k₀ := k₀) (l := l) X).mapDerivedCategory

/-- Pull an ordinary base coefficient complex to the geometric fibre, then tensor
with the encoded inverse-Tate shifted input. This is an actual functor, without
any chosen comparison or cohomology data.
Source: geometric pullback and the proper projection formula
(blueprint: lem-pur-a3-projective-chern-tensor-factorization). -/
abbrev projectiveChernTensorTransport (M : WeilSheaf k₀ l X) :=
  (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).mapDerivedCategory ⋙
      tensorLeft ((projectiveChernBaseEncoding X).obj
        ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          (WeilSheaf.toComplex.obj M)))

/-- The encoded normalized adjunct is the tensor image of the coefficient adjunct,
up to invertible endpoints. The complementary coefficient line becomes an unshifted
sheaf. This is a comparison of whole arrows and contains no projective cohomology
calculation or assertion that the Chern component is invertible.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md, projection formula,
and sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, paragraph (1).
(blueprint: lem-pur-a3-projective-chern-tensor-factorization).

Proof: exact forgetting of fixed pairs and the specified ordinary encoding
compare the actual native pullback/direct-image adjunction with the ordinary
module adjunction, including its unit. Proper base change compares the ordinary
coefficient adjunct with its geometric-fibre pullback. The definition of
nativeClass is the exact derived image of the ordinary route under descent.
Forgetting its fixed-pair structure gives geometric-fibre inverse image, with
the unital source comparison and prescribed root comparison. The inverse native
encoding cancels by its unit and counit. These equations identify the class used by
ProjectiveChernNormalized with that base-changed ordinary coefficient class.
Tensor the adjunction unit and the class with the encoded shifted inverse-Tate
input. The proper projection formula identifies its target with the encoding
of Rq_*q*M. Cartesian pullback of the Tate line, inverse-line evaluation and
shift addition identify the complementary line with the encoding of M[0].
For arbitrary endpoint isomorphisms s and t in the normalization, compare them
with these canonical ones. Their differences are automorphisms of pulled-back
sheaves, shifted by minus two at the source. Degree-zero full faithfulness of
projective-line pullback on sheaves descends both automorphisms to the base;
this follows from the degree-zero projective-line unit calculation and does
not assert full faithfulness on all derived objects. Naturality of the actual
adjunction unit then absorbs these automorphisms into the two displayed endpoint
isomorphisms. The complementary-line isomorphism is unchanged. For a qcqs base
work on affine opens to verify the canonical base-change and projection maps
are isomorphisms; their defining global maps and the sheaf Hom identification
supply the global comparisons, without gluing arbitrary derived morphisms.
All operations preserve the empty base and zero input. -/
theorem projectiveChern_tensor_factorization
    (C : ProEtale.NativeCartier.Construction k₀ l) (M : WeilSheaf k₀ l X)
    (a : (upperStar (ProjectiveLine X ↘ X)).obj
        ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          (WeilSheaf.toComplex.obj M)) ⟶
      (upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M))
    (ha : ProjectiveChernNormalized X C M a) :
    ∃ s : (projectiveChernBaseEncoding X).obj
        ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          (WeilSheaf.toComplex.obj M)) ≅
        (projectiveChernTensorTransport X M).obj
          (projectiveChernCoefficientUnit (l := l) X),
    ∃ t : (projectiveChernTensorTransport X M).obj
        ((ProEtale.CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj l) (ProjectiveLine X ↘ X)).obj
            ((projectiveChernCoefficientLine (l := l) (ProjectiveLine X))⟦(2 : ℤ)⟧)) ≅
        (projectiveChernBaseEncoding X).obj
          ((derivedLowerStar (ProjectiveLine X ↘ X)).obj
            ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M))),
    ∃ z : (projectiveChernTensorTransport X M).obj
        ((projectiveChernCoefficientLine (l := l) X)⟦(2 : ℤ)⟧) ≅
        (projectiveChernBaseEncoding X).obj (WeilSheaf.toComplex.obj M),
      (projectiveChernBaseEncoding X).map
          ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
            (ProjectiveLine X ↘ X)).homEquiv _ _ a) =
        s.hom ≫ (projectiveChernTensorTransport X M).map
          (projectiveChernCoefficientAdjunct X C) ≫ t.hom := by sorry

end AlgebraicGeometry.WeilComplex
