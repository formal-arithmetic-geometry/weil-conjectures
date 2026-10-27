/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData
public import Sheaf.CategoryTheory.CyclicDerivedHomData

/-! # Native exceptional counit and the two outer Hom squares

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence; native left-model proof, Steps 1--2.
(blueprint: lem-sf-native-exceptional-counit-hom-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The normalized geometric counit has a native lift, and its maps on the two outer
terms of the cyclic Hom sequence are additive equivalences commuting with the boundary
and forgetting maps. No bijection on native Hom sets is asserted here.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence; Steps 1--2 of
lem-sf-native-exceptional-left-models.
(blueprint: lem-sf-native-exceptional-counit-hom-squares).

Proof: choose the native compactification of the model morphism. The exact open and
right-derived proper comparisons of lem-sf-native-weil-open-proper-forgetting
identify its ordinary compact-support functor and Frobenius action, including every
derived morphism. Transport along the algebraic-closure isomorphisms and the exact
section presentations. Compose with the inverse scalar-normalized comparison of
lem-sf-native-weil-scalar-frobenius-counit, then use full faithfulness of the
specified realizations to lift the resulting comparison to the given ForgetModels.
Refinement identifies this comparison with the operation of S at c; call it a.
The scalar counit theorem gives the invertible Frobenius mate on the ordinary
exceptional image of L. The action-realization part of
lem-sf-cyclic-derived-lifted-counit-represents realizes this object by a bounded
native H, with underlying identification e. Its invariant ordinary counit lifts to
d by surjectivity onto degree-zero invariants in the normalized cyclic Hom sequence.
In every degree the shifted ordinary adjunction and e give an additive Hom
equivalence. Frobenius compatibility makes it intertwine the cyclic action. Restrict
in degree zero to the kernel of 1-T and descend in degree minus one to the quotient
by its image: these are pZero and pMinus. Exact open extension, total right-derived
proper image, and their finite composite preserve the normalized boundary by
lem-sf-cyclic-derived-hom-exact-sequence. Follow this boundary square by naturality
under d to obtain the displayed left square, on quotient representatives and hence
on the quotient. Forgetting and its zero-shift comparison give the right square on
all native morphisms. These constructions do not use a native right adjoint or
faithfulness of derived forgetting. On empty schemes the same groups and maps are
zero; for identity compactifications the unit/counit equations give the same squares.
The supplied boundary families can be used because their normalization uniquely
identifies them with those in the functoriality theorem. -/
theorem native_exceptional_counit_hom_squares (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryExact _ bX ∧ CyclicDerivedHomBoundaryNatural _ bX ∧
      CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryExact _ bY ∧ CyclicDerivedHomBoundaryNatural _ bY ∧
      CyclicDerivedHomBoundaryNormalized _ bY) :
    ∃ a : nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F,
      ∀ L : W D l Y, ∃ (H : W D l X)
        (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
        (d : (nativeShriek D l f₀).obj H ⟶ L),
        VY.functor.map d = a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
          (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L) ∧
        ∀ K : W D l X,
          ∃ (pMinus : CyclicDerivedHomCoinvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj ≃+
              CyclicDerivedHomCoinvariants
                (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
                ((nativeShriek D l f₀).obj K).obj L.obj)
            (pZero : CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj ≃+
              CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
                ((nativeShriek D l f₀).obj K).obj L.obj),
            (∀ z,
              ((nativeShriek D l f₀).map (ObjectProperty.homMk
                (bX K.obj H.obj K.property.1 H.property.1 z)) ≫ d).hom =
              bY ((nativeShriek D l f₀).obj K).obj L.obj
                ((nativeShriek D l f₀).obj K).property.1 L.property.1 (pMinus z)) ∧
            (∀ (v : K ⟶ H)
              (z : CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj),
              z.val = cyclicDerivedForget _ K.obj H.obj v.hom →
              (pZero z).val = cyclicDerivedForget _
                ((nativeShriek D l f₀).obj K).obj L.obj
                ((nativeShriek D l f₀).map v ≫ d).hom) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
