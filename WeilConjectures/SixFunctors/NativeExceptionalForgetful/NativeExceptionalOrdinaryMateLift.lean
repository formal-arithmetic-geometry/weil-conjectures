/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalHomTransport
public import WeilConjectures.WeilSheaf.Localization

/-! # Realizing the ordinary exceptional transpose as a native morphism

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
final exceptional-adjunction sentence, ordinary counit identification.
(blueprint: lem-sf-native-exceptional-ordinary-mate-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The ordinary bounded constructible category on the native geometric fiber.
Source: the ordinary category in the exceptional-adjunction sentence.
(blueprint: lem-sf-native-exceptional-ordinary-mate-lift). -/
abbrev ordinaryCounitProperty (T : Space D) :=
  ProEtale.DerivedCategory.boundedAdicConstructible l
    (T.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber

/-- The ordinary object underlying a native Weil complex.
Source: WeilComplex.objectProperty_iff.
(blueprint: lem-sf-native-exceptional-ordinary-mate-lift). -/
abbrev ordinaryCounitObject (T : Space D) (K : W D l T) :
    (ordinaryCounitProperty D l T).FullSubcategory :=
  ⟨WeilComplex.forget.obj K, (WeilComplex.objectProperty_iff K.obj).mp K.property⟩

/-- Restriction of the actual, fixed open/proper functor, retaining its actual maps.
The preservation assertion is a proof parameter, rather than chosen data.
Source: native compact-support construction and its finiteness theorem.
(blueprint: lem-sf-native-exceptional-ordinary-mate-lift). -/
abbrev ordinaryCounitLeft {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (h : ∀ K, ordinaryCounitProperty D l X K →
      ordinaryCounitProperty D l Y ((counitOrdinaryShriek D l f₀).obj K)) :=
  (ordinaryCounitProperty D l X).liftFullSubcategory (ordinaryCounitProperty D l Y)
    (counitOrdinaryShriek D l f₀) h

/-- The invariant ordinary transpose has a native lift with the prescribed right-hand object.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
final exceptional-adjunction sentence, Frobenius realization of the exceptional image.

Proof: construct the scalar-normalized right Frobenius mate for the common-stage
exceptional adjunction, using the proper integral mate and the open restriction unit.
The two Frobenius counit equations make its scalar right-adjoint value an invertible
Frobenius object. Realize that object as a bounded constructible native Weil complex M;
the fixed-pair derived realization applies because the underlying cohomology is bounded
constructible. Scalar realization, section equivalence and change of algebraic closure
give the displayed common-stage identification b. Transport the ordinary adjunction
through these equivalences. Uniqueness of right adjoints identifies the underlying
object of M with G(L), giving d for the supplied adjunction, independently of any
comparison a on native morphisms. The Frobenius counit equation says that transposition
carries the invariant ordinary carrier to an invariant ordinary map H -> M. The
surjectivity at degree zero of the cyclic derived Hom exact sequence lifts this map
to a native morphism q. Cancel the degree-zero shift unitor to obtain the displayed
literal equality. No assertion that q or its underlying map is invertible is used
here. Empty schemes yield zero objects; the construction for the identity morphism
is the original action on L. Neither a comparison a, an identification of H with the
exceptional image, nor the transported-arrow equation is assumed.
(blueprint: lem-sf-native-exceptional-ordinary-mate-lift). -/
theorem native_exceptional_ordinary_mate_lift (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (h : ∀ K, ordinaryCounitProperty D l X K →
      ordinaryCounitProperty D l Y ((counitOrdinaryShriek D l f₀).obj K))
    (G : (ordinaryCounitProperty D l Y).FullSubcategory ⥤
      (ordinaryCounitProperty D l X).FullSubcategory)
    (adj : ordinaryCounitLeft D l f₀ h ⊣ G)
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (L : W D l Y) (H : W D l X)
    (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
      WeilComplex.forget.obj L)
    (hinv : (t ≫ (shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L)) ∈
      CyclicDerivedHomInvariants (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
        ((nativeShriek D l f₀).obj H).obj L.obj) :
    ∃ (M : W D l X)
      (b : VX.functor.obj M ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
      (d : ordinaryCounitObject D l X M ≅ G.obj (ordinaryCounitObject D l Y L))
      (q : H ⟶ M),
      ObjectProperty.homMk (WeilComplex.forget.map q) ≫ d.hom =
        adj.homEquiv (ordinaryCounitObject D l X H) (ordinaryCounitObject D l Y L)
          (ObjectProperty.homMk ((counitForgetComparison D l f₀).inv.app H ≫ t)) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
