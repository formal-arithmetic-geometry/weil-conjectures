/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CoefficientSetup
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorShifts
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis

/-!
# Finite coefficient tensor–Hom exchange

Source: latest blueprint, sec-six-functors/sk-thm-sf-tensor-hom, order 3478.
(blueprint: lem-sf-tensor-hom)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Pretriangulated.Opposite CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The canonical shifts of the finite constructible exceptional inverse image
`nu_X^* f^times Rnu_Y,*` of def-weil-exceptional-inverse-image: the composite of the derived
comparison direct image shift, the etale right-adjoint shift of `f^times` (adjoint to the
canonical etale compact-support shift) and the derived comparison inverse image shift.
Source: def-weil-exceptional-inverse-image, finite-level formula; blueprint order 3478.
(blueprint: lem-sf-tensor-hom) -/
@[instance_reducible] def finiteExceptionalInverseImageCommShift
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    (ProEtale.rightDerivedUpperShriek Λ f).CommShift ℤ := by
  letI := (Etale.rightDerivedUpperShriekAdjunction Λ f).rightAdjointCommShift ℤ
  exact inferInstanceAs (((ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor ⋙
      Etale.rightDerivedUpperShriek Λ f ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory).CommShift ℤ)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The finite specialization of the published signed closed shift laws. Both clauses
are inherited from the finite conjunct; the auxiliary condensed argument is immaterial.
Source: lem-sf-condensed-derived-tensor-shifts, finite coefficient clause.
(blueprint: lem-sf-tensor-hom) -/
abbrev finiteSignedClosedShiftLaws (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) :
    SignedClosedShiftLaws
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (CondensedRing.condensedDerivedTensorShiftStructure
    (𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) X).2 A X

section ExchangeShifts

universe a b c d e g h i
variable {C₀ : Type a} {D₀ : Type b} {C : Type c} {D : Type d}
  [Category.{e} C₀] [Category.{g} D₀] [Category.{h} C] [Category.{i} D]
  [HasShift C₀ ℤ] [HasShift D₀ ℤ] [HasShift C ℤ] [HasShift D ℤ]

/-- The two exchange bifunctors with four shift structures fixed before the exchange.
The target-Hom and signed source-Hom structures are arguments supplied by the published
closed shift laws; only the exchange is quantified. Flip transport uses definitional
isomorphisms, independently of that exchange.
Source: blueprint lem-sf-tensor-hom, both shift clauses of Step 2.
(blueprint: lem-sf-tensor-hom) -/
@[irreducible] def tensorHomExchangeWithFixedShifts
    (I : C₀ ⥤ C) (J : D₀ ⥤ D) (Q : D ⥤ C) (S P : C ⥤ D)
    (H : Cᵒᵖ ⥤ C ⥤ C) (K : Dᵒᵖ ⥤ D ⥤ D)
    [I.CommShift ℤ] [I.op.CommShift ℤ] [J.CommShift ℤ] [Q.CommShift ℤ]
    [S.CommShift ℤ] [(I ⋙ S).op.CommShift ℤ] [P.CommShift ℤ]
    (tH : ∀ M : Cᵒᵖ, (H.obj M).CommShift ℤ)
    (tK : ∀ M : Dᵒᵖ, (K.obj M).CommShift ℤ)
    (sH : ∀ N : C, (H.flip.obj N).CommShift ℤ)
    (sK : ∀ N : D, (K.flip.obj N).CommShift ℤ) : Prop :=
  let F := (I ⋙ S).op ⋙ K ⋙ (Functor.whiskeringLeft _ _ _).obj J
  let G := I.op ⋙ H ⋙ (Functor.whiskeringLeft _ _ _).obj (J ⋙ Q) ⋙
    (Functor.whiskeringRight _ _ _).obj P
  let hN : ∀ M : C₀, (F.obj (op M)).CommShift ℤ := fun M ↦ by
    letI := tK (op (S.obj (I.obj M)))
    change (J ⋙ K.obj (op (S.obj (I.obj M)))).CommShift ℤ
    infer_instance
  let hN' : ∀ M : C₀, (G.obj (op M)).CommShift ℤ := fun M ↦ by
    letI := tH (op (I.obj M))
    change (J ⋙ Q ⋙ H.obj (op (I.obj M)) ⋙ P).CommShift ℤ
    infer_instance
  let hM : ∀ N : D₀, (F.flip.obj N).CommShift ℤ := fun N ↦ by
    letI := sK (J.obj N)
    let T := (I ⋙ S).op ⋙ K.flip.obj (J.obj N)
    letI : T.CommShift ℤ := by dsimp only [T]; infer_instance
    exact Functor.CommShift.ofIso (F := T) (Iso.refl _) ℤ
  let hM' : ∀ N : D₀, (G.flip.obj N).CommShift ℤ := fun N ↦ by
    letI := sH (Q.obj (J.obj N))
    let T := I.op ⋙ H.flip.obj (Q.obj (J.obj N)) ⋙ P
    letI : T.CommShift ℤ := by dsimp only [T]; infer_instance
    exact Functor.CommShift.ofIso (F := T) (Iso.refl _) ℤ
  ∃ iso : F ≅ G,
    (∀ M : C₀,
      letI := hN M
      letI := hN' M
      NatTrans.CommShift (iso.app (op M)).hom ℤ) ∧
    (∀ N : D₀,
      letI := hM N
      letI := hM' N
      NatTrans.CommShift (iso.hom.flipApp N) ℤ)

variable [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [(curriedTensor C).CommShift₂Int] [(curriedTensor D).CommShift₂Int]

/-- The exchange predicate specialized to closed internal Homs, with its four structures
pinned by the two clauses of the supplied published signed shift laws.
Source: blueprint lem-sf-tensor-hom, Step 2; SignedClosedShiftLaws clauses 1 and 2.
(blueprint: lem-sf-tensor-hom) -/
@[irreducible] def closedTensorHomExchangeWithFixedShifts
    (I : C₀ ⥤ C) (J : D₀ ⥤ D) (Q : D ⥤ C) (S P : C ⥤ D)
    [I.CommShift ℤ] [I.op.CommShift ℤ] [J.CommShift ℤ] [Q.CommShift ℤ]
    [S.CommShift ℤ] [(I ⋙ S).op.CommShift ℤ] [P.CommShift ℤ]
    (hC : SignedClosedShiftLaws C) (hD : SignedClosedShiftLaws D) : Prop :=
  tensorHomExchangeWithFixedShifts I J Q S P
    MonoidalClosed.internalHom MonoidalClosed.internalHom
    (fun M ↦ (hC.1 M.unop).choose) (fun M ↦ (hD.1 M.unop).choose)
    (fun N ↦ (hC.2 N).choose) (fun N ↦ (hD.2 N).choose)

end ExchangeShifts

/-- Tensor–Hom exchange at A_{E,n}, natural in the bounded constructible finite-Tor
arguments M and N, with both integer-shift squares. The finite exceptional inverse image
is the published `nu_X^* f^times Rnu_Y,*` of def-weil-exceptional-inverse-image on the
fixed-ring module sheaves, with its composite canonical shifts. All four fixed-variable
shift structures are fixed before the isomorphism;
in particular the signed M shifts come from clause 2 of SignedClosedShiftLaws, independently
of the exchange.

Source: latest blueprint, sec-six-functors/sk-thm-sf-tensor-hom, order 3478.
Proof steps (H8): (1) fix M,N and test against L on Y. (2) use tensor–Hom on Y to identify
Hom(L,RHom(Rf_!M,N)) with Hom(Rf_!M tensor L,N). (3) precompose with the inverse of the
canonical projection formula to obtain Hom(Rf_!(M tensor Lf^*L),N). (4) use the exceptional
adjunction, tensor–Hom on X, and Lf^* adjoint Rf_* to obtain
Hom(L,Rf_*RHom(M,f^!N)). (5) the exceptional adjunction is the published
rightDerivedUpperShriekHomEquiv on the bounded-below objects of etale origin, which contain
D^b_ctf. Yoneda gives the exchange, and
naturality of every arrow gives naturality in M and N. (6) carry the canonical target-Hom
and signed source-Hom shifts through these five arrows; the projection shift square and
unit/counit-compatible adjoint shifts give the two asserted CommShift equations.
(blueprint: lem-sf-tensor-hom) -/
/- STATEMENT-DISPUTED: the original helper orientation placed `Rf_!` outside the
internal Hom and `Rf_*` in its parameter. The blueprint exchange has the reverse
orientation, so the helper is repaired above; the remaining target still needs the
constructible Yoneda realization. -/
theorem sfTensorHomExchange
    (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k]
    [Fact (ringChar k ≠ ell)] (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left] :
    let A := Padic.coefficientExtensionRing ell E n
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    let B := ULift.{u + 1} A
    letI : HasCompactification f.left :=
      hasCompactification_of_finiteType_over_field k X.left Y.left f.left
    let Q := ProEtale.rightDerivedUpperShriek B f.left
    letI : Q.CommShift ℤ := finiteExceptionalInverseImageCommShift B f.left
    let CX := DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X.left
    let CY := DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) Y.left
    closedTensorHomExchangeWithFixedShifts CX.ι CY.ι Q
      (R(f.left)_![ModuleCat.{u + 1} B]) (R((f.left)_*[ModuleCat.{u + 1} B]))
      (finiteSignedClosedShiftLaws B X.left) (finiteSignedClosedShiftLaws B Y.left) := by
  sorry

end AlgebraicGeometry.ProEtale
