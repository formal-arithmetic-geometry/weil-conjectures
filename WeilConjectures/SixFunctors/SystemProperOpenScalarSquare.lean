/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.DiagramOpenClopenShiftModels
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.SixFunctors.SystemProperOpenScalarData
import all WeilConjectures.SixFunctors.SystemProperOpenScalarData
import WeilConjectures.CategoryTheory.ExchangeMateCube
import WeilConjectures.SixFunctors.ScalarIntrinsicAlphaCube
import WeilConjectures.SixFunctors.ScalarInverseImageCoherence
import all WeilConjectures.AlgebraicGeometry.DiagramOpenClopenShiftModels
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Scalar naturality of the intrinsic proper/open mate

Source: Zheng, Section 5, Lemma 5.13 and Constructions 5.14--5.15.
(blueprint: lem-sf-system-proper-open-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C}
    {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) [a.CommShift ℤ] [b.CommShift ℤ]
    (t : TwoSquare R₁ H G R₂) [NatTrans.CommShift t.natTrans ℤ] :
    NatTrans.CommShift ((mateEquiv a b).symm t).natTrans ℤ := by
  change NatTrans.CommShift
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight a.unit (G ⋙ L₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ t.natTrans) L₂ ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L₁ ⋙ H) b.counit ≫
      (Functor.rightUnitor _).hom) ℤ
  infer_instance

private theorem model_limits_of_flat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S)
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (hφ : ∀ U : Cᵒᵖ, (φ.hom.app U).hom.Flat) : PreservesFiniteLimits D.E := by
  exact scalarModel_limits_of_flat φ D hφ

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar

variable (A B : ℕ → CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n) (b : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (φ : ∀ n : ℕ, A n ⟶ B n)
  (hφ : ∀ n : ℕ, φ (n + 1) ≫ b n = a n ≫ φ n)
  (d : ℕ) (hd : 1 ≤ d) (e : Bases A B b φ d)

private theorem scalar_comp {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z)
    (M : Derived A a X) :
    (T A B a b φ hφ d hd e Z).map ((sComp A a v w).hom.app M) ≫
        (chi A B a b φ hφ d hd e (v ≫ w)).app M =
      (chi A B a b φ hφ d hd e w).app ((R A a v).obj M) ≫
        (R B b w).map ((chi A B a b φ hφ d hd e v).app M) ≫
        (sComp B b v w).hom.app ((T A B a b φ hφ d hd e X).obj M) := by
  let sw := TwoSquare.mk _ _ _ _ (ell A B a b φ hφ d hd e w).hom
  let sv := TwoSquare.mk _ _ _ _ (ell A B a b φ hφ d hd e v).hom
  let sc := TwoSquare.mk _ _ _ _ (ell A B a b φ hφ d hd e (v ≫ w)).hom
  have he : sc.whiskerLeft (pComp A a v w).hom =
      (TwoSquare.vComp sw sv).whiskerRight (pComp B b v w).hom := by
    ext N
    simpa [sc, sw, sv] using
      (scalarInverseImageCoherence A B a b φ hφ d hd e).1 v w N
  have hh := congrArg
    (mateEquiv ((adj A a w).comp (adj A a v)) (adj B b (v ≫ w))) he
  rw [conjugateEquiv_mateEquiv_vcomp
      ((adj A a w).comp (adj A a v)) (adj A a (v ≫ w)) (adj B b (v ≫ w))
      (pComp A a v w).hom sc,
    mateEquiv_conjugateEquiv_vcomp
      ((adj A a w).comp (adj A a v)) ((adj B b w).comp (adj B b v))
      (adj B b (v ≫ w)) (TwoSquare.vComp sw sv) (pComp B b v w).hom,
    mateEquiv_hcomp (adj A a w) (adj B b w) (adj A a v) (adj B b v)] at hh
  simpa [sc, sw, sv, chi, sComp, mateEquiv] using
    congrArg (fun t ↦ t.natTrans.app M) hh

private theorem scalar_id (X : Scheme.{u}) (M : Derived A a X) :
    (chi A B a b φ hφ d hd e (𝟙 X)).app M ≫
        (sId B b X).hom.app ((T A B a b φ hφ d hd e X).obj M) =
      (T A B a b φ hφ d hd e X).map ((sId A a X).hom.app M) := by
  let sc := TwoSquare.mk _ _ _ _ (ell A B a b φ hφ d hd e (𝟙 X)).hom
  let si := TwoSquare.vId (T A B a b φ hφ d hd e X)
  have he : sc.whiskerLeft (pId A a X).hom =
      si.whiskerRight (pId B b X).hom := by
    ext N
    simpa [sc, si] using
      (scalarInverseImageCoherence A B a b φ hφ d hd e).2 X N
  have hh := congrArg (mateEquiv Adjunction.id (adj B b (𝟙 X))) he
  rw [conjugateEquiv_mateEquiv_vcomp Adjunction.id (adj A a (𝟙 X))
      (adj B b (𝟙 X)) (pId A a X).hom sc,
    mateEquiv_conjugateEquiv_vcomp Adjunction.id Adjunction.id (adj B b (𝟙 X))
      si (pId B b X).hom] at hh
  have hm :
      (T A B a b φ hφ d hd e X).map ((sId A a X).inv.app M) ≫
          (chi A B a b φ hφ d hd e (𝟙 X)).app M =
        (sId B b X).inv.app ((T A B a b φ hφ d hd e X).obj M) := by
    simpa [sc, si, chi, sId, mateEquiv, Adjunction.id] using
      congrArg (fun t ↦ t.natTrans.app M) hh
  apply (cancel_epi
    ((T A B a b φ hφ d hd e X).map ((sId A a X).inv.app M))).mp
  rw [← Category.assoc, hm, Iso.inv_hom_id_app, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

private theorem scalar_ell_shift {X Y : Scheme.{u}} (v : X ⟶ Y) :
    NatTrans.CommShift (ell A B a b φ hφ d hd e v).hom ℤ := by
  let := extensionLimits A B a b φ hφ d hd e X
  let := extensionColimits A B a b φ hφ d hd e X
  let := extensionLimits A B a b φ hφ d hd e Y
  let := extensionColimits A B a b φ hφ d hd e Y
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryCompIso (E A B a b φ hφ Y) (pull B b v)).inv ≫
      (Functor.mapDerivedCategoryNatIso (ellOrdinary A B a b φ hφ v)).hom ≫
      (Functor.mapDerivedCategoryCompIso (pull A a v) (E A B a b φ hφ X)).hom) ℤ
  infer_instance

private theorem scalar_chi_shift {X Y : Scheme.{u}} (v : X ⟶ Y) :
    NatTrans.CommShift (chi A B a b φ hφ d hd e v) ℤ := by
  have := (Classical.choice
    (DiagramShift.diagramOpenClopenShiftModels A a)).direct_adjunction_shift v
  have := (Classical.choice
    (DiagramShift.diagramOpenClopenShiftModels B b)).direct_adjunction_shift v
  have := scalar_ell_shift A B a b φ hφ d hd e v
  exact NatTrans.CommShift.mateEquiv (adj A a v) (adj B b v) _

private theorem scalar_beta_shift {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : NatTrans.CommShift (beta A B a b φ hφ d hd e j).hom ℤ := by
  have := scalar_ell_shift A B a b φ hφ d hd e j
  have := NatTrans.CommShift.of_iso_inv (ell A B a b φ hφ d hd e j) ℤ
  have := DiagramShift.openAdjShift A a j
  have := DiagramShift.openAdjShift B b j
  have hb := betaInv_isIso A B a b φ hφ d hd e j
  have hi : NatTrans.CommShift (betaInv A B a b φ hφ d hd e j) ℤ :=
    inverse_mate_shift (jAdj A a j) (jAdj B b j) _
  have : NatTrans.CommShift (asIso (betaInv A B a b φ hφ d hd e j)).hom ℤ := by
    simpa only [asIso_hom] using hi
  exact NatTrans.CommShift.of_iso_inv
    (@asIso _ _ _ _ (betaInv A B a b φ hφ d hd e j)
      (betaInv_isIso A B a b φ hφ d hd e j)) ℤ

private theorem geometric_pull_congr_shift
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.CommShift (eqToIso (congrArg (P C τ) h)).hom ℤ := by
  subst g
  change NatTrans.CommShift (𝟙 (P C τ f)) ℤ
  infer_instance

private theorem geometric_open_congr_shift
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Scheme.{u}} {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) : NatTrans.CommShift (jCongr C τ h).hom ℤ := by
  subst g
  change NatTrans.CommShift (𝟙 (J C τ f)) ℤ
  infer_instance

private theorem geometric_square_shift
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) : NatTrans.CommShift (squareP C τ k r p i h).hom ℤ := by
  have := DiagramShift.pComp_shift C τ r i
  have := DiagramShift.pComp_shift C τ k p
  have := geometric_pull_congr_shift C τ h.symm
  dsimp only [squareP, Iso.trans_hom, Iso.symm_hom]
  infer_instance

private theorem geometric_beta_shift
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion r] [IsOpenImmersion p]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    NatTrans.CommShift (SemilinearProperOpen.beta C τ k r p i h hsq).hom ℤ := by
  have := geometric_square_shift C τ k r p i h
  have := NatTrans.CommShift.of_iso_inv (squareP C τ k r p i h) ℤ
  have he : SemilinearProperOpen.betaInv C τ k r p i h =
      ((mateEquiv (jAdj C τ p) (jAdj C τ r)).symm
        (TwoSquare.mk _ _ _ _ (squareP C τ k r p i h).inv)).natTrans := by
    ext M
    simp [SemilinearProperOpen.betaInv, betaInvApp, mateEquiv,
      Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have := DiagramShift.openAdjShift C τ p
  have := DiagramShift.openAdjShift C τ r
  have hb := SemilinearProperOpen.betaInv_isIso C τ k r p i h hsq
  have hi : NatTrans.CommShift (SemilinearProperOpen.betaInv C τ k r p i h) ℤ := by
    rw [he]
    exact inverse_mate_shift (jAdj C τ p) (jAdj C τ r) _
  have : NatTrans.CommShift
      (asIso (SemilinearProperOpen.betaInv C τ k r p i h)).hom ℤ := by
    simpa only [asIso_hom] using hi
  exact NatTrans.CommShift.of_iso_inv
    (@asIso _ _ _ _ (SemilinearProperOpen.betaInv C τ k r p i h)
      (SemilinearProperOpen.betaInv_isIso C τ k r p i h hsq)) ℤ

private theorem geometric_gamma_shift
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    NatTrans.CommShift (gamma C τ k r p i h) ℤ := by
  let s := StrictTower.squareLift k r p i h
  have := geometric_beta_shift C τ (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip
  have := DiagramShift.pi_shift C τ s
  have := DiagramShift.jComp_shift C τ s (pullback.fst p i)
  have := DiagramShift.pComp_shift C τ s (pullback.snd p i)
  have := NatTrans.CommShift.of_iso_inv (pComp C τ s (pullback.snd p i)) ℤ
  have := geometric_open_congr_shift C τ (pullback.lift_fst k r h)
  have := geometric_pull_congr_shift C τ (pullback.lift_snd k r h)
  -- The right unitor aligns the shift on P_q with the composite shift on P_q ⋙ 𝟭.
  let projection : P C τ (pullback.snd p i) ⋙ J C τ (pullback.fst p i) ⟶
      (P C τ (pullback.snd p i) ⋙ (P C τ s ⋙ J C τ s)) ⋙ J C τ (pullback.fst p i) :=
    Functor.whiskerRight
      (Functor.whiskerLeft (P C τ (pullback.snd p i)) (pi C τ s))
      (J C τ (pullback.fst p i))
  have hproj : NatTrans.CommShift projection ℤ := by
    have he : projection =
        Functor.whiskerRight
          ((Functor.rightUnitor (P C τ (pullback.snd p i))).inv ≫
            Functor.whiskerLeft (P C τ (pullback.snd p i)) (pi C τ s))
          (J C τ (pullback.fst p i)) := by
      ext M
      simp [projection]
    rw [he]
    infer_instance
  have ha : NatTrans.CommShift (alpha C τ k r p i h) ℤ := by
    unfold alpha
    infer_instance
  have := (Classical.choice
    (DiagramShift.diagramOpenClopenShiftModels C τ)).direct_adjunction_shift r
  have := (Classical.choice
    (DiagramShift.diagramOpenClopenShiftModels C τ)).direct_adjunction_shift p
  exact NatTrans.CommShift.mateEquiv (adj C τ r) (adj C τ p) _

/-- Scalar extension preserves the intrinsic noncartesian proper/open mate on the
ordinary unbounded derived category of strict systems, with composition and cochain shifts.
Source: Zheng 5.13 and Constructions 5.14--5.15, agent finite-free naturality argument;
Stacks 03DI, 0E8I, 0F7B (blueprint: lem-sf-system-proper-open-scalar-square).
Proof:
1. Compatible bases identify the underlying ordinary extension with d copies. It is
exact on whole systems, hence preserves acyclic complexes and quasi-isomorphisms;
its localization computes the K-flat derived extension for every unbounded input.
2. Inverse image and tensor preserve the same local pure tensors. Open balancing is
the open-unit transpose, so it and the geometric cartesian open comparison commute
on ordinary systems, retaining every transition t(m) tensor tau(b).
3. The intrinsic square lift is clopen even for noncartesian squares. Restriction
to it and its complement identifies systems with a product; tensor is componentwise
and commutes with the projector (1,0), including either empty component.
4. Substitute these equalities into the intrinsic alpha word (cartesian open
comparison, clopen projection, and compositors). Localization preserves their
composition and equality, giving the inverse-image scalar cube on whole derived systems.
5. Apply exchangeMate_cube with the four scalar functors, inverse-image comparisons
and open balancing. Its mates are precisely chi and the recorded gamma, yielding
the displayed equality without faithfulness of evaluation or scalar restriction.
6. The inverse-image tensor comparison obeys composition on ordinary tensors.
Mate pasting gives the chi composition equation with the canonical sComp, and its
identity equation. Whiskering the equality by an outer proper image is then valid.
7. The exact model has the termwise cochain shift with signed differential. The
ordinary comparisons commute degreewise with it. Right-adjoint shifts are the
counit-normalized mates of inverse-image shifts; uniqueness of adjoint shifts makes
units and counits compatible. Substitution in the mate words proves all shift clauses.
No constructibility, cartesianness, Tor bound or cohomological bound is used. -/
theorem systemProperOpenScalarSquare :
    (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A a U),
      (T A B a b φ hφ d hd e Z).map ((gamma A a k r p i h).app M) ≫
          (chi A B a b φ hφ d hd e p).app ((J A a k).obj M) ≫
          (R B b p).map ((beta A B a b φ hφ d hd e k).hom.app M) =
        (beta A B a b φ hφ d hd e i).hom.app ((R A a r).obj M) ≫
          (J B b i).map ((chi A B a b φ hφ d hd e r).app M) ≫
          (gamma B b k r p i h).app ((T A B a b φ hφ d hd e U).obj M)) ∧
    (∀ {X Y Z : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z) (M : Derived A a X),
      (T A B a b φ hφ d hd e Z).map ((sComp A a v w).hom.app M) ≫
          (chi A B a b φ hφ d hd e (v ≫ w)).app M =
        (chi A B a b φ hφ d hd e w).app ((R A a v).obj M) ≫
          (R B b w).map ((chi A B a b φ hφ d hd e v).app M) ≫
          (sComp B b v w).hom.app ((T A B a b φ hφ d hd e X).obj M)) ∧
    (∀ (X : Scheme.{u}) (M : Derived A a X),
      (chi A B a b φ hφ d hd e (𝟙 X)).app M ≫
          (sId B b X).hom.app ((T A B a b φ hφ d hd e X).obj M) =
        (T A B a b φ hφ d hd e X).map ((sId A a X).hom.app M)) ∧
    (∀ {X Y : Scheme.{u}} (v : X ⟶ Y),
      NatTrans.CommShift (ell A B a b φ hφ d hd e v).hom ℤ ∧
        NatTrans.CommShift (chi A B a b φ hφ d hd e v) ℤ) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
      NatTrans.CommShift (beta A B a b φ hφ d hd e j).hom ℤ) ∧
    (∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
      [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      NatTrans.CommShift (gamma A a k r p i h) ℤ ∧
        NatTrans.CommShift (gamma B b k r p i h) ℤ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U V W Z k i r p _ _ _ _ _ _ h M
    exact exchangeMate_cube (adj A a r) (adj A a p) (adj B b r) (adj B b p)
      (T A B a b φ hφ d hd e W) (T A B a b φ hφ d hd e U)
      (T A B a b φ hφ d hd e Z) (T A B a b φ hφ d hd e V)
      (ell A B a b φ hφ d hd e r).symm (beta A B a b φ hφ d hd e i)
      (beta A B a b φ hφ d hd e k) (ell A B a b φ hφ d hd e p).symm
      (alpha A a k r p i h) (alpha B b k r p i h)
      (scalarIntrinsicAlphaCube A B a b φ hφ d hd e k i r p h) M
  · exact scalar_comp A B a b φ hφ d hd e
  · exact scalar_id A B a b φ hφ d hd e
  · intro X Y v
    exact ⟨scalar_ell_shift A B a b φ hφ d hd e v,
      scalar_chi_shift A B a b φ hφ d hd e v⟩
  · exact scalar_beta_shift A B a b φ hφ d hd e
  · intro U V W Z k i r p _ _ _ _ _ _ h
    exact ⟨geometric_gamma_shift A a k i r p h,
      geometric_gamma_shift B b k i r p h⟩

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar
