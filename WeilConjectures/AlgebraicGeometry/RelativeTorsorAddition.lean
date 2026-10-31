/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeCocycleCoordinates
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Comma
import all WeilConjectures.AlgebraicGeometry.RelativeCocycleCoordinates
import all WeilConjectures.CategoryTheory.Sites.BinaryTorsorQuotient
/-! # Addition of relative torsor classes
Source: Stacks Project, Tag 03AJ, injective lifting-torsor argument.
(blueprint: lem-pur-relative-torsor-pairing-addition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace AlgebraicGeometry.Etale
local instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities

private theorem framed_lift_add (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (z₁ z₂ : ResolutionFramedLift T U I) :
    ∃ z : ResolutionFramedLift T U I, z.1 = z₁.1 + z₂.1 ∧
      z.2.1 = (show (I.cocomplex.X 0).obj.obj (op U) from z₁.2.1) +
        (show (I.cocomplex.X 0).obj.obj (op U) from z₂.2.1) ∧
      relativeFrameClass T U I z = relativeFrameClass T U I z₁ +
        relativeFrameClass T U I z₂ := by
  let z : ResolutionFramedLift T U I := ⟨z₁.1 + z₂.1,
    ⟨(show (I.cocomplex.X 0).obj.obj (op U) from z₁.2.1) +
        (show (I.cocomplex.X 0).obj.obj (op U) from z₂.2.1), by
      change (I.cocomplex.toCycles 0 1).hom.app (op U) (_ + _) =
        (I.cocomplex.cycles 1).obj.map _ (z₁.1 + z₂.1)
      rw [map_add, z₁.2.2, z₂.2.2, map_add]⟩⟩
  refine ⟨z, rfl, rfl, ?_⟩
  unfold relativeFrameClass
  erw [← map_add]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective
    ((relativeSectionComplex T U I.cocomplex).iCycles 1)).1 inferInstance
  rw [map_add, relativeFrameCycle_i, relativeFrameCycle_i, relativeFrameCycle_i]
  apply relative_coordinates_ext T U I.cocomplex 0
  · erw [(relativeFrameElement_coordinates T U I z).1, map_add, map_add,
      (relativeFrameElement_coordinates T U I z₁).1,
      (relativeFrameElement_coordinates T U I z₂).1]
  · erw [(relativeFrameElement_coordinates T U I z).2, map_add,
      (relativeFrameElement_coordinates T U I z₁).2,
      (relativeFrameElement_coordinates T U I z₂).2]
    change -(z₁.2.1 + z₂.2.1 : (I.cocomplex.X 0).obj.obj (op U)) = _
    exact neg_add _ _

/-- A pairing of abelian torsors equivariant in both inputs adds their pointed
relative cohomology classes.
Source: Stacks Project, Tag 03AJ, injective lifting-torsor proof.
(blueprint: lem-pur-relative-torsor-pairing-addition).
Proof: present the two torsors inside one injective resolution. Addition of the
ambient lifts lands in the lifting torsor of the sum of the two global cocycles.
The binary quotient universal property factors this pairing through the given
output torsor. Local equivariance makes the factor an isomorphism, carrying the
specified section to the sum of the specified lifts. The signed cone coordinates
are (iCycles(s),-b), so the resulting cycle and its homology class are the sums. -/
theorem relativeTorsorEquiv_add_of_equivariant (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (I : InjectiveResolution G)
    (P Q R : Sheaf.Torsor G)
    (m : ∀ A, P.sheaf.obj.obj A → Q.sheaf.obj.obj A → R.sheaf.obj.obj A)
    (hn : ∀ {A B} (f : A ⟶ B) x y, R.sheaf.obj.map f (m A x y) =
      m B (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y))
    (h₁ : ∀ A g x y, m A (P.vadd A g x) y = R.vadd A g (m A x y))
    (h₂ : ∀ A g x y, m A x (Q.vadd A g y) = R.vadd A g (m A x y))
    (τ₁ : P.sheaf.obj.obj (op U)) (τ₂ : Q.sheaf.obj.obj (op U)) :
    relativeTorsorEquiv T U I (Quotient.mk _ ⟨R, m (op U) τ₁ τ₂⟩) =
      relativeTorsorEquiv T U I (Quotient.mk _ ⟨P, τ₁⟩) +
      relativeTorsorEquiv T U I (Quotient.mk _ ⟨Q, τ₂⟩) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let hS := resolutionLiftSequence_shortExact T I
  let : Injective (I.cocomplex.X 0) := I.injective 0
  obtain ⟨s₁, ⟨e₁⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT hS P
  obtain ⟨s₂, ⟨e₂⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT hS Q
  let z₁ : ResolutionFramedLift T U I := ⟨s₁, e₁.iso.hom.hom.app (op U) τ₁⟩
  let z₂ : ResolutionFramedLift T U I := ⟨s₂, e₂.iso.hom.hom.app (op U) τ₂⟩
  obtain ⟨z, hz, hb, hc⟩ := framed_lift_add T U I z₁ z₂
  let S := Sheaf.Torsor.lifts hT hS z.1
  let a (A) (x : P.sheaf.obj.obj A) (y : Q.sheaf.obj.obj A) : S.sheaf.obj.obj A :=
    ⟨(show (I.cocomplex.X 0).obj.obj A from (e₁.iso.hom.hom.app A x).1) +
      (show (I.cocomplex.X 0).obj.obj A from (e₂.iso.hom.hom.app A y).1), by
      change (I.cocomplex.toCycles 0 1).hom.app A (_ + _) =
        (I.cocomplex.cycles 1).obj.map _ z.1
      rw [map_add, Sheaf.Torsor.lifts_val hT hS, Sheaf.Torsor.lifts_val hT hS,
        hz, map_add]
      rfl⟩
  have an {A B} (f : A ⟶ B) x y : S.sheaf.obj.map f (a A x y) =
      a B (P.sheaf.obj.map f x) (Q.sheaf.obj.map f y) := by
    apply Subtype.ext
    change (I.cocomplex.X 0).obj.map f (_ + _) = _
    rw [map_add]
    have h₁' := ConcreteCategory.congr_hom (e₁.iso.hom.hom.naturality f) x
    have h₂' := ConcreteCategory.congr_hom (e₂.iso.hom.hom.naturality f) y
    exact congrArg₂ (fun x y ↦ (show (I.cocomplex.X 0).obj.obj B from x.1) + y.1)
      h₁'.symm h₂'.symm
  have ae₁ A g x y : a A (P.vadd A g x) y = S.vadd A g (a A x y) := by
    apply Subtype.ext
    have h := congrArg Subtype.val (e₁.map_vadd A g x)
    change (show (I.cocomplex.X 0).obj.obj A from
      (e₁.iso.hom.hom.app A (P.vadd A g x)).1) =
      (show (I.cocomplex.X 0).obj.obj A from (e₁.iso.hom.hom.app A x).1) +
        (I.ι.f 0).hom.app A g at h
    change (show (I.cocomplex.X 0).obj.obj A from
      (e₁.iso.hom.hom.app A (P.vadd A g x)).1) + _ =
      ((show (I.cocomplex.X 0).obj.obj A from (e₁.iso.hom.hom.app A x).1) +
        (show (I.cocomplex.X 0).obj.obj A from (e₂.iso.hom.hom.app A y).1)) + _
    rw [h]
    abel
  have ae₂ A g x y : a A x (Q.vadd A g y) = S.vadd A g (a A x y) := by
    apply Subtype.ext
    have h := congrArg Subtype.val (e₂.map_vadd A g y)
    change (show (I.cocomplex.X 0).obj.obj A from
      (e₂.iso.hom.hom.app A (Q.vadd A g y)).1) =
      (show (I.cocomplex.X 0).obj.obj A from (e₂.iso.hom.hom.app A y).1) +
        (I.ι.f 0).hom.app A g at h
    change (show (I.cocomplex.X 0).obj.obj A from (e₁.iso.hom.hom.app A x).1) +
      (show (I.cocomplex.X 0).obj.obj A from
        (e₂.iso.hom.hom.app A (Q.vadd A g y)).1) =
      ((show (I.cocomplex.X 0).obj.obj A from (e₁.iso.hom.hom.app A x).1) +
        (show (I.cocomplex.X 0).obj.obj A from (e₂.iso.hom.hom.app A y).1)) + _
    exact (congrArg (fun t ↦ (show (I.cocomplex.X 0).obj.obj A from
      (e₁.iso.hom.hom.app A x).1) + t) h).trans (add_assoc _ _ _).symm
  obtain ⟨l, hl, _⟩ := Sheaf.Torsor.binaryTorsorQuotient_universal P Q R m hn h₁ h₂
    S.sheaf a (fun f x y ↦ an f x y) (fun A g x y ↦ by
      rw [ae₁, ae₂, ← S.add_vadd, add_neg_cancel, S.zero_vadd])
  let e := Sheaf.Torsor.Iso.ofHom l
    (Sheaf.Torsor.binary_factor_equivariant P Q R S m h₁ a ae₁ l hl)
  have hp : (Quotient.mk _ ⟨R, m (op U) τ₁ τ₂⟩ : Sheaf.Torsor.WithSection.Classes G U) =
      Quotient.mk _ z.toPair := by
    apply Quotient.sound
    refine ⟨e, ?_⟩
    apply Subtype.ext
    exact (congrArg Subtype.val (hl (op U) τ₁ τ₂)).trans hb.symm
  rw [hp, relativeTorsorEquiv_frame, relativeTorsorEquiv_presentation T U I ⟨P, τ₁⟩ s₁ e₁,
    relativeTorsorEquiv_presentation T U I ⟨Q, τ₂⟩ s₂ e₂]
  exact hc
end AlgebraicGeometry.Etale
