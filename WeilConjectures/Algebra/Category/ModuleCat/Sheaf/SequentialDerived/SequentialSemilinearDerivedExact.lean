/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Helper.SequentialSemilinearDerivedDiagramsDefs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedBoundary
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearHomNormalization
import WeilConjectures.CategoryTheory.Triangulated.TriangleSourceShiftHomExact

/-! Sequential semilinear derived vertex-edge exactness. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived
open Helper CategoryTheory.Pretriangulated

private theorem exact_transport
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (a : A ≃+ A') (b : B ≃+ B') (c : C ≃+ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (hf : ∀ x, f' (a x) = b (f x)) (hg : ∀ y, g' (b y) = c (g y))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨y, rfl⟩ := b.surjective y
  constructor
  · intro hy
    have hy' : g y = 0 := c.injective (by rw [map_zero, ← hg, hy])
    obtain ⟨x, hx⟩ := (h y).1 hy'
    exact ⟨a x, (hf x).trans (congrArg b hx)⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := a.surjective x
    have hx' : f x = y := b.injective ((hf x).symm.trans hx)
    rw [hg, (h y).2 ⟨x, hx'⟩, map_zero]


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [siteSmall : EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The coinduced two-term resolution gives the exact vertex-edge Hom sequence.
The proof constructs the degreewise augmentation and difference short exact sequence,
localizes its distinguished triangle, and applies the derived Hom exact sequence;
this is independent of the bounded-below realization construction.
Proof: form the locally finite coinduced product resolution, take its degreewise
augmentation and difference short exact sequence, pass to the localized derived
triangle, and apply Hom exactness; functoriality follows from the coinduced adjunction.
(blueprint: lem-sf-sequential-semilinear-derived-exact). -/
theorem sequentialSemilinearDerivedExact :
    ∃ δ : ∀ (M N : DerivedCategory (StrictRingSystem B)),
        HasCommonLowerBound B M → HasCommonLowerBound B N →
          edgeHom B M N (-1) →+ (M ⟶ N),
      (∀ (M N : DerivedCategory (StrictRingSystem B))
        (hM : HasCommonLowerBound B M) (hN : HasCommonLowerBound B N),
        Function.Exact (difference B M N (-1)) (δ M N hM hN) ∧
        Function.Exact (δ M N hM hN) (evaluateHom B M N) ∧
        Function.Exact (evaluateHom B M N) (difference B M N 0)) ∧
      (∀ (M M' N N' : DerivedCategory (StrictRingSystem B))
        (hM : HasCommonLowerBound B M) (hM' : HasCommonLowerBound B M')
        (hN : HasCommonLowerBound B N) (hN' : HasCommonLowerBound B N')
        (f : M' ⟶ M) (g : N ⟶ N') (x : edgeHom B M N (-1)),
        δ M' N' hM' hN' (edgeMap B f g (-1) x) =
          f ≫ δ M N hM hN x ≫ g) := by
  let δ : ∀ (M N : DerivedCategory (StrictRingSystem B)),
      HasCommonLowerBound B M → HasCommonLowerBound B N →
        edgeHom B M N (-1) →+ (M ⟶ N) := fun M N _ _ ↦
    (sourceShiftConnecting M ((Coinduced.boundary B).app N)).comp
      (Coinduced.edgeCoordinatesNeg B M N).symm.toAddMonoidHom
  refine ⟨δ, ?_, ?_⟩
  · intro M N hM hN
    have h := sourceShiftHom_exact (Coinduced.coinducedTriangle B N)
      (Coinduced.coinducedTriangle_distinguished B N) M
    refine ⟨?_, ?_, ?_⟩
    · exact exact_transport (Coinduced.vertexCoordinatesNeg B M N)
        (Coinduced.edgeCoordinatesNeg B M N) (AddEquiv.refl _)
        (postcomposeHom (M⟦(1 : ℤ)⟧) (Coinduced.difference B N))
        (sourceShiftConnecting M ((Coinduced.boundary B).app N))
        (Helper.difference B M N (-1)) (δ M N hM hN)
        (fun x ↦ (Coinduced.vertexCoordinatesNeg_difference B x).symm)
        (fun x ↦ by
          change sourceShiftConnecting M ((Coinduced.boundary B).app N)
            ((Coinduced.edgeCoordinatesNeg B M N).symm
              ((Coinduced.edgeCoordinatesNeg B M N) x)) = _
          rw [AddEquiv.symm_apply_apply, AddEquiv.refl_apply])
        h.1
    · exact exact_transport (Coinduced.edgeCoordinatesNeg B M N)
        (AddEquiv.refl _) (Coinduced.vertexCoordinatesZero B M N)
        (sourceShiftConnecting M ((Coinduced.boundary B).app N))
        (postcomposeHom M (Coinduced.augmentation B N))
        (δ M N hM hN) (evaluateHom B M N)
        (fun x ↦ by
          change sourceShiftConnecting M ((Coinduced.boundary B).app N)
            ((Coinduced.edgeCoordinatesNeg B M N).symm
              ((Coinduced.edgeCoordinatesNeg B M N) x)) = _
          rw [AddEquiv.symm_apply_apply, AddEquiv.refl_apply])
        (fun x ↦ (Coinduced.vertexCoordinatesZero_augmentation B x).symm)
        h.2.1
    · exact exact_transport (AddEquiv.refl _) (Coinduced.vertexCoordinatesZero B M N)
        (Coinduced.edgeCoordinatesZero B M N)
        (postcomposeHom M (Coinduced.augmentation B N))
        (postcomposeHom M (Coinduced.difference B N))
        (evaluateHom B M N) (Helper.difference B M N 0)
        (fun x ↦ (Coinduced.vertexCoordinatesZero_augmentation B x).symm)
        (fun x ↦ (Coinduced.vertexCoordinatesZero_difference B x).symm)
        h.2.2
  · intro M M' N N' hM hM' hN hN' f g x
    let b := (Coinduced.edgeCoordinatesNeg B M N).symm x
    have hb : (Coinduced.edgeCoordinatesNeg B M' N').symm (edgeMap B f g (-1) x) =
        f⟦(1 : ℤ)⟧' ≫ b ≫ (Coinduced.relationsFunctor B).map g := by
      apply (Coinduced.edgeCoordinatesNeg B M' N').injective
      rw [AddEquiv.apply_symm_apply, Coinduced.edgeCoordinatesNeg_natural]
      simp only [b, AddEquiv.apply_symm_apply]
    change sourceShiftConnecting M' ((Coinduced.boundary B).app N')
      ((Coinduced.edgeCoordinatesNeg B M' N').symm (edgeMap B f g (-1) x)) = _
    rw [hb]
    exact sourceShiftConnecting_natural _ _ f g _
      ((Coinduced.boundary B).naturality g).symm b

end SheafOfModules.SequentialDerived
