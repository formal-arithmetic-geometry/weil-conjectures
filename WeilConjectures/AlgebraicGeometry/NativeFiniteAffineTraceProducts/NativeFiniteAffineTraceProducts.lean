/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps

/-! # Native finite affine integration and exterior products

Source: sk-prop-tf-exceptional-external-kunneth, proof, Constant and lisse coefficients,
compatibility of the smooth trace with products, affine-projection substep.
(blueprint: lem-sf-native-finite-affine-trace-products).
The coefficient categories are ordinary, uncompleted native internal modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeFiniteAffineTraceProducts
open PurityTransport
open CompactificationReindexing RelativeKunneth

/-- The smooth geometric index of a separated finite-type arrow, retaining its
actual compactification. Source: smooth affine substep
(blueprint: lem-sf-native-finite-affine-trace-products). -/
abbrev datum {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y)
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) : GeneralPurityTransport.SmoothDatum k := by
  letI : X.obj.left.Over (Spec (.of k)) := ⟨X.obj.hom⟩
  letI : Y.obj.left.Over (Spec (.of k)) := ⟨Y.obj.hom⟩
  letI : f.hom.left.IsOver (Spec (.of k)) := ⟨f.hom.w⟩
  letI : IsSeparated f.hom.left := by
    have h : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
      simpa only [Over.w] using (inferInstanceAs (IsSeparated X.obj.hom))
    exact IsSeparated.of_comp f.hom.left Y.obj.hom
  letI : LocallyOfFiniteType f.hom.left := by
    have h : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
      simpa only [Over.w] using (inferInstanceAs (LocallyOfFiniteType X.obj.hom))
    exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  letI : QuasiCompact f.hom.left := by
    have h : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
      simpa only [Over.w] using (inferInstanceAs (QuasiCompact X.obj.hom))
    exact QuasiCompact.of_comp f.hom.left Y.obj.hom
  exact { X := X.obj, Y := Y.obj, map := f.hom.left, dim := d, compactification := c }

/-- The specified exterior pullback/tensor comparison. The normalized root
coordinates fix the Tate pullbacks. Multiplication is the recorded root-tower
multiplication with the usual even-shift tensorator; the middle interchange
is the derived braiding, so all Koszul signs are retained.
Source: canonical s in the affine product substep
(blueprint: lem-sf-native-finite-affine-trace-products). -/
def sourceComparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {k : Type u} [Field k] (G : ProductComparisons.Geometry k) (d₁ d₂ : ℕ)
    [∀ x : G.W.obj.left, Invertible (ell : G.W.obj.left.residueField x)]
    (p₁ : LinePullCoordinates ell c G.r₁.hom.left)
    (p₂ : LinePullCoordinates ell c G.r₂.hom.left)
    (L₁ : c.derived ell G.Y₁.obj.left) (L₂ : c.derived ell G.Y₂.obj.left) :
    exterior (c.bundled ell) G.source
      ((c.smoothSource ell G.f₁.hom.left d₁).obj L₁)
      ((c.smoothSource ell G.f₂.hom.left d₂).obj L₂) ≅
    (c.smoothSource ell (G.q ≫ G.v).hom.left (d₁ + d₂)).obj
      (exterior (c.bundled ell) G.target L₁ L₂) := by
  let Λ := c.bundled ell
  let f := (G.q ≫ G.v).hom.left
  let B₁ := (P Λ.X G.f₁.hom.left).obj L₁
  let B₂ := (P Λ.X G.f₂.hom.left).obj L₂
  let T₁ := c.derivedLine ell G.X₁.obj.left d₁
  let T₂ := c.derivedLine ell G.X₂.obj.left d₂
  let pure :=
    (pullPath Λ G.r₁.hom.left G.f₁.hom.left ((G.q ≫ G.v ≫ G.t₁).hom.left)
      (by
        rw [← G.path₁, Category.assoc, G.exchange₁.w, ← Category.assoc]
        rw [G.relativeProduct.w]
        rfl) L₁ ⊗ᵢ
      pullPath Λ G.r₂.hom.left G.f₂.hom.left ((G.q ≫ G.v ≫ G.t₂).hom.left)
        (by rw [← G.path₂, Category.assoc, G.exchange₂.w]; rfl) L₂) ≪≫
      ((CondensedRing.leftDerivedUpperStarComp Λ.X f G.t₁.hom.left).app L₁ ⊗ᵢ
        (CondensedRing.leftDerivedUpperStarComp Λ.X f G.t₂.hom.left).app L₂) ≪≫
      (Functor.Monoidal.μIso (P Λ.X f) _ _)
  let lines := (LinePullCoordinates.derived ell p₁ d₁ ⊗ᵢ
    LinePullCoordinates.derived ell p₂ d₂) ≪≫
    derivedProduct ell c G.W.obj.left d₁ d₂
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1})
      (condensedRingObj Λ.X G.W.obj.left))
  exact ((Functor.Monoidal.μIso (P Λ.X G.r₁.hom.left) B₁ T₁).symm ⊗ᵢ
      (Functor.Monoidal.μIso (P Λ.X G.r₂.hom.left) B₂ T₂).symm) ≪≫
    Functor.Monoidal.μIso (tensor _)
      ((P Λ.X G.r₁.hom.left).obj B₁, (P Λ.X G.r₁.hom.left).obj T₁)
      ((P Λ.X G.r₂.hom.left).obj B₂, (P Λ.X G.r₂.hom.left).obj T₂) ≪≫
    (pure ⊗ᵢ lines)

set_option maxHeartbeats 2000000 in
-- Elaborating the full counit equality exceeds the default budget through derived functor types.
end AlgebraicGeometry.ProEtale.NativeFiniteAffineTraceProducts
