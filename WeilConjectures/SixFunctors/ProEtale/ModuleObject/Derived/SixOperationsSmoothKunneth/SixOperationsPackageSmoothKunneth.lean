/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.ZetaSeries
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth exceptional Künneth compatibility data over the package field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
_section.md, clause (5), final sentence (blueprint: def-sf-smooth-kunneth-compatibility-data).

The setting is that of def-sf-setting: a field k (no finite-field datum), ell invertible
in k, and a finite ell-primary coefficient ring A (the finite stage A_{E,n} is such a ring),
as the recorded purity coefficient `Coefficient.finite`. Every object is a recorded one:
the shifted Tate line `Coefficient.derivedLine`, the twisted pullback
`Coefficient.smoothSource`, the root-normalized line pullback `derivedPull` with the
normalized coordinates of `linePullCoordinates_nonempty`, the line product
`derivedProduct`, the pullback tensorator `RelativeKunneth.pullTensor`, the pullback
compositors, and the exceptional Künneth map `ProductComparisons.alpha` over `Geometry k`.
The orientation gamma_f is the unique comparison of right adjoints of the same
compact-support functor: the explicit smooth adjunction of a purity family
(`GeneralPurityTransport.AdjunctionFamily`) and the constructible exceptional adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.SixOperationsSmoothKunneth

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]

/-- ell is invertible at every residue field of a k-scheme, transported from k through
the structure morphism. Source: def-sf-setting, char k ≠ ell
(blueprint: def-sf-smooth-kunneth-compatibility-data). -/
@[instance_reducible]
def residueInvertible (hEll : IsUnit (ell : k)) (X : SepFinType k) :
    ∀ x : X.obj.left, Invertible (ell : X.obj.left.residueField x) :=
  fun x ↦ (by
    simpa using hEll.map ((X.obj.left ↘ Spec (.of k)).residueFieldAlgebraMap x) :
      IsUnit (ell : X.obj.left.residueField x)).invertible

/-- A smooth arrow of SepFinType k with a compactification, as a smooth datum of the
purity family. Finite type and separatedness of the arrow follow from those of the source
over k and separatedness of the target. Source: def-sf-setting, finite-type setting
(blueprint: def-sf-smooth-kunneth-compatibility-data). -/
def smoothDatum {X Y : SepFinType k} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] (c : Compactification f.hom.left) :
    GeneralPurityTransport.SmoothDatum k :=
  haveI h : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  haveI : IsSeparated (f.hom.left ≫ Y.obj.hom) := by rw [h]; infer_instance
  haveI : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by rw [h]; infer_instance
  haveI : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by rw [h]; infer_instance
  haveI : IsSeparated f.hom.left := IsSeparated.of_comp f.hom.left Y.obj.hom
  haveI : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  haveI : QuasiCompact f.hom.left := QuasiCompact.of_comp f.hom.left Y.obj.hom
  { X := X.obj
    Y := Y.obj
    map := f.hom.left
    dim := d
    compactification := c }

/-- The orientation gamma_f : Lf^*(-)(d)[2d] ≅ Rf^! on Dctf: the comparison of the two
right adjoints of the same compact-support functor, namely the source functor of the
explicit purity adjunction of the family a and the constructible exceptional adjoint of J.
It is the unique natural isomorphism compatible with the two counits.
Source: clause (5), orientation (blueprint: def-sf-smooth-kunneth-compatibility-data). -/
def orientation (a : GeneralPurityTransport.AdjunctionFamily ell k)
    (c : PurityTransport.Coefficient ell) {X Y : SepFinType k} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] (cf : Compactification f.hom.left)
    (J : SixOperationsLocalizingAdjunction (c.obj ell) cf) :
    PurityTransport.source ell c (smoothDatum f d cf).map (smoothDatum f d cf).dim
        (a c (smoothDatum f d cf)).source_closed ≅
      ProductComparisons.exceptional (c.bundled ell) J :=
  Adjunction.rightAdjointUniq (a c (smoothDatum f d cf)).adjunction
    (ProductComparisons.adjunction (c.bundled ell) J)

/-- The root-normalized pullback of the shifted Tate line,
Lr^*(Lambda_Y(d)[2d]) ≅ Lambda_X(d)[2d]. The coordinates are the normalized ones of
linePullCoordinates_nonempty; each field is fixed by its normalization equation.
Source: Tate-line pullback (blueprint: def-sf-smooth-kunneth-compatibility-data). -/
def linePull (c : PurityTransport.Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    (CompactificationReindexing.P (c.obj ell) f).obj (c.derivedLine ell Y d) ≅
      c.derivedLine ell X d :=
  PurityTransport.derivedPull ell c f d
    ((Classical.choice (PurityTransport.linePullCoordinates_nonempty ell c f)).power d)

/-- The canonical isomorphism
Lf_1^*L_1(d_1)[2d_1] ⊠ Lf_2^*L_2(d_2)[2d_2] ≅ L(f_1×f_2)^*(L_1 ⊠ L_2)(d_1+d_2)[2d_1+2d_2]
on the product W = X_1 ×_k X_2: the pullback tensorators along r_1, r_2, the middle
interchange, the pullback compositors of the two paths W → T → Y_i, the tensorator along
f_1×f_2 = q ≫ v, and the root-normalized line pullbacks followed by the line product.
Source: clause (5), the canonical pullback--tensor isomorphism
(blueprint: def-sf-smooth-kunneth-compatibility-data). -/
def canonical (hEll : IsUnit (ell : k)) (c : PurityTransport.Coefficient ell)
    (G : ProductComparisons.Geometry k) (d₁ d₂ : ℕ)
    (L₁ : c.derived ell G.Y₁.obj.left) (L₂ : c.derived ell G.Y₂.obj.left) :
    (CompactificationReindexing.P (c.obj ell) G.r₁.hom.left).obj
        ((c.smoothSource ell G.f₁.hom.left d₁).obj L₁) ⊗
      (CompactificationReindexing.P (c.obj ell) G.r₂.hom.left).obj
        ((c.smoothSource ell G.f₂.hom.left d₂).obj L₂) ≅
    (c.smoothSource ell (G.q ≫ G.v).hom.left (d₁ + d₂)).obj
      (RelativeKunneth.exterior (c.bundled ell) G.target L₁ L₂) :=
  let Λ := c.bundled ell
  let P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ CompactificationReindexing.P Λ.X f
  let F := G.q ≫ G.v
  letI := residueInvertible ell hEll G.W
  letI := residueInvertible ell hEll G.X₁
  letI := residueInvertible ell hEll G.X₂
  let B₁ := (P G.f₁.hom.left).obj L₁
  let B₂ := (P G.f₂.hom.left).obj L₂
  let T₁ := c.derivedLine ell G.X₁.obj.left d₁
  let T₂ := c.derivedLine ell G.X₂.obj.left d₂
  let pure :=
    (RelativeKunneth.pullPath Λ G.r₁.hom.left G.f₁.hom.left
      ((G.q ≫ G.v ≫ G.t₁).hom.left)
      (by
        rw [← G.path₁, Category.assoc, G.exchange₁.w, ← Category.assoc]
        rw [G.relativeProduct.w]
        rfl) L₁ ⊗ᵢ
      RelativeKunneth.pullPath Λ G.r₂.hom.left G.f₂.hom.left
        ((G.q ≫ G.v ≫ G.t₂).hom.left)
        (by rw [← G.path₂, Category.assoc, G.exchange₂.w]; rfl) L₂) ≪≫
      ((leftDerivedUpperStarComp Λ.X F.hom.left G.t₁.hom.left).app L₁ ⊗ᵢ
        (leftDerivedUpperStarComp Λ.X F.hom.left G.t₂.hom.left).app L₂) ≪≫
      (RelativeKunneth.pullTensor Λ F.hom.left _ _).symm
  let lines := (linePull ell c G.r₁.hom.left d₁ ⊗ᵢ linePull ell c G.r₂.hom.left d₂) ≪≫
    PurityTransport.derivedProduct ell c G.W.obj.left d₁ d₂
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology G.W.obj.left) Ab.{u + 1}) (condensedRingObj Λ.X G.W.obj.left))
  (RelativeKunneth.pullTensor Λ G.r₁.hom.left B₁ T₁ ⊗ᵢ
    RelativeKunneth.pullTensor Λ G.r₂.hom.left B₂ T₂) ≪≫
    Functor.Monoidal.μIso (tensor _)
      ((P G.r₁.hom.left).obj B₁, (P G.r₁.hom.left).obj T₁)
      ((P G.r₂.hom.left).obj B₂, (P G.r₂.hom.left).obj T₂) ≪≫ (pure ⊗ᵢ lines)

set_option maxHeartbeats 1600000 in
-- The product geometry carries a large dependent tuple of instances.
set_option synthInstance.maxHeartbeats 160000 in
end AlgebraicGeometry.ProEtale.CondensedRing.SixOperationsSmoothKunneth
