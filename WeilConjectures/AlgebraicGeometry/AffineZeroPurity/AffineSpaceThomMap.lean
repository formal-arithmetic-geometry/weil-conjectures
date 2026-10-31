/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Coordinate Thom map for the affine zero section

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 1, 3 and 5 (blueprint: def-pur-affine-space-thom-map).

## Main definitions

- `supportedClass`: the actual ordered supported coordinate-boundary product.
- `thom`: its image under the canonical closed exceptional Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

/-- Reuse the recorded compactification of the standard affine projection.
Source: proof Step 1 (blueprint: def-pur-affine-space-thom-map). -/
instance projection_compactification (B : Scheme.{u}) (c : ℕ) :
    HasCompactification (iteratedAffineLineProj B c) :=
  (AffineSpacePurity.projection_geometry B c).2

/-- The ordered tensor power of shifted finite Tate lines with its coefficient unit.
Source: the product display (blueprint: def-pur-affine-space-thom-map). -/
abbrev target (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (c : ℕ) : D P n X :=
  (AffineSpacePurity.action
    ((@curriedTensor (D P n X) _ (cupMonoidal (setting P n) X)).flip.obj
      (AffineSpacePurity.shiftedLine (setting P n) X)) c).obj (unit P n X)

/-- The literal successive scheme-theoretic intersections of coordinate supports.
Source: the supported cup prescription (blueprint: def-pur-affine-space-thom-map). -/
def supportData (B : Scheme.{u}) (c : ℕ) :
    List (Fin c) → Σ S : Scheme.{u}, S ⟶ iteratedAffineLine B c
  | [] => ⟨_, 𝟙 _⟩
  | i :: is => ⟨pullback (supportData B c is).2 (inclusion B c i),
      cupIntersection (supportData B c is).2 (inclusion B c i)⟩

/-- The actual intersection scheme. Source: supported cup prescription
(blueprint: def-pur-affine-space-thom-map). -/
abbrev support (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) := (supportData B c is).1

/-- The actual intersection immersion. Source: supported cup prescription
(blueprint: def-pur-affine-space-thom-map). -/
abbrev supportMap (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) := (supportData B c is).2

/-- Every partial coordinate intersection is closed. Source: proof Step 5
(blueprint: def-pur-affine-space-thom-map).
Proof: the empty intersection is the identity. Each successor is a pullback
of a closed coordinate immersion followed by a closed immersion. -/
theorem support_closed (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) :
    IsClosedImmersion (supportMap B c is) := by
  induction is with
  | nil => exact inferInstanceAs (IsClosedImmersion (𝟙 (iteratedAffineLine B c)))
  | cons i is ih =>
    let := ih
    change IsClosedImmersion (pullback.fst (supportMap B c is) (inclusion B c i) ≫
      supportMap B c is)
    infer_instance
attribute [instance] support_closed

attribute [local irreducible] comparisonUpperStar lowerStar

/-- Exact functors commute with degree-zero complexes, preserving their origin.
Source: exact comparison (blueprint: def-pur-affine-space-thom-map). -/
private theorem exact_single_origin {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) : (DerivedCategory.TStructure.t.plus.map F.mapDerivedCategory)
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M)) := by
  exact (DerivedCategory.TStructure.t.plus.map F.mapDerivedCategory).prop_of_iso
    ((F.mapDerivedCategorySingleFunctor 0).app M)
    (ObjectProperty.prop_map_obj _ _ (show DerivedCategory.TStructure.t.plus
      ((DerivedCategory.singleFunctor C 0).obj M) from ⟨0, inferInstance⟩))

/-- Degree-zero comparison sheaves have bounded-below etale origin.
Source: comparison in Step 1 (blueprint: def-pur-affine-space-thom-map). -/
private theorem single_origin (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology A) :
    DerivedCategory.plusEtaleOrigin A X
      ((DerivedCategory.singleFunctor _ 0).obj ((comparisonUpperStar A X).obj M)) := by
  exact exact_single_origin (comparisonUpperStar A X) M

/-- Exact comparison preserves the lower bound -2 of a shifted degree-zero sheaf.
Source: Steps 1 and 3 (blueprint: def-pur-affine-space-thom-map). -/
private theorem compared_line_plus (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (X : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus
      ((comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) := by
  have : ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧).IsGE (-2) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)
  exact ⟨-2, (comparisonUpperStar (ModuleCat.{u + 1} A) X).isGE_mapDerivedCategory_obj
    ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) (-2)⟩

/-- Tensor by a shifted flat sheaf preserves boundedness below.
Source: finite Tate tensor in Step 5 (blueprint: def-pur-affine-space-thom-map). -/
private theorem flat_shift_tensor_plus
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [IsGrothendieckAbelian C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (L : C) (hf : ObjectProperty.flat L) (m : ℤ)
    (K : DerivedCategory C) (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ ((DerivedCategory.singleFunctor C 0).obj L)⟦m⟧) := by
  obtain ⟨a, ha⟩ := hK
  have : K.IsGE a := ha
  let S := (DerivedCategory.singleFunctor C 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  have : (K ⊗ S).IsGE (a + 0) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeGE_right (fun F ↦ (ht F).1) K a
  have hs : DerivedCategory.TStructure.t.plus ((K ⊗ S)⟦m⟧) :=
    ⟨a + 0 - m,
      DerivedCategory.TStructure.t.isGE_shift _ (a + 0) m (a + 0 - m) (by omega)⟩
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (((tensorLeft K).commShiftIso m).app S).symm hs

/-- Exact functors carry shifts of single objects to their canonical shifts.
Source: comparison and tensor bounds (blueprint: def-pur-affine-space-thom-map). -/
private theorem exact_flat_shift_tensor_plus {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) (hf : ObjectProperty.flat (F.obj M)) (m : ℤ)
    (K : DerivedCategory D) (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦m⟧)) := by
  let e := (F.mapDerivedCategory.commShiftIso m).app
      ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
    (shiftFunctor _ m).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)
  exact DerivedCategory.TStructure.t.plus.prop_of_iso (whiskerLeftIso K e).symm
    (flat_shift_tensor_plus _ hf m K hK)

/-- The compared shifted Tate line preserves a finite lower bound under tensor.
Source: finite Tate tensor in Step 5 (blueprint: def-pur-affine-space-thom-map). -/
private theorem compared_line_tensor_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (N : Γ(X, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  have hInv : ∀ x : X, IsUnit (N : X.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat (Scheme.finiteEtaleTateLine X N A hA) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line X N hN hInv A hA 1).2.2.1
  exact exact_flat_shift_tensor_plus (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (Scheme.finiteEtaleTateLine X N A hA) (flat_comparisonUpperStar_obj hf) 2 K hK

/-- Boundedness of every finite tensor power of the shifted locally free Tate line.
Source: proof Steps 1 and 5 (blueprint: def-pur-affine-space-thom-map).
Proof: the ordinary root line is etale locally a free module of rank one because
ell is invertible. It is flat, as are its tensor powers. Thus the tensor power
is a sheaf shifted by 2c and is bounded below; exact comparison preserves this. -/
theorem target_plus (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    DerivedCategory.TStructure.t.plus (target P n X c) := by
  induction c with
  | zero =>
    change DerivedCategory.TStructure.t.plus ((DerivedCategory.singleFunctor _ 0).obj _)
    exact ⟨0, inferInstance⟩
  | succ c ih =>
    exact compared_line_tensor_plus (setting P n).Coefficient _
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) _ X
      (AffineSpacePurity.exponentUnit (setting P n) X aX) (target P n X c) ih

/-- The one-factor shifted line is bounded below. Source: proof Steps 1--3
(blueprint: def-pur-affine-space-thom-map).
Proof: the ordinary finite Tate line is a sheaf in degree zero. Shift by two
preserves boundedness below, as does the exact site comparison. -/
theorem boundary_plus (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (AffineSpacePurity.shiftedLine (setting P n) X) := by
  unfold AffineSpacePurity.shiftedLine
  exact compared_line_plus (setting P n).Coefficient _ _ X

/-- Apply the recorded supportedCup at degrees zero and cancel the zero-shift
unitors. This uses the published operation itself. Source: proof Step 5
(blueprint: def-pur-affine-space-thom-map). -/
def cupZero (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j))) ⟶ cupTensorObject P X F.obj G.obj :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  supportedCup P i j F G 0 0
      (α ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app F.obj)
      (β ≫ (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app G.obj) ≫
    (shiftFunctorZero (CupDerivedCategory P X) ℤ).hom.app
      (cupTensorObject P X F.obj G.obj)

/-- The degree-zero object supported on a literal partial coordinate intersection.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def classSource (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (is : List (Fin c)) : D P n (iteratedAffineLine B c) :=
  (cupSingle (setting P n) (iteratedAffineLine B c)).obj
    ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (supportMap B c is)).obj
      ((setting P n).constant (support B c is)))

/-- Unfold the named partial-support object once, without choosing an identification.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: this is the defining equation of classSource. -/
theorem classSource_eq (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (is : List (Fin c)) :
    classSource P n B c is =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (supportMap B c is)).obj
          ((setting P n).constant (support B c is))) := by
  unfold classSource
  rfl

/-- The empty support intersection is the whole affine space with its identity map.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold classSource, support, supportMap and the empty equation of supportData. -/
theorem classSource_nil (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (c : ℕ) :
    classSource P n B c [] =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
          (𝟙 (iteratedAffineLine B c))).obj
            ((setting P n).constant (iteratedAffineLine B c))) := by
  unfold classSource
  rfl

/-- The successor support is exactly the scheme-theoretic cup intersection.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold classSource, support and supportMap and reduce the cons equation
of supportData. Both sides are the same sheaf on the same pullback scheme. -/
theorem classSource_cons (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (c : ℕ) (i : Fin c) (is : List (Fin c)) :
    classSource P n B c (i :: is) =
      (cupSingle (setting P n) (iteratedAffineLine B c)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
          (cupIntersection (supportMap B c is) (inclusion B c i))).obj
            ((setting P n).constant (pullback (supportMap B c is) (inclusion B c i)))) := by
  unfold classSource
  rfl

/-- The successor target is the same tensor product used by supportedCup.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map).
Proof: unfold target and the successor equation of AffineSpacePurity.action.
The two tensor symbols refer to the same canonical derived monoidal structure. -/
theorem target_succ (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (d : ℕ) :
    cupTensorObject (setting P n) X (target P n X d)
      (AffineSpacePurity.shiftedLine (setting P n) X) = target P n X (d + 1) := by
  rfl

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def coordinateProductFold {c : ℕ} {C : Type (u + 2)} [Category.{u + 1} C]
    (S : List (Fin c) → C) (T : ℕ → C)
    (empty : S [] ⟶ T 0)
    (step : ∀ i is, (S is ⟶ T is.length) → (S (i :: is) ⟶ T (i :: is).length)) :
    ∀ is, S is ⟶ T is.length :=
  List.rec empty step

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def coordinateProductTransport {C : Type (u + 2)} [Category.{u + 1} C] {W X Y Z : C}
    (a : W = X) (f : X ⟶ Y) (b : Y = Z) : W ⟶ Z :=
  eqToHom a ≫ f ≫ eqToHom b

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def coordinateProductStart {C : Type (u + 2)} [Category.{u + 1} C] {W X Y : C}
    (a : W = X) (f : X ⟶ Y) : W ⟶ Y := eqToHom a ≫ f

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def coordinateSupportedCompose {C : Type (u + 2)} [Category.{u + 1} C] {W X Y Z U : C}
    (f : W ⟶ X) (e : X = Y) (g : Y ⟶ Z) (h : Z = U) : W ⟶ U :=
  f ≫ eqToHom e ≫ g ≫ eqToHom h

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def closedSingleComparison {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.rightDerivedFunctor)
    (M : C) : G.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  e.app ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
    F.rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app M

/-- Cached generic construction used by the specified coordinate Thom map.
Source: supported coordinate product and exceptional adjunct
(blueprint: def-pur-affine-space-thom-map). -/
def coordinateThomAdjunct (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i] [CompactSpace X]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z K)
    (hL : DerivedCategory.TStructure.t.plus L)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (e : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj
      K ≅ N) (a : N ⟶ L) :
    K ⟶ (rightDerivedUpperShriek A i).obj L :=
  rightDerivedUpperShriekHomEquiv (K := K)
    (L := L) i hM hL (e.hom ≫ a)

/-- The ordered product of the actual coordinate Cartier boundaries. The empty
product is the constant-unit identity; each successor is the recorded supported cup.
The equality transports only unfold its literal support and tensor endpoints.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def product (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) : (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  coordinateProductFold (classSource P n B c) (target P n (iteratedAffineLine B c))
    (coordinateProductStart (classSource_nil P n B c)
      ((cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c)))))
    (fun i is previous ↦ coordinateProductTransport (classSource_cons P n B c i is)
      (cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (coordinateProductStart (classSource_eq P n B c is).symm previous)
        (boundary P n B aB c i))
      (target_succ P n (iteratedAffineLine B c) is.length))

/-- Evaluate a composite pullback on a global section.
Source: scheme pullback functoriality (blueprint: def-pur-affine-space-thom-map). -/
private theorem comp_appTop_apply {T Y X : Scheme.{u}} (f : T ⟶ Y) (g : Y ⟶ X)
    (t : Γ(X, ⊤)) : (f ≫ g).appTop t = f.appTop (g.appTop t) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Projection and coordinate sections determine a map into an affine tower.
Source: affine-space universal property (blueprint: def-pur-affine-space-thom-map). -/
private theorem tower_hom_ext {B T : Scheme.{u}} (c : ℕ)
    (f g : T ⟶ iteratedAffineLine B c)
    (hp : f ≫ iteratedAffineLineProj B c = g ≫ iteratedAffineLineProj B c)
    (ht : ∀ i, f.appTop (iteratedAffineLine.coord B c i) =
      g.appTop (iteratedAffineLine.coord B c i)) : f = g := by
  induction c with
  | zero =>
    exact (Category.comp_id f).symm.trans (hp.trans (Category.comp_id g))
  | succ c ih =>
    apply AffineSpace.hom_ext (n := PUnit.{u + 1})
    · apply ih
      · have h := hp
        rw [iteratedAffineLineProj_succ] at h
        exact (Category.assoc f _ _).trans (h.trans (Category.assoc g _ _).symm)
      · intro i
        have h := ht i.succ
        rw [iteratedAffineLine.coord_succ_succ] at h
        let p : iteratedAffineLine B (c + 1) ⟶ iteratedAffineLine B c :=
          𝔸(PUnit.{u + 1}; iteratedAffineLine B c) ↘ iteratedAffineLine B c
        exact (comp_appTop_apply f p _).trans
          (h.trans (comp_appTop_apply g p _).symm)
    · intro i
      cases i
      have h := ht 0
      rw [iteratedAffineLine.coord_succ_zero] at h
      exact h

/-- Pulling back a vanishing global section preserves its vanishing.
Source: coordinate support calculation (blueprint: def-pur-affine-space-thom-map). -/
private theorem comp_appTop_zero {T Y X : Scheme.{u}} (f : T ⟶ Y) (g : Y ⟶ X)
    (t : Γ(X, ⊤)) (ht : g.appTop t = 0) : (f ≫ g).appTop t = 0 := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ht, map_zero]

/-- A coordinate occurring in the support list vanishes on its intersection.
Source: successive coordinate quotients (blueprint: def-pur-affine-space-thom-map). -/
private theorem support_coord_zero (B : Scheme.{u}) (c : ℕ) (is : List (Fin c))
    (i : Fin c) (hi : i ∈ is) :
    (supportMap B c is).appTop (iteratedAffineLine.coord B c i) = 0 := by
  induction is with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j is ih =>
    rcases List.mem_cons.mp hi with h | h
    · subst i
      change (pullback.fst (supportMap B c is) (inclusion B c j) ≫
        supportMap B c is).appTop _ = 0
      rw [pullback.condition]
      exact comp_appTop_zero _ _ _
        (Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _))
    · exact comp_appTop_zero (pullback.fst (supportMap B c is) (inclusion B c j))
        (supportMap B c is) _ (ih h)

/-- The zero section lifts to every successive coordinate intersection.
Source: successive coordinate quotients (blueprint: def-pur-affine-space-thom-map). -/
private theorem zero_lifts_support (B : Scheme.{u}) (c : ℕ) (is : List (Fin c)) :
    ∃ f : B ⟶ support B c is, f ≫ supportMap B c is = zero B c := by
  induction is with
  | nil => exact ⟨zero B c, Category.comp_id _⟩
  | cons i is ih =>
    obtain ⟨f, hf⟩ := ih
    let g : B ⟶ divisor B c i := (zero B c).liftZeroLocusSubscheme (by
      intro t ht
      rcases Set.mem_singleton_iff.mp ht with rfl
      exact Scheme.Hom.toIteratedAffineLine_appTop_coord (𝟙 B) (fun _ ↦ 0) i)
    have hg : g ≫ inclusion B c i = zero B c :=
      Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
    refine ⟨pullback.lift f g (hf.trans hg.symm), ?_⟩
    change pullback.lift f g _ ≫
      (pullback.fst (supportMap B c is) (inclusion B c i) ≫ supportMap B c is) = _
    rw [← Category.assoc, pullback.lift_fst, hf]

/-- All the coordinate equations cut out exactly the zero section, canonically over X.
Source: proof Steps 1 and 5 (blueprint: def-pur-affine-space-thom-map).
Proof: on every affine chart the successive pullback quotient is the polynomial
ring modulo all coordinates, hence the base ring. The quotient identifications
fix constants and kill every generator, so glue over the base. They identify the
closed immersion with zero. Any two such isomorphisms agree after composing
with the monomorphism zero, which proves uniqueness. This includes c=0. -/
theorem supportIso_existsUnique (B : Scheme.{u}) (c : ℕ) :
    ∃! e : support B c (List.finRange c) ≅ B,
      e.hom ≫ zero B c = supportMap B c (List.finRange c) := by
  obtain ⟨f, hf⟩ := zero_lifts_support B c (List.finRange c)
  have he : (supportMap B c (List.finRange c) ≫ iteratedAffineLineProj B c) ≫
      zero B c = supportMap B c (List.finRange c) := by
    apply tower_hom_ext
    · simp only [Category.assoc, zero, Scheme.Hom.toIteratedAffineLine_proj,
        Category.comp_id]
    · intro i
      exact (comp_appTop_zero _ (zero B c) _
        (Scheme.Hom.toIteratedAffineLine_appTop_coord (𝟙 B) (fun _ ↦ 0) i)).trans
        (support_coord_zero B c (List.finRange c) i (List.mem_finRange i)).symm
  let e : support B c (List.finRange c) ≅ B :=
    { hom := supportMap B c (List.finRange c) ≫ iteratedAffineLineProj B c
      inv := f
      hom_inv_id := by
        apply (cancel_mono (supportMap B c (List.finRange c))).mp
        simp only [Category.assoc, hf, Category.id_comp]
        simpa only [Category.assoc] using he
      inv_hom_id := by
        rw [← Category.assoc, hf]
        exact Scheme.Hom.toIteratedAffineLine_proj (𝟙 B) (fun _ ↦ 0) }
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact (cancel_mono (zero B c)).mp (he'.trans he.symm)

/-- The unique support identification over the affine space, not an arbitrary iso.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
def supportIso (B : Scheme.{u}) (c : ℕ) : support B c (List.finRange c) ≅ B :=
  (supportIso_existsUnique B c).exists.choose

/-- The supported product on the zero section itself, transported by its unique
scheme-theoretic support identification. Coordinates have even degree, so this
right-associated enumeration agrees with the specified ordered product.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
def supportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  coordinateSupportedCompose ((cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec))
    (classSource_eq P n B c (List.finRange c)).symm
    (product P n B aB c (List.finRange c))
    (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))

/-- The coefficient unit is bounded below of etale origin.
Source: proof Step 1 (blueprint: def-pur-affine-space-thom-map).
Proof: it is comparison inverse image of the constant sheaf in degree zero.
The exact comparison preserves the lower bound zero. -/
theorem unit_origin (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (setting P n).Coefficient) X
      (unit P n X) := by
  exact single_origin (ModuleCat.{u + 1} (setting P n).Coefficient) X
    ((setting P n).constantEtale X)

/-- Closed direct image is exact for this Noetherian coordinate immersion.
Source: proof Step 3 (blueprint: def-pur-affine-space-thom-map).
Proof: finite type over k makes X Noetherian, so the complementary open is
quasi-compact. The open-closed exactness theorem applies to this complementary
pair and gives preservation of finite colimits. -/
theorem zero_exact (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)) := by
  let := AffineSpacePurity.tower_noetherian (setting P n) B aB c
  exact preservesFiniteColimits_lowerStar_of_isCompl (zero B c)
    (zero B c).openComplement.ι
    (eq_compl_iff_isCompl.mp (zero B c).range_eq_compl_range_openComplement_ι)

/-- Proper compact support followed by exact closed direct image in degree zero.
Every arrow is the canonical derived or compactification comparison.
Source: proof Steps 3 and 5 (blueprint: def-pur-affine-space-thom-map). -/
def closedSingleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj M) :=
  closedSingleComparison (lowerStar (ModuleCat.{u + 1} A) i) _
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) i) M

/-- The Thom morphism is the exceptional adjunct of the actual supported cup product.
No purity isomorphism is selected in defining its data.
Source: proof Step 5 (blueprint: def-pur-affine-space-thom-map). -/
@[irreducible]
def thom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient
        (zero B c)).obj (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  coordinateThomAdjunct (setting P n).Coefficient (zero B c)
      (unit P n B) (target P n (iteratedAffineLine B c) c)
      (unit_origin P n B)
      (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c) _
      (closedSingleIso (setting P n).Coefficient (zero B c) ((setting P n).constant B))
      (supportedClass P n B aB c)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
