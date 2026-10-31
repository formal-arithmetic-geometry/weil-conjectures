/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedRelativeKunneth
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom

/-!
# Canonical product comparisons on ordinary condensed coefficient categories

Source: `literature/blueprint/latest/blueprint/sec-six-functors/
sk-def-sf-kv-maps/def-sf-kv-maps.md`, clauses (i)--(iv) (blueprint: def-sf-kv-maps).
The older main-20261015 sketch,
order 2511, has the same four words. The current source uses ordinary condensed
coefficients and constructible exceptional adjoints, rather than completed operations.

All functors below are the existing native module-object functors. The relative
Kunneth interface fixes its isomorphism by the explicit inverse word. The exceptional
arrows are adjunction transposes; no exceptional comparison is assumed invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons

open CompactificationReindexing RelativeKunneth

variable {k : Type u} [Field k] (Λ : ScalarSixRing.{u})

/-- The base scheme with its identity structure map.
Source: products over k in clause (i) (blueprint: def-sf-kv-maps). -/
abbrev base (k : Type u) [Field k] : SepFinType k :=
  ⟨Over.mk (𝟙 (Spec (.of k))),
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k)))),
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k)))),
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))⟩

/-- The four product schemes and the two exchange squares in clause (i).
All schemes, including the targets, are separated of finite type. The Cartesian
squares specify the products by their universal properties, without choosing coordinates.
Source: clause (i) (blueprint: def-sf-kv-maps). -/
structure Geometry (k : Type u) [Field k] where
  X₁ : SepFinType k
  X₂ : SepFinType k
  Y₁ : SepFinType k
  Y₂ : SepFinType k
  T : SepFinType k
  U : SepFinType k
  V : SepFinType k
  W : SepFinType k
  f₁ : X₁ ⟶ Y₁
  f₂ : X₂ ⟶ Y₂
  t₁ : T ⟶ Y₁
  t₂ : T ⟶ Y₂
  a₁ : U ⟶ X₁
  a₂ : V ⟶ X₂
  u : U ⟶ T
  v : V ⟶ T
  p : W ⟶ U
  q : W ⟶ V
  r₁ : W ⟶ X₁
  r₂ : W ⟶ X₂
  sourceProduct : IsPullback r₁.hom.left r₂.hom.left X₁.obj.hom X₂.obj.hom
  targetProduct : IsPullback t₁.hom.left t₂.hom.left Y₁.obj.hom Y₂.obj.hom
  exchange₁ : IsPullback a₁.hom.left u.hom.left f₁.hom.left t₁.hom.left
  exchange₂ : IsPullback a₂.hom.left v.hom.left f₂.hom.left t₂.hom.left
  relativeProduct : IsPullback p.hom.left q.hom.left u.hom.left v.hom.left
  path₁ : p.hom.left ≫ a₁.hom.left = r₁.hom.left
  path₂ : q.hom.left ≫ a₂.hom.left = r₂.hom.left

/-- The source absolute product square. Source: (i) (blueprint: def-sf-kv-maps). -/
def Geometry.source (G : Geometry k) : Diagram k :=
  ⟨base k, G.X₁, G.X₂, G.W,
    ObjectProperty.homMk (Over.homMk G.X₁.obj.hom),
    ObjectProperty.homMk (Over.homMk G.X₂.obj.hom), G.r₁, G.r₂, G.sourceProduct⟩

/-- The target absolute product square. Source: (i) (blueprint: def-sf-kv-maps). -/
def Geometry.target (G : Geometry k) : Diagram k :=
  ⟨base k, G.Y₁, G.Y₂, G.T,
    ObjectProperty.homMk (Over.homMk G.Y₁.obj.hom),
    ObjectProperty.homMk (Over.homMk G.Y₂.obj.hom), G.t₁, G.t₂, G.targetProduct⟩

/-- The relative product over T = Y1 times Y2.
Source: (i) (blueprint: def-sf-kv-maps). -/
def Geometry.relative (G : Geometry k) : Diagram k :=
  ⟨G.T, G.U, G.V, G.W, G.u, G.v, G.p, G.q, G.relativeProduct⟩

/-- Compactifications for the actual per-morphism support functors.
Source: (i), compact-support construction (blueprint: def-sf-kv-maps). -/
structure Models (G : Geometry k) where
  f₁ : Compactification G.f₁.hom.left
  f₂ : Compactification G.f₂.hom.left
  relative : RelativeKunneth.Models G.relative

/-- The canonical relative map and the two inverse compact-support exchanges.
The initial transport is the tensor of the inverse pullback-composition isomorphisms.
Source: (i) (blueprint: def-sf-kv-maps). -/
def ku (H : CompactSupportComposition.CoherentData Λ.X k) (A : IsoFamily Λ H)
    (G : Geometry k) (c : Models G)
    (B₁ : ConstantModelConstructibleFiniteTor Λ.X G.X₁.obj.left)
    (B₂ : ConstantModelConstructibleFiniteTor Λ.X G.X₂.obj.left) :
    (F Λ.X c.relative.total).obj (exterior Λ G.source B₁.obj B₂.obj) ≅
      exterior Λ G.target ((F Λ.X c.f₁).obj B₁.obj) ((F Λ.X c.f₂).obj B₂.obj) :=
  (F Λ.X c.relative.total).mapIso
      ((pullPath Λ G.p.hom.left G.a₁.hom.left G.r₁.hom.left G.path₁ B₁.obj).symm ⊗ᵢ
        (pullPath Λ G.q.hom.left G.a₂.hom.left G.r₂.hom.left G.path₂ B₂.obj).symm) ≪≫
    A.iso G.relative c.relative
      (pullObject Λ H G.U G.X₁ G.a₁.hom.left B₁)
      (pullObject Λ H G.V G.X₂ G.a₂.hom.left B₂) ≪≫
    (((H.exchange (X := G.X₁) (Y := G.Y₁) (X' := G.U) (Y' := G.T)
      (f := G.f₁) (f' := G.u) G.exchange₁ c.f₁ c.relative.f).app
        (localizingObject Λ _ B₁)).symm ⊗ᵢ
      ((H.exchange (X := G.X₂) (Y := G.Y₂) (X' := G.V) (Y' := G.T)
        (f := G.f₂) (f' := G.v) G.exchange₂ c.f₂ c.relative.g).app
          (localizingObject Λ _ B₂)).symm)

/-- Restrict the specified support functor using the fixed localizing adjunction.
Source: det-def-sf-operations (vi) (blueprint: def-sf-kv-maps). -/
def lower {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c) :
    ConstantModelConstructibleFiniteTor Λ.X X ⥤ ConstantModelConstructibleFiniteTor Λ.X Y :=
  (constantModelBoundedConstructible Λ.X Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible Λ.X X ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ F Λ.X c)
    (fun K ↦ S.lower_ctf ⟨K.obj, S.source_mem K.obj K.property⟩ K.property)

/-- The specified constructible exceptional adjoint, with the same morphism and model.
Source: det-def-sf-operations (vi) (blueprint: def-sf-kv-maps). -/
def exceptional {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c) :
    ConstantModelConstructibleFiniteTor Λ.X Y ⥤ ConstantModelConstructibleFiniteTor Λ.X X :=
  (constantModelBoundedConstructible Λ.X X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).lift
    (ObjectProperty.ιOfLE S.target_mem ⋙ S.right ⋙ (localizingClosureProEtale Λ.X X).ι)
    (fun K ↦ S.right_ctf ⟨K.obj, S.target_mem K.obj K.property⟩ K.property)

/-- The restricted Hom bijections, retaining the fixed units and counits.
Source: det-def-sf-operations (vi) (blueprint: def-sf-kv-maps). -/
def adjunction {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : SixOperationsLocalizingAdjunction Λ.X c) : lower Λ S ⊣ exceptional Λ S :=
  S.adjunction.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE S.source_mem)
    (ObjectProperty.fullyFaithfulιOfLE S.target_mem)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)) (NatIso.ofComponents (fun _ ↦ Iso.refl _))


/-- The exceptional comparison is exactly homEquiv applied to Ku followed by
both counits. It is a morphism; its invertibility is not used.
Source: (ii) (blueprint: def-sf-kv-maps). -/
def alpha (H : CompactSupportComposition.CoherentData Λ.X k) (A : IsoFamily Λ H)
    (G : Geometry k) (c : Models G)
    (S₁ : SixOperationsLocalizingAdjunction Λ.X c.f₁)
    (S₂ : SixOperationsLocalizingAdjunction Λ.X c.f₂)
    (S : SixOperationsLocalizingAdjunction Λ.X c.relative.total)
    (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
    (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) :
    (IsoFamily.exteriorObject Λ A G.source ((exceptional Λ S₁).obj L₁)
      ((exceptional Λ S₂).obj L₂)) ⟶
    (exceptional Λ S).obj (IsoFamily.exteriorObject Λ A G.target L₁ L₂) :=
  (adjunction Λ S).homEquiv _ _
    ⟨(ku Λ H A G c ((exceptional Λ S₁).obj L₁) ((exceptional Λ S₂).obj L₂)).hom ≫
      ((P Λ.X G.t₁.hom.left).map ((adjunction Λ S₁).counit.app L₁).hom ⊗ₘ
        (P Λ.X G.t₂.hom.left).map ((adjunction Λ S₂).counit.app L₂).hom)⟩

/-- The external Hom map is the signed evaluation transpose in the native closed
monoidal derived category. Source: (iii) (blueprint: def-sf-kv-maps). -/
def beta {T X Y : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ Y)
    (E₁ L₁ : D Λ.X X) (E₂ L₂ : D Λ.X Y) :
    (P Λ.X p).obj ((ihom E₁).obj L₁) ⊗ (P Λ.X q).obj ((ihom E₂).obj L₂) ⟶
      (ihom ((P Λ.X p).obj E₁ ⊗ (P Λ.X q).obj E₂)).obj
        ((P Λ.X p).obj L₁ ⊗ (P Λ.X q).obj L₂) :=
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
  MonoidalClosed.externalIhomMap (P Λ.X p) (P Λ.X q) E₁ L₁ E₂ L₂

/-- Normalize X times Spec k to X, while retaining the same source product W.
This is the geometry used for alpha at (id_X,a_Y).
Source: (iv) (blueprint: def-sf-kv-maps). -/
def verdierGeometry (X Y W : SepFinType k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom) : Geometry k where
  X₁ := X
  X₂ := Y
  Y₁ := X
  Y₂ := base k
  T := X
  U := X
  V := W
  W := W
  f₁ := 𝟙 X
  f₂ := ObjectProperty.homMk (Over.homMk Y.obj.hom)
  t₁ := 𝟙 X
  t₂ := ObjectProperty.homMk (Over.homMk X.obj.hom)
  a₁ := 𝟙 X
  a₂ := pY
  u := 𝟙 X
  v := pX
  p := pX
  q := 𝟙 W
  r₁ := pX
  r₂ := pY
  sourceProduct := sq
  targetProduct := by
    change IsPullback (𝟙 _) X.obj.hom X.obj.hom (𝟙 _)
    exact IsPullback.of_id_fst
  exchange₁ := IsPullback.of_id_fst
  exchange₂ := sq.flip
  relativeProduct := IsPullback.of_id_snd
  path₁ := Category.comp_id _
  path₂ := Category.id_comp _

/-- The unit for the exceptional identity functor is the transpose of the canonical
support-identity isomorphism, including compactification independence.
Source: unit identifications in (iv) (blueprint: def-sf-kv-maps). -/
def identityExceptional (H : CompactSupportComposition.CoherentData Λ.X k)
    (X : SepFinType k) (c : Compactification (𝟙 X.obj.left))
    (S : SixOperationsLocalizingAdjunction Λ.X c)
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    M ⟶ (exceptional Λ S).obj M :=
  (adjunction Λ S).homEquiv M M
    ⟨((H.comparison (𝟙 X) c (Compactification.ofIsProper (𝟙 X.obj.left))).hom.app
      (localizingObject Λ _ M)) ≫ (CompactSupportComposition.identity Λ.X X.obj.left).hom.app M.obj⟩

/-- The exceptional comparison alpha_(id_X,a_Y), with the two unit identifications.
The coefficient unit is a bundled constructible object with its specified identification;
its object is not chosen from existence. No inverse of alpha is used.
Source: (iv), referring to (ii) (blueprint: def-sf-kv-maps). -/
def alphaUnit (H : CompactSupportComposition.CoherentData Λ.X k) (A : IsoFamily Λ H)
    (X Y W : SepFinType k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (c : Models (verdierGeometry X Y W pX pY sq))
    (S₁ : SixOperationsLocalizingAdjunction Λ.X c.f₁)
    (S₂ : SixOperationsLocalizingAdjunction Λ.X c.f₂)
    (S : SixOperationsLocalizingAdjunction Λ.X c.relative.total)
    (U : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of k)))
    (eU : U.obj ≅ 𝟙_ (D Λ.X (Spec (.of k))))
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) :
    (P Λ.X pX.hom.left).obj M.obj ⊗
        (P Λ.X pY.hom.left).obj ((exceptional Λ S₂).obj U).obj ⟶
      ((exceptional Λ S).obj M).obj :=
  let G := verdierGeometry X Y W pX pY sq
  let targetUnit : IsoFamily.exteriorObject Λ A G.target M U ≅ M :=
    ObjectProperty.isoMk _
      (((leftDerivedUpperStarId Λ.X X.obj.left).app M.obj ⊗ᵢ
        ((P Λ.X X.obj.hom).mapIso eU ≪≫ leftDerivedUpperStarUnitIso Λ.X X.obj.hom)) ≪≫
          ρ_ M.obj)
  ((P Λ.X pX.hom.left).map (identityExceptional Λ H X c.f₁ S₁ M).hom ⊗ₘ 𝟙 _) ≫
    (alpha Λ H A G c S₁ S₂ S M U).hom ≫
    ((exceptional Λ S).map targetUnit.hom).hom

/-- The Kunneth--Verdier arrow is beta followed by RHom(1,alphaUnit).
Here omega_Y is literally the exceptional image of the coefficient unit U, and
D_Y N is literally internal Hom into that object. The contravariant Hom transport
uses the unit identification Lambda_X boxtimes N = LpY^* N. The target still contains
LpY^* N. Source: (iv) (blueprint: def-sf-kv-maps). -/
def kappa (H : CompactSupportComposition.CoherentData Λ.X k) (A : IsoFamily Λ H)
    (X Y W : SepFinType k) (pX : W ⟶ X) (pY : W ⟶ Y)
    (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
    (c : Models (verdierGeometry X Y W pX pY sq))
    (S₁ : SixOperationsLocalizingAdjunction Λ.X c.f₁)
    (S₂ : SixOperationsLocalizingAdjunction Λ.X c.f₂)
    (S : SixOperationsLocalizingAdjunction Λ.X c.relative.total)
    (U : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of k)))
    (eU : U.obj ≅ 𝟙_ (D Λ.X (Spec (.of k))))
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (N : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    (P Λ.X pX.hom.left).obj M.obj ⊗
        (P Λ.X pY.hom.left).obj ((ihom N.obj).obj ((exceptional Λ S₂).obj U).obj) ⟶
      (ihom ((P Λ.X pY.hom.left).obj N.obj)).obj ((exceptional Λ S).obj M).obj :=
  let omega := ((exceptional Λ S₂).obj U).obj
  let unitHom := (MonoidalClosed.unitIsoSelf (X := M.obj)).symm
  let unitExternal :=
    (leftDerivedUpperStarUnitIso Λ.X pX.hom.left ⊗ᵢ
      Iso.refl ((P Λ.X pY.hom.left).obj N.obj)) ≪≫ λ_ _
  ((P Λ.X pX.hom.left).map unitHom.hom ⊗ₘ 𝟙 _) ≫
    beta Λ pX.hom.left pY.hom.left (𝟙_ _) M.obj N.obj omega ≫
    (MonoidalClosed.pre unitExternal.inv).app _ ≫
    (ihom ((P Λ.X pY.hom.left).obj N.obj)).map
      (alphaUnit Λ H A X Y W pX pY sq c S₁ S₂ S U eU M)

/-- The recorded relative theorem supplies a family whose inverse is fixed by its
six explicit forward factors. This choice therefore selects canonical isomorphisms,
not witnesses of an unnormalized existence assertion.
Source: (i), sk-thm-sf-kunneth-relative (blueprint: def-sf-kv-maps). -/
def relativeDatum (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell) : ProductTheorem ell D.k :=
  Classical.choice (condensedRelativeKunneth D ell hne)

/-- The four maps for a fixed per-morphism constructible exceptional datum S.
The coefficient quantifier ranges over every admissible condensed ring: finite A,
O_E, E, and the finite-subextension-valued algebraic closure. The relative theorem
provides the normalized support comparisons, and S provides only the per-morphism
right adjoints with their defining adjunctions. The four maps themselves are computed.
Source: all clauses (i)--(iv) (blueprint: def-sf-kv-maps). -/
def maps (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (S : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left),
      SixOperationsLocalizingAdjunction Λ.X c) :=
  let R := relativeDatum D ell hne
  let H := R.coherent Λ hΛ
  let A := R.product Λ hΛ
  (ku Λ H A,
    fun (G : Geometry D.k) (c : Models G)
      (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
      (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) ↦
      alpha Λ H A G c (S G.f₁ c.f₁) (S G.f₂ c.f₂)
        (S (G.q ≫ G.v) c.relative.total) L₁ L₂,
    fun (G : Geometry D.k)
      (E₁ L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
      (E₂ L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left) ↦
      beta Λ G.t₁.hom.left G.t₂.hom.left E₁.obj L₁.obj E₂.obj L₂.obj,
    fun (X Y W : SepFinType D.k) (pX : W ⟶ X) (pY : W ⟶ Y)
      (sq : IsPullback pX.hom.left pY.hom.left X.obj.hom Y.obj.hom)
      (c : Models (verdierGeometry X Y W pX pY sq)) ↦
      let G := verdierGeometry X Y W pX pY sq
      kappa Λ H A X Y W pX pY sq c (S G.f₁ c.f₁) (S G.f₂ c.f₂)
        (S (G.q ≫ G.v) c.relative.total))

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
