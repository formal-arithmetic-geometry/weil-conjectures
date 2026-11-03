/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
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

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
