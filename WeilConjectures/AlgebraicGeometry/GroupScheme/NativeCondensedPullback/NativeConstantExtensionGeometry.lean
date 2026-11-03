/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Geometry of native finite constant extension

The model is the actual base change by extensionEmbedding. The fibre isomorphism
and its Frobenius identity are proved from the two pullback projections. No legacy
Weil-heart model is imported or used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.NativeCondensedPullback
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- Base change of a model morphism to the fixed algebraic closure.
Source: the geometric-fibre construction
(blueprint: def-zl-native-constant-extension-geometry). -/
def fiberMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Geometric Frobenius commutes with the actual base-changed model morphism.
Source: the geometric-fibre construction
(blueprint: def-zl-native-constant-extension-geometry).
Proof: compare the model and closure projections of the two pullback maps. -/
theorem frobenius_naturality {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFrobenius X₀).hom ≫ fiberMap D f₀ =
      fiberMap D f₀ ≫ (D.geometricFrobenius Y₀).hom := by
  apply pullback.hom_ext
  · simp [fiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]
  · simp [fiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

/-- X_(0,m) as a k_m-scheme, the actual finite constant base change.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionModel : Over (Spec (.of (D.extensionSubfield m hm))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀

/-- The same scheme regarded over k_0, before finite pushforward.
Source: blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionOriginalModel : Over (Spec (.of D.k₀)) :=
  Over.mk ((constantExtensionModel D m hm X₀).hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))

set_option linter.unusedSectionVars false in
/-- Finite type of the base change and of its restriction to k_0.
Source: blueprint finite constant extension, parts (a)--(b)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: base change preserves finite type. The finite field extension is finite,
hence finite type and quasi-compact. Composition gives the k_0 assertions. -/
theorem constantExtensionModel_properties :
    LocallyOfFiniteType (constantExtensionModel D m hm X₀).hom ∧
      QuasiCompact (constantExtensionModel D m hm X₀).hom ∧
      LocallyOfFiniteType (constantExtensionOriginalModel D m hm X₀).hom ∧
      QuasiCompact (constantExtensionOriginalModel D m hm X₀).hom := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have := (constantExtensionField_properties D m hm).1
  have : IsFinite (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) :=
    (IsFinite.SpecMap_iff _).mpr (show Module.Finite D.k₀ (D.extensionSubfield m hm) from
      inferInstance)
  change LocallyOfFiniteType (pullback.snd X₀.hom _) ∧
    QuasiCompact (pullback.snd X₀.hom _) ∧
    LocallyOfFiniteType (pullback.snd X₀.hom _ ≫ _) ∧
    QuasiCompact (pullback.snd X₀.hom _ ≫ _)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Finite-type structure over k_m, inherited from base change.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
instance constantExtensionModel_lft :
    LocallyOfFiniteType (constantExtensionModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).1

/-- Quasi-compact structure over k_m, inherited from base change.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
instance constantExtensionModel_qc :
    QuasiCompact (constantExtensionModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.1

/-- Finite type after restriction of the finite base field.
Source: blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry). -/
instance constantExtensionOriginalModel_lft :
    LocallyOfFiniteType (constantExtensionOriginalModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.2.1

/-- Quasi-compactness after restriction of the finite base field.
Source: blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry). -/
instance constantExtensionOriginalModel_qc :
    QuasiCompact (constantExtensionOriginalModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.2.2

/-- The actual projection g_m, as a morphism over the original base field.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionProjection : constantExtensionOriginalModel D m hm X₀ ⟶ X₀ :=
  Over.homMk (pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))) pullback.condition

/-- Compatibility needed for the canonical sheet inclusion into the k_0-geometric fibre.
Source: blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: the inclusion k_m into k composed with extensionEmbedding is algebraMap.
Apply Spec and the defining pullback projection equation. -/
theorem constantExtensionSheet_compatible :
    pullback.fst (constantExtensionModel D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
        (constantExtensionOriginalModel D m hm X₀).hom =
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  change pullback.fst _ _ ≫
      ((constantExtensionModel D m hm X₀).hom ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  rw [← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

/-- The distinguished sheet for the given inclusion k_m into k, constructed by a lift.
Source: blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionSheet :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ⟶
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left :=
  pullback.lift
    (pullback.fst (constantExtensionModel D m hm X₀).hom
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)))
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).hom
    (constantExtensionSheet_compatible D m hm X₀)

/-- The distinguished sheet maps isomorphically onto the original geometric fibre.
Source: blueprint parts (a)--(b)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: associativity of base change identifies the composite with
(X_0 times_{k_0} k_m) times_{k_m} k to X_0 times_{k_0} k.
Its two projections are the canonical ones; the pullback universal property
constructs its inverse and proves both inverse identities. -/
theorem constantExtensionFiberMap_isIso :
    IsIso (constantExtensionSheet D m hm X₀ ≫
      fiberMap D (constantExtensionProjection D m hm X₀)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hs : Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) =
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let e := pullbackLeftPullbackSndIso X₀.hom
      (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≪≫
    pullback.congrHom rfl hs
  have he : constantExtensionSheet D m hm X₀ ≫
      fiberMap D (constantExtensionProjection D m hm X₀) = e.hom := by
    apply pullback.hom_ext
    · simp [e, constantExtensionSheet, fiberMap, constantExtensionProjection,
        Over.pullback, pullback.congrHom]
      rfl
    · simp [e, constantExtensionSheet, fiberMap, Over.pullback, pullback.congrHom]
      rfl
  rw [he]
  infer_instance

/-- The canonical associativity identification; no geometric scheme is replaced silently.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionFiberIso :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ≅ (D.geometricFiber X₀).left :=
  letI := constantExtensionFiberMap_isIso D m hm X₀
  asIso (constantExtensionSheet D m hm X₀ ≫
    fiberMap D (constantExtensionProjection D m hm X₀))

/-- The q^m-Frobenius returns to the distinguished sheet.
Source: Deligne, Weil II (1.1.7)--(1.1.10), blueprint part (b)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: the geometric q^m automorphism is gamma^m on the same closure.
The latter fixes k_m. Comparing both projections of the defining fibre products
proves the sheet-return identity. -/
theorem constantExtensionSheet_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫ constantExtensionSheet D m hm X₀ =
      constantExtensionSheet D m hm X₀ ≫
        localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1) := by
  let := Fintype.ofFinite D.k₀
  let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).algebra_closure
  let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).isAlgClosure
  let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
  have hn := (constantExtensionDatum D m hm).galoisMap_projections
    (constantExtensionModel D m hm X₀).hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k)
  have ho := frobeniusPower_projections D
    (constantExtensionOriginalModel D m hm X₀) (m - 1)
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have he := extensionFrobenius_power D m hm
  change ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom ≫ _ = _
  have hn' :
      ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
          pullback.fst (constantExtensionModel D m hm X₀).hom
            (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) =
        pullback.fst (constantExtensionModel D m hm X₀).hom
          (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) := by
    exact hn.1
  have hn'' :
      ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
          ((constantExtensionDatum D m hm).geometricFiber
            (constantExtensionModel D m hm X₀)).hom =
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).hom ≫
          Spec.map (CommRingCat.ofHom
            (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ m).toRingHom) := by
    rw [← he]
    exact hn.2
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [ho.1]
    simp only [constantExtensionSheet, pullback.lift_fst]
    exact hn'
  · simp only [Category.assoc]
    rw [ho.2, hm']
    simp only [constantExtensionSheet, pullback.lift_snd, pullback.lift_snd_assoc]
    exact hn''


/-- The residue degree uses the actual field map induced by g_m, not its total degree.
Source: blueprint part (a), f=[kappa(z):kappa(x)]
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionResidueDegree
    (z : (constantExtensionModel D m hm X₀).left) : ℕ :=
  letI : Algebra
      (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
      ((constantExtensionModel D m hm X₀).left.residueField z) :=
    ((constantExtensionProjection D m hm X₀).left.residueFieldMap z).hom.toAlgebra
  Module.finrank (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
    ((constantExtensionModel D m hm X₀).left.residueField z)

set_option linter.unusedSectionVars false in
/-- A closed point has closed image under the finite projection.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: g_m is finite, hence closed. The image of the one-point closed subset is closed. -/
theorem constantExtensionClosedImage_mem
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    (constantExtensionProjection D m hm X₀).left z.val ∈ closedPoints X₀.left := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have := (constantExtensionField_properties D m hm).1
  have : IsFinite (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) :=
    (IsFinite.SpecMap_iff _).mpr (show Module.Finite D.k₀ (D.extensionSubfield m hm) from
      inferInstance)
  have : IsFinite (constantExtensionProjection D m hm X₀).left :=
    show IsFinite (pullback.fst X₀.hom _) from inferInstance
  have hc := (constantExtensionProjection D m hm X₀).left.isClosedMap _ z.property
  change IsClosed {(constantExtensionProjection D m hm X₀).left z.val}
  simpa only [Set.image_singleton] using hc

/-- The closed image point with its inherited closedness proof.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry). -/
def constantExtensionClosedImage
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    {x : X₀.left // x ∈ closedPoints X₀.left} :=
  ⟨(constantExtensionProjection D m hm X₀).left z.val,
    constantExtensionClosedImage_mem D m hm X₀ z⟩

/-- The canonical fibre isomorphism intertwines the new Frobenius with the mth power.
Source: blueprint part (a)
(blueprint: def-zl-native-constant-extension-geometry).
Proof: the fibre isomorphism is the associativity map of base change, and geometric
Frobenius acts only on the closure factor. Over k_m its coefficient action is gamma^m.
Comparing the two projections gives the equality, also when the model is empty. -/
theorem constantExtensionFiber_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
        (constantExtensionFiberIso D m hm X₀).hom =
      (constantExtensionFiberIso D m hm X₀).hom ≫
        localPositivePower (D.geometricFrobenius X₀).hom (m - 1) := by
  have hn (n : ℕ) :
      localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom n ≫
          fiberMap D (constantExtensionProjection D m hm X₀) =
        fiberMap D (constantExtensionProjection D m hm X₀) ≫
          localPositivePower (D.geometricFrobenius X₀).hom n := by
    induction n with
    | zero => exact frobenius_naturality D (constantExtensionProjection D m hm X₀)
    | succ n ih =>
      rw [localPositivePower, Category.assoc, frobenius_naturality,
        ← Category.assoc, ih, Category.assoc]
      rfl
  change _ ≫ (constantExtensionSheet D m hm X₀ ≫
      fiberMap D (constantExtensionProjection D m hm X₀)) =
    (constantExtensionSheet D m hm X₀ ≫
      fiberMap D (constantExtensionProjection D m hm X₀)) ≫ _
  rw [← Category.assoc, constantExtensionSheet_return, Category.assoc, hn,
    Category.assoc]

end WeilConjectures.NativeCondensedPullback
