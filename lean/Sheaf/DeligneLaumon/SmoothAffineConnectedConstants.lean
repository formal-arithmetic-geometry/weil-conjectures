/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.PointCount
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.AlgebraicGeometry.GeometricallyConnectedImageCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Algebraic.Integral

/-! # The constant field of a connected smooth affine scheme

Source: Stacks Project, `varieties.tex`, proof of
`lemma-image-connected-component`, and the constant-field step in
`sk-i-dl-general-real`.
(blueprint: lem-zl-smooth-affine-connected-constants).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A connected smooth affine scheme over a finite field has a smooth,
geometrically connected structure over a finite extension of that field.
This changes only the structure morphism of the given scheme.

Source: Stacks Project, `varieties.tex`, proof of
`lemma-image-connected-component`, and blueprint `sk-i-dl-general-real`,
constant-field reduction.
(blueprint: lem-zl-smooth-affine-connected-constants).

Proof: Let A be the global sections. It is a finitely generated algebra over k.
Smoothness implies regularity, and connectedness then makes A a normal domain.
Let L be the integral closure of k in A. Since k is a field and A is a domain,
L is a field. Choose a finite point of X; it exists since X is nonempty and of
finite type over k. Evaluation embeds L into the finite residue field at that
point. Thus L itself is finite. Normality identifies L with the relative
algebraic closure of k in Frac(A).
The inclusion L → A defines g : X → Spec L and gives the displayed factorization.
Since k is perfect, L/k is finite separable and etale. Formal smoothness of A
lifts from k to L by formal etaleness of L/k. A is still finite type over L;
as L is Noetherian this is finite presentation. Thus g is smooth.
Finally L is algebraically closed in Frac(A) by transitivity of algebraicity.
The generic point Spec Frac(A) is therefore geometrically irreducible over L
(k is perfect), hence geometrically connected. The connected-image criterion
(Stacks `lemma-geometrically-connected-if-connected-and-point`) makes X
geometrically connected over L. ConnectedSpace includes nonemptiness; dimension
zero causes no exception, and no rational point over L is asserted. -/
theorem exists_smooth_geometricallyConnected_constant_field
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsAffine X] [ConnectedSpace X] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L)
      (g : X ⟶ Spec (CommRingCat.of L)),
      f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Smooth g ∧ GeometricallyConnected g := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsIntegral X := IsRegular.isIntegral X
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  let A : Type u := Γ(X, ⊤)
  let φ : CommRingCat.of k ⟶ CommRingCat.of A := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let : Algebra k A := φ.hom.toAlgebra
  have hfac : X.toSpecΓ ≫ Spec.map φ = f := by
    dsimp only [φ]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hspec : Smooth (Spec.map φ) := by
    have heq : X.isoSpec.inv ≫ f = Spec.map φ := by
      rw [← hfac, ← Category.assoc, X.isoSpec_inv_toSpecΓ, Category.id_comp]
    rw [← heq]
    infer_instance
  have : Algebra.Smooth k A := HasRingHomProperty.Spec_iff.mp hspec
  let L := integralClosure k A
  let : Field L := (isField_of_isIntegral_of_isField' (Field.toIsField k)).toField
  obtain ⟨x, hx⟩ := f.exists_mem_finitePoints
  have : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  let ev : L →+* X.residueField x := (X.Γevaluation x).hom.comp L.val.toRingHom
  have : Finite L := Finite.of_injective ev ev.injective
  have : Module.Finite k L := Module.Finite.of_finite
  have : Algebra.Etale k L := Algebra.Etale.of_finite_of_isSeparable
  have : Algebra.FiniteType L A := Algebra.FiniteType.of_restrictScalars_finiteType k L A
  have : Algebra.FormallySmooth L A := Algebra.FormallySmooth.of_restrictScalars k L A
  have : Algebra.FinitePresentation L A := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have : Algebra.Smooth L A := ⟨inferInstance, inferInstance⟩
  let g : X ⟶ Spec (.of L) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L.val.toRingHom)
  have hg : Smooth g := by
    have : Smooth (Spec.map (CommRingCat.ofHom L.val.toRingHom)) :=
      HasRingHomProperty.Spec_iff.mpr (show (algebraMap L A).Smooth from
        RingHom.smooth_algebraMap.mpr inferInstance)
    dsimp only [g]
    infer_instance
  have hfg : f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← hfac]
    dsimp only [g]
    rw [Category.assoc, ← Spec.map_comp]
    rfl
  let : Algebra k X.functionField := ((algebraMap A X.functionField).comp
    (algebraMap k A)).toAlgebra
  have : IsScalarTower k A X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsIntegrallyClosed A :=
    Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk
      (IsRegular.isIntegrallyClosed_stalk (X := X)) ⊤
  have : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  have halg : ∀ a : X.functionField, IsAlgebraic L a →
      ∃ b : L, algebraMap L X.functionField b = a := by
    intro a ha
    have hak : _root_.IsIntegral k a := isIntegral_trans a ha.isIntegral
    have haA : _root_.IsIntegral A a := hak.tower_top
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral haA
    have hbk : _root_.IsIntegral k b :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom k A X.functionField)
        (IsFractionRing.injective A X.functionField)).mp (hb.symm ▸ hak)
    exact ⟨⟨b, hbk⟩, hb⟩
  have : GeometricallyIrreducible (Spec.map
      (CommRingCat.ofHom (algebraMap L X.functionField))) :=
    geometricallyIrreducible_of_isAlgebraic_mem halg
  let : X.Over (Spec (.of L)) := ⟨g⟩
  let : (Spec X.functionField).Over (Spec (.of L)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap L X.functionField))⟩
  have : GeometricallyConnected (Spec X.functionField ↘ Spec (.of L)) :=
    show GeometricallyConnected (Spec.map
      (CommRingCat.ofHom (algebraMap L X.functionField))) from
        GeometricallyIrreducible.geometricallyConnected _
  have : X.fromSpecFunctionField.IsOver (Spec (.of L)) := ⟨by
    change X.fromSpecFunctionField ≫ g = _
    dsimp only [g, Scheme.fromSpecFunctionField]
    rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    rfl⟩
  have hgeo : GeometricallyConnected g :=
    GeometricallyConnected.of_connectedSpace_of_geometricallyConnected X.fromSpecFunctionField
  exact ⟨L, inferInstance, inferInstance, inferInstance, g, hfg, hg, hgeo⟩

end AlgebraicGeometry
