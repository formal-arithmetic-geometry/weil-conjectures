/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.FieldTheory.FieldExtensionGeometricallyIrreducible
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedImageCriterion

/-! Constant-field factorization data for a connected normal finite-field scheme.

Source: Stacks Project, properties.tex, Tag 033L; varieties.tex, Tags 04PZ and 054Q.
(blueprint: lem-dl-a1-normal-constant-field-basic).

Given the integral structure, the proof constructs the algebraically closed constant subfield
and its global-sections inclusion, then proves finite degree and geometric connectedness.
The construction uses the normality, finite-type and connectedness hypotheses exactly as in
Tags 033L, 00FV, 054Q and 01I1. The theorem is split from the component calculation because
the latter additionally requires affine tensor-product decompositions and Frobenius transport.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The constant-field and factorization data needed for the geometric component calculation.
Source: Stacks Project, varieties.tex, Tags 04PZ and 054Q.
(blueprint: def-dl-a1-normal-constant-field-basic-data). -/
structure NormalConstantFieldBasicData
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField] where
  algebraMap_eq :
    algebraMap D.k₀ U₀.left.functionField =
      ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ U₀.hom.appTop ≫
        (@Scheme.germToFunctionField U₀.left inferInstance ⊤
          ⟨⟨Classical.choice inferInstance, trivial⟩⟩)).hom
  L : IntermediateField D.k₀ U₀.left.functionField
  L_eq : L = algebraicClosure D.k₀ U₀.left.functionField
  finite : Module.Finite D.k₀ L
  e : L →+* Γ(U₀.left, ⊤)
  g : U₀.left ⟶ Spec (CommRingCat.of L)
  germ_e :
    ((@Scheme.germToFunctionField U₀.left inferInstance ⊤
      ⟨⟨Classical.choice inferInstance, trivial⟩⟩)).hom.comp e = L.subtype
  g_eq : g = U₀.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e)
  factor : g ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ L)) = U₀.hom
  geometricallyConnected : GeometricallyConnected g
  d : ℕ
  d_eq : d = Module.finrank D.k₀ L
  d_pos : 1 ≤ d

/-- The first part of the normal constant-field theorem.

Source: Stacks Project, properties.tex, Tag 033L; varieties.tex, Tags 04PZ and 054Q.
(blueprint: lem-dl-a1-normal-constant-field-basic).

Proof: on each affine
open, the generic stalk is the fraction field and normality of all prime localizations makes
the coordinate ring integrally closed. Every element algebraic over the finite base is therefore
in every affine ring, and the resulting sections glue by injectivity of the generic germ. A
maximal ideal of a finite-type affine chart gives a finite residue field, into which the constant
field injects, proving finite degree. Finally the constant field is algebraically closed in the
function field; the field-extension and generic-point criteria imply geometric connectedness.
-/
theorem exists_normal_constant_field_basic
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    (hN : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x))
    [IsIntegral U₀.left] :
    ∃ (_ : Algebra D.k₀ U₀.left.functionField),
      Nonempty (NormalConstantFieldBasicData D U₀) := by
  classical
  have : Nonempty (⊤ : U₀.left.Opens) := ⟨⟨Classical.arbitrary U₀.left, trivial⟩⟩
  let X := U₀.left
  let A : Type u := Γ(X, ⊤)
  let φ := (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ U₀.hom.appTop
  let : Algebra D.k₀ A := φ.hom.toAlgebra
  let a : D.k₀ →+* X.functionField := (X.germToFunctionField ⊤).hom.comp φ.hom
  let : Algebra D.k₀ X.functionField := a.toAlgebra
  let : Algebra A X.functionField := (X.germToFunctionField ⊤).hom.toAlgebra
  have : IsScalarTower D.k₀ A X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let L := algebraicClosure D.k₀ X.functionField
  have hex (z : L) : ∃ t : Γ(X, ⊤), X.germToFunctionField ⊤ t = (z : X.functionField) := by
    apply Scheme.exists_germToFunctionField_eq ⊤
    intro x hx
    have : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
    let : Algebra A (X.presheaf.stalk x) := (X.presheaf.germ ⊤ x hx).hom.toAlgebra
    let xx : (⊤ : X.Opens) := ⟨x, hx⟩
    have : IsScalarTower A (X.presheaf.stalk x) X.functionField := by
      dsimp only [A]
      exact functionField_isScalarTower X ⊤ xx
    have hz : _root_.IsIntegral A (z : X.functionField) := z.2.tower_top
    exact (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk x)).mp
      (hz.tower_top (A := X.presheaf.stalk x))
  let e : L →+* A :=
    { toFun := fun z ↦ Classical.choose (hex z)
      map_zero' := by
        apply X.germToFunctionField_injective ⊤
        simpa using Classical.choose_spec (hex 0)
      map_one' := by
        apply X.germToFunctionField_injective ⊤
        simpa using Classical.choose_spec (hex 1)
      map_add' := by
        intro x y
        apply X.germToFunctionField_injective ⊤
        simp only [map_add, Classical.choose_spec (hex _)]
        rfl
      map_mul' := by
        intro x y
        apply X.germToFunctionField_injective ⊤
        simp only [map_mul, Classical.choose_spec (hex _)]
        rfl }
  have he (z : L) : X.germToFunctionField ⊤ (e z) = (z : X.functionField) :=
    Classical.choose_spec (hex z)
  have heφ : e.comp (algebraMap D.k₀ L) = φ.hom := by
    ext c
    apply X.germToFunctionField_injective ⊤
    exact he (algebraMap D.k₀ L c)
  obtain ⟨x, hx⟩ := U₀.hom.exists_mem_finitePoints
  have : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  let ev : L →+* X.residueField x := (X.Γevaluation x).hom.comp e
  have : Finite L := Finite.of_injective ev ev.injective
  have hfinite : Module.Finite D.k₀ L := Module.Finite.of_finite
  let g : X ⟶ Spec (.of L) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e)
  have hfac : X.toSpecΓ ≫ Spec.map φ = U₀.hom := by
    dsimp only [φ]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hfactor : g ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ L)) = U₀.hom := by
    dsimp only [g]
    rw [Category.assoc, ← Spec.map_comp]
    change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (e.comp (algebraMap D.k₀ L))) = _
    rw [heφ]
    exact hfac
  have halg : ∀ z : X.functionField, IsAlgebraic L z →
      ∃ b : L, algebraMap L X.functionField b = z := by
    intro z hz
    exact ⟨⟨z, isIntegral_trans z hz.isIntegral⟩, rfl⟩
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
    congr 1
    ext z
    exact he z⟩
  have hgeo : GeometricallyConnected g :=
    GeometricallyConnected.of_connectedSpace_of_geometricallyConnected X.fromSpecFunctionField
  refine ⟨a.toAlgebra, ⟨{
    algebraMap_eq := rfl
    L := L
    L_eq := rfl
    finite := hfinite
    e := e
    g := g
    germ_e := ?_
    g_eq := rfl
    factor := hfactor
    geometricallyConnected := hgeo
    d := Module.finrank D.k₀ L
    d_eq := rfl
    d_pos := ?_ }⟩⟩
  · ext z
    exact he z
  · exact Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos.ne')

end AlgebraicGeometry
