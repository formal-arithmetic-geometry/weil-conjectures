/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Canonical extension-valued geometric point

The compatibility proof and fibre-product construction are reused with distinct helper names from
`LocalFrobeniusTrace`, whose original declarations remain intact.
Source: latest blueprint, local Frobenius and its canonical geometric point
(blueprint: lem-trf-extension-point-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The finite-field inclusion and a point over k₀ have matching base maps.
Source: blueprint finite-field-point clause (blueprint: lem-trf-extension-point-geometry).
Proof: the composite of extensionEmbedding with the subfield inclusion is algebraMap.
Contravariant functoriality of Spec and the equation Over.w x give the equality. -/
theorem extensionPointGeometryCompatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) :
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hbase :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.2.2.2.2.2.choose_spec
  rw [Category.assoc, Over.w x, Category.id_comp]
  change Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hbase

/-- The geometric point obtained from F_(q^n) ⊂ k by the universal fibre-product lift.
Source: blueprint xbar (blueprint: lem-trf-extension-point-geometry). -/
def extensionPointGeometry (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (𝟙 _) (extensionPointGeometryCompatible D Y₀ n hn x)

end WeilConjectures
