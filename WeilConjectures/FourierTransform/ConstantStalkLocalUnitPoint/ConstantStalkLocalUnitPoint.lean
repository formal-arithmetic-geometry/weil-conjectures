/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace

/-! # The embedded geometric point of a finite-field point and its semilinear return

Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
prop-every-iterate-trace.md, constant-sheaf clause; return convention of
def-weil-local-frobenius-trace (blueprint: lem-zl-constant-stalk-local-unit-point).

An `F_{q^n}`-point `x` of `Y₀` and an embedding `ι : F_{q^n} → k` over `k₀` give the
geometric point `(x ∘ Spec ι, id) : Spec k → Y₀ ×_{k₀} k`. Its `n`-th positive power of
the geometric Frobenius returns it along the `n`-th power of the field Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.ConstantStalkLocalUnitPoint

/-- The geometric point `(x ∘ Spec ι, id)` of `Y₀ ×_{k₀} k` defined by a finite-field point
and an embedding of `F_{q^n}` into `k` over `k₀`.
Source: def-weil-local-frobenius-trace, associated geometric point
(blueprint: lem-zl-constant-stalk-local-unit-point). -/
def embeddingPoint (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom iota) ≫ x.left) (𝟙 _)
    (by
      rw [Category.assoc, Over.w x, Category.id_comp]
      change Spec.map (CommRingCat.ofHom iota) ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hι)

section Helpers

variable (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end Helpers

end WeilConjectures.ConstantStalkLocalUnitPoint
