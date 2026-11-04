/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.WeilSheaf.Native.NativeGeometricHomComparison

/-!
# The derived internal hom of Weil complexes is a Weil complex

For Weil complexes `K` and `L` on a separated `k₀`-scheme of finite type `X`, the derived internal
hom `RHom(K, L)` of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`) is
again a Weil complex (`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom`), the Weil analogue
of `lem-sfb-dc-hom-preserves`.

Forget the Weil structure and pass to condensed `ℚ̲̄_ℓ`-modules on the geometric fibre `X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget`). This functor detects Weil complexes
among the objects of the derived category, and it carries `RHom(K, L)` to the derived hom of the
underlying condensed complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison`). That derived
hom is bounded constructible
(`AlgebraicGeometry.ProEtaleWeilSheaf.weil_geometric_hom_constructibility`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The derived internal hom preserves Weil complexes** (blueprint: `lem-fix-weil-operations`,
internal-Hom paragraph, with `lem-sfb-dc-hom-preserves`): for Weil complexes `K` and `L`, the
derived internal hom `RHom(K, L)` of pro-étale Weil sheaves is a Weil complex. -/
theorem objectProperty_derivedHom (K L : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X L.obj).obj (op K.obj)) := by
  obtain ⟨hcrit, -, hhom⟩ := ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison k₀ l X K.obj L.obj
  have := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (Profinite.padicAlgClRingObj l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).2.1
  exact (hcrit _).2 (ObjectProperty.prop_of_iso _ e.symm (hhom K L).2.2.1)

end AlgebraicGeometry.WeilComplex
