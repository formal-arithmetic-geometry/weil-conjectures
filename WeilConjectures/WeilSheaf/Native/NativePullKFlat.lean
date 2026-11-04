/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Pullback and condensed realization of native K-flat complexes

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_obj`: the pullback `g^*` of
  pro-étale Weil sheaves along any morphism `g` of `k₀`-schemes sends native K-flat complexes to
  native K-flat complexes (Stacks 06YW).
- `AlgebraicGeometry.ProEtaleWeilSheaf.kFlat_condensedRealization`: the condensed realization of
  a native K-flat complex is K-flat.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullback of pro-étale Weil sheaves along any morphism `g : Z ⟶ Y` of `k₀`-schemes preserves
native K-flat complexes (Stacks 06YW). -/
theorem nativeIsKFlat_upperStar_obj {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hP : NativeIsKFlat k₀ l Y P) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P) :=
  sorry

/-- The condensed realization of a native K-flat complex of pro-étale Weil sheaves is K-flat. -/
theorem kFlat_condensedRealization (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hP : NativeIsKFlat k₀ l X P) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P)) :=
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
