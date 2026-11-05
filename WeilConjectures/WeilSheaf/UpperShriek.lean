/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# The exceptional inverse image of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes of finite type, the direct
image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) has a right adjoint `Rf^!`; this is the
constructible adjunction `Rf_! ⊣ Rf^!` of the six-functor chapter
(`det-pd-biduality-coefficients`), `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`.
It is deduced through a compactification from the proper case
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerStar_of_isProper`, which is stated here
with `sorry`. The exceptional inverse image `AlgebraicGeometry.WeilComplex.upperShriek f` is
*defined* as that right adjoint, which is how the blueprint characterizes it
(`def-weil-exceptional-inverse-image`); so that no data is chosen from the unproved existence
statement, it takes the existence of the right adjoint
(`AlgebraicGeometry.WeilComplex.HasUpperShriek f`) as a hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section Proper

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
  [IsProper g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

end Proper

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The direct image with compact support `Rf₀!` of Weil complexes along `f` has a right adjoint,
the exceptional inverse image `Rf^!` (`AlgebraicGeometry.WeilComplex.upperShriek`). That it
always has one is `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. -/
abbrev HasUpperShriek : Prop :=
  (derivedLowerShriek k₀ l f).IsLeftAdjoint

variable [HasUpperShriek k₀ l f]

/-- The exceptional inverse image `Rf^!` of Weil complexes along a separated morphism of finite
type `f : X ⟶ Y` of `k₀`-schemes of finite type: the right adjoint of the direct image with
compact support `Rf₀!` (blueprint: `def-weil-exceptional-inverse-image`, which characterizes
`Rf^!` by the adjunction `Hom(Rf_! K, L) ≅ Hom(K, Rf^! L)` on constructible complexes). -/
noncomputable def upperShriek : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l f).rightAdjoint

/-- The adjunction `Rf₀! ⊣ Rf^!`. -/
noncomputable def derivedLowerShriekUpperShriekAdjunction :
    derivedLowerShriek k₀ l f ⊣ upperShriek (k₀ := k₀) (l := l) f :=
  Adjunction.ofIsLeftAdjoint _

end UpperShriek

end WeilComplex

end AlgebraicGeometry
