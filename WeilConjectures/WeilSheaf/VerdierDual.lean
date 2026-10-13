/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# The exceptional inverse image and the Verdier dual of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the direct image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) has a right adjoint `Rf^!` on Weil
complexes; this is the constructible adjunction `Rf_! ⊣ Rf^!` of the six-functor chapter
(`thm-coef-qbar-verdier`), stated here as
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. The exceptional inverse image
`AlgebraicGeometry.WeilComplex.upperShriek f` is *defined* as that right adjoint, which is how
the blueprint characterizes it (`def-weil-exceptional-inverse-image`). It gives the dualizing
complex `ω_X = Ra_X^! ℚ̄_ℓ` (`AlgebraicGeometry.WeilComplex.dualizingComplex`) and the Verdier
dual `𝔻_X = RHom(-, ω_X)` (`AlgebraicGeometry.WeilComplex.verdierDual`), the derived internal
hom of pro-étale Weil sheaves into `ω_X` (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`).

The statements of the duality theory for Weil complexes that the boundary duality of
`sec-deligne-laumon-a1` uses belong to the chapters on the six functors and on smooth purity;
they are stated here with `sorry`, each with the blueprint node it renders:

- `thm-coef-qbar-verdier`: the adjunction `Rf₀! ⊣ Rf^!`, the fact that `𝔻_X` preserves Weil
  complexes, its exactness, biduality `K ≅ 𝔻_X 𝔻_X K` and `Rf^! ≅ 𝔻_X f^* 𝔻_Y`;
- `fix-cor-verdier-exchange`: `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X`;
- `cor-pur-adic-and-rational-smooth-dualizing-complexes`: `ω_X ≅ ℚ̄_ℓ(d)[2d]` for `X` smooth of
  pure dimension `d`;
- `lem-sf-hom-finite-projective`: `RHom(P, N) ≅ P^∨ ⊗ N` and `P ≅ P^∨∨` for a lisse `P`;
- `prop-sf-localization-all-stages`, clause (4): `Ri^! Rj_* = 0` and the unit
  `Q ⟶ Ri^! Ri_* Q` is an isomorphism, for complementary immersions `i` and `j`.

All isomorphisms are stated as the existence of an isomorphism, as in
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The constructible exceptional adjunction** (blueprint: `thm-coef-qbar-verdier`, "the
constructible adjunction `Rf_! ⊣ Rf^!`", and `def-weil-exceptional-inverse-image`): for a
separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes of finite type, the direct image
with compact support `Rf₀!` of Weil complexes has a right adjoint. -/
theorem isLeftAdjoint_derivedLowerShriek : (derivedLowerShriek k₀ l f).IsLeftAdjoint :=
  sorry

/-- The exceptional inverse image `Rf^!` of Weil complexes along a separated morphism of finite
type `f : X ⟶ Y` of `k₀`-schemes of finite type: the right adjoint of the direct image with
compact support `Rf₀!` (blueprint: `def-weil-exceptional-inverse-image`, which characterizes
`Rf^!` by the adjunction `Hom(Rf_! K, L) ≅ Hom(K, Rf^! L)` on constructible complexes). -/
noncomputable def upperShriek : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  have := isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l) f
  (derivedLowerShriek k₀ l f).rightAdjoint

/-- The adjunction `Rf₀! ⊣ Rf^!`. -/
noncomputable def derivedLowerShriekUpperShriekAdjunction :
    derivedLowerShriek k₀ l f ⊣ upperShriek (k₀ := k₀) (l := l) f :=
  have := isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l) f
  Adjunction.ofIsLeftAdjoint _

end UpperShriek

section VerdierDual

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The dualizing complex `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k₀`-scheme of finite type `X`: the
exceptional inverse image of the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀` along the structure
morphism (blueprint: `thm-coef-qbar-verdier`, `fix-cor-verdier-exchange`). -/
noncomputable def dualizingComplex : WeilComplex k₀ l X :=
  (upperShriek (X ↘ Spec (CommRingCat.of k₀))).obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X} in
/-- **The Verdier dual preserves Weil complexes** (blueprint: `thm-coef-qbar-verdier`, the
duality `D_{X,ℚ̄_ℓ} : D^b_c(X, ℚ̄_ℓ)ᵒᵖ ⥤ D^b_c(X, ℚ̄_ℓ)` is the internal hom into
`ω_{X,ℚ̄_ℓ} = Ra_X^! ℚ̄_ℓ`): the derived internal hom `RHom(K, ω_X)` of a Weil complex `K` into
the dualizing complex is a Weil complex. -/
theorem objectProperty_derivedHom_dualizingComplex (K : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.obj)) :=
  sorry

/-- The Verdier dual `𝔻_X K = RHom(K, ω_X)` of Weil complexes on a separated `k₀`-scheme of
finite type `X`, the derived internal hom into the dualizing complex
(blueprint: `thm-coef-qbar-verdier`, `fix-cor-verdier-exchange`). -/
noncomputable def verdierDual : (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj)
    fun K ↦ objectProperty_derivedHom_dualizingComplex k₀ l K.unop

@[simp]
lemma verdierDual_obj_obj (K : (WeilComplex k₀ l X)ᵒᵖ) :
    ((verdierDual k₀ l X).obj K).obj =
      (ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.unop.obj) :=
  rfl

/-- **Verdier biduality** (blueprint: `thm-coef-qbar-verdier`, "evaluation and biduality
descend, giving a natural isomorphism `K ≅ D_{X,ℚ̄_ℓ} D_{X,ℚ̄_ℓ} K`"). -/
theorem nonempty_iso_verdierDual_rightOp_comp_verdierDual :
    Nonempty (𝟭 (WeilComplex k₀ l X) ≅ (verdierDual k₀ l X).rightOp ⋙ verdierDual k₀ l X) :=
  sorry

open Pretriangulated.Opposite in
/-- **The Verdier dual is exact** (blueprint: `thm-coef-qbar-verdier`, "an exact `ℚ̄_ℓ`-linear
anti-equivalence `D_{X,ℚ̄_ℓ}`"): it commutes with the shifts and carries distinguished
triangles of `(WeilComplex X)ᵒᵖ` to distinguished triangles. -/
theorem exists_commShift_isTriangulated_verdierDual :
    ∃ _ : (verdierDual k₀ l X).CommShift ℤ, (verdierDual k₀ l X).IsTriangulated :=
  sorry

end VerdierDual

section Exchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The exceptional inverse image as a conjugate of the pullback** (blueprint:
`thm-coef-qbar-verdier`, "`Rf^! = D_X f^* D_Y`"): `Rf^! L ≅ 𝔻_X f^* 𝔻_Y L`. -/
theorem nonempty_upperShriek_obj_iso (L : WeilComplex k₀ l Y) :
    Nonempty ((upperShriek f).obj L ≅
      (verdierDual k₀ l X).obj (op ((upperStar f).obj ((verdierDual k₀ l Y).obj (op L))))) :=
  sorry

/-- **Verdier exchange** (blueprint: `fix-cor-verdier-exchange`): for a separated morphism of
finite type `f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)`. -/
theorem nonempty_verdierDual_derivedLowerShriek_iso (M : WeilComplex k₀ l X) :
    Nonempty ((verdierDual k₀ l Y).obj (op ((derivedLowerShriek k₀ l f).obj M)) ≅
      (derivedLowerStar f).obj ((verdierDual k₀ l X).obj (op M))) :=
  sorry

end Exchange

section Smooth

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The dualizing complex of a smooth scheme** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ`): if `X`
is smooth of pure dimension `d` over `k₀`, then `ω_X ≅ ℚ̄_ℓ(d)[2d]`. -/
theorem nonempty_dualizingComplex_iso (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (dualizingComplex k₀ l X ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) :=
  sorry

end Smooth

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **The internal hom out of a lisse sheaf** (blueprint: `lem-sf-hom-finite-projective`): for
a lisse Weil sheaf `P`, a locally free `ℚ̄_ℓ,X̄`-module of finite rank, and a Weil complex `N`,
the canonical map `P^∨ ⊗ N ⟶ RHom(P, N)` is an isomorphism. -/
theorem nonempty_tensorLisse_dual_iso_derivedHom (P : WeilSheaf k₀ l X) (hP : P.IsLisse)
    (N : WeilComplex k₀ l X) :
    Nonempty (((tensorLisse (P.dual hP) hP.dual).obj N).obj ≅
      (ProEtaleWeilSheaf.derivedHom k₀ l X N.obj).obj (op (WeilSheaf.toComplex.obj P).obj)) :=
  sorry

end Lisse

section Localization

variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]

/-- **The exceptional restriction of a direct image from the open complement vanishes**
(blueprint: `prop-sf-localization-all-stages`, clause (4), `Ri^! Rj_* G = 0`): for a closed
immersion `i` with open complement `j`, `Ri^! Rj_* G = 0`. Here `Ri^!` is the right adjoint of
`Ri₀! ≅ Ri_*`. -/
theorem isZero_upperShriek_obj_derivedLowerStar_obj
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    IsZero ((upperShriek i).obj ((derivedLowerStar j).obj G)) :=
  sorry

/-- **The closed unit** (blueprint: `prop-sf-localization-all-stages`, clause (4), the unit
`Q ⟶ Ri^! i_* Q` is an isomorphism; `prop-sf-closed-unit-all-stages`): for a closed immersion
`i`, the unit of the adjunction `Ri₀! ⊣ Ri^!` is an isomorphism, `Ri₀! ≅ Ri_*` being fully
faithful. -/
theorem isIso_derivedLowerShriekUpperShriekAdjunction_unit_app (Q : WeilComplex k₀ l Z) :
    IsIso ((derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) i).unit.app Q) :=
  sorry

end Localization

end WeilComplex

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **Biduality of a lisse sheaf** (blueprint: `lem-sf-hom-finite-projective`, "the canonical
map `P ⟶ P^∨∨` is an isomorphism"). -/
theorem nonempty_iso_dual_dual (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    Nonempty (P ≅ (P.dual hP).dual hP.dual) :=
  sorry

end WeilSheaf

end AlgebraicGeometry
