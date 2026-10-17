/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.WeilSheaf.Bidual
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
the blueprint characterizes it (`def-weil-exceptional-inverse-image`); the existence of the
right adjoint is an instance argument of the definition, so that no definition depends on the
unproved statement. It gives the dualizing complex `ω_X = Ra_X^! ℚ̄_ℓ`
(`AlgebraicGeometry.WeilComplex.dualizingComplex`) and the Verdier dual `𝔻_X = RHom(-, ω_X)`
(`AlgebraicGeometry.WeilComplex.verdierDual`), the derived internal hom of pro-étale Weil sheaves
into `ω_X` (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`).
The Verdier dual on `X` takes as instance argument
`AlgebraicGeometry.WeilComplex.HasVerdierDual`, the existence of `Ra_X^!` together with the
fact that `RHom(-, ω_X)` preserves Weil complexes; it holds by `thm-coef-qbar-verdier`
(`AlgebraicGeometry.WeilComplex.hasVerdierDual`).

The statements of the duality theory for Weil complexes that the boundary duality of
`sec-deligne-laumon-a1` uses belong to the chapters on the six functors and on smooth purity;
they are stated here with `sorry`, each with the blueprint node it renders:

- `thm-coef-qbar-verdier`: the adjunction `Rf₀! ⊣ Rf^!`, the fact that `𝔻_X` preserves Weil
  complexes, its exactness, biduality `K ≅ 𝔻_X 𝔻_X K` (its clause
  `Ri^! ≅ 𝔻_Z i^* 𝔻_X` for a closed immersion `i` is stated in
  `WeilConjectures.WeilSheaf.VerdierDualLocalization`);
- `fix-cor-verdier-exchange`: `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X`;
- `cor-pur-adic-and-rational-smooth-dualizing-complexes`: `ω_X ≅ ℚ̄_ℓ(d)[2d]` for `X` smooth of
  pure dimension `d`;
- `lem-sf-hom-finite-projective`: `RHom(P, N) ≅ P^∨ ⊗ N` for a lisse `P` (its biduality
  clause `P ≅ P^∨∨` is `AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`, in
  `WeilConjectures.WeilSheaf.Bidual`).

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
noncomputable def upperShriek [(derivedLowerShriek k₀ l f).IsLeftAdjoint] :
    WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l f).rightAdjoint

end UpperShriek

section VerdierDual

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

section Dualizing

variable [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]

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

end Dualizing

/-- The input needed to define the Verdier dual of Weil complexes on `X`: the direct image with
compact support along the structure morphism `a_X` has a right adjoint `Ra_X^!`, so that the
dualizing complex `ω_X = Ra_X^! ℚ̄_ℓ` is defined, and the derived internal hom into `ω_X`
preserves Weil complexes. Both are consequences of `thm-coef-qbar-verdier`
(`AlgebraicGeometry.WeilComplex.hasVerdierDual`); they are taken as an instance argument so
that the Verdier dual is defined without depending on the unproved statements. -/
class HasVerdierDual : Prop where
  isLeftAdjoint : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint
  objectProperty_derivedHom (K : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.obj))

attribute [instance 100] HasVerdierDual.isLeftAdjoint

/-- The Verdier dual of Weil complexes is defined on every separated `k₀`-scheme of finite type,
by `thm-coef-qbar-verdier` (`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek` and
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex`). -/
theorem hasVerdierDual : HasVerdierDual k₀ l X :=
  have := isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀))
  ⟨this, objectProperty_derivedHom_dualizingComplex k₀ l⟩

variable [HasVerdierDual k₀ l X]

/-- The Verdier dual `𝔻_X K = RHom(K, ω_X)` of Weil complexes on a separated `k₀`-scheme of
finite type `X`, the derived internal hom into the dualizing complex
(blueprint: `thm-coef-qbar-verdier`, `fix-cor-verdier-exchange`). -/
noncomputable def verdierDual : (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj)
    fun K ↦ HasVerdierDual.objectProperty_derivedHom K.unop

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
  [HasVerdierDual k₀ l X] [HasVerdierDual k₀ l Y]

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
  [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]

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

/-- For a lisse Weil sheaf `P`, the tensor product `P^∨ ⊗ N` with its dual is the right derived
functor of the internal hom `𝓗om(P, -)` evaluated at `N`: `P^∨ ⊗ -` is by definition
`R𝓗om(P^∨∨, -)` (`AlgebraicGeometry.WeilComplex.tensorLisse`), and `P ≅ P^∨∨`
(`AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`). -/
theorem nonempty_tensorLisse_dual_iso_rightDerivedFunctor_ihomFunctor (P : WeilSheaf k₀ l X)
    (hP : P.IsLisse) (N : WeilComplex k₀ l X) :
    Nonempty (((tensorLisse (P.dual hP) hP.dual).obj N).obj ≅
      (ProEtaleWeilSheaf.ihomFunctor k₀ l X P.obj).rightDerivedFunctor.obj N.obj) := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_dual_dual P hP
  exact ⟨(Functor.rightDerivedFunctorNatIso ((ProEtaleWeilSheaf.ihomBifunctor k₀ l X).mapIso
    ((ObjectProperty.ι _).mapIso e).op)).app N.obj⟩

/-- **The internal hom out of a lisse sheaf** (blueprint: `lem-sf-hom-finite-projective`): for
a lisse Weil sheaf `P`, a locally free `ℚ̄_ℓ,X̄`-module of finite rank, and a Weil complex `N`,
the canonical map `P^∨ ⊗ N ⟶ RHom(P, N)` is an isomorphism. -/
theorem nonempty_tensorLisse_dual_iso_derivedHom (P : WeilSheaf k₀ l X) (hP : P.IsLisse)
    (N : WeilComplex k₀ l X) :
    Nonempty (((tensorLisse (P.dual hP) hP.dual).obj N).obj ≅
      (ProEtaleWeilSheaf.derivedHom k₀ l X N.obj).obj (op (WeilSheaf.toComplex.obj P).obj)) :=
  sorry

end Lisse

end WeilComplex

end AlgebraicGeometry
