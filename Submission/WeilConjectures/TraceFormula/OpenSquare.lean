/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import Submission.WeilConjectures.TraceFormula.Frobenius

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# Open squares, the open-square exchange and the Weil extension by zero

Let `j : U ⟶ Y` be an open immersion of separated `k`-schemes of finite type.

* **Frobenius open squares** (blueprint `lem-trf-frobenius-open-square`). If `Φ_Y` is the model
  Frobenius of `Y = Y₀ ×_{k₀} k`, `j` is the base change of an open immersion `j₀ : U₀ ⟶ Y₀` and
  `Φ_U ≫ j = j ≫ Φ_Y`, then every square `Φ_U^m ≫ j = j ≫ Φ_Y^m` is cartesian
  (`ProEtale.CondensedRing.isPullback_frobeniusIterate_of_isOpenImmersion`). The reason is that
  the `q`-power Frobenius of `Y₀` is the identity on points, so `Φ_Y⁻¹(U) = U`; the general
  criterion is `AlgebraicGeometry.IsOpenImmersion.isPullback_of_preimage_range_subset`.
* **The open-square exchange** (blueprint `lem-trf-open-square-exchange`). For a cartesian square
  `g_U ≫ j = j' ≫ g` with `j`, `j'` open immersions, `b_g : Lg^* j_! ≅ j'_! Lg_U^*`
  (`ProEtale.CondensedRing.openSquareExchange`); its restriction to `U'` is the identity
  (`ProEtale.CondensedRing.unit_comp_map_openSquareExchange_inv`).
* **The Weil extension by zero** (blueprint `def-trf-weil-extension-zero`). For a cartesian square
  `Φ_U ≫ j = j ≫ Φ_Y`, a Weil object `(K, φ)` for `Φ_U` gives the Weil object
  `(j_! K, j_! φ ∘ b_{Φ_Y})` for `Φ_Y` (`ProEtale.CondensedRing.weilOpenLowerShriek`), functorially.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-! ### Open squares of schemes -/

/-- Let `j : U ⟶ Y` be an open immersion and `g : U ⟶ U`, `f : Y ⟶ Y` with `g ≫ j = j ≫ f`. If
`f` maps no point outside `U` into `U`, the square `g ≫ j = j ≫ f` is cartesian. -/
lemma IsOpenImmersion.isPullback_of_preimage_range_subset {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] {g : U ⟶ U} {f : Y ⟶ Y} (w : g ≫ j = j ≫ f)
    (h : f.base ⁻¹' Set.range j.base ⊆ Set.range j.base) : IsPullback g j j f :=
  IsOpenImmersion.isPullback g j j f w.symm (TopologicalSpace.Opens.ext (subset_antisymm h
    (by
      rintro _ ⟨x, rfl⟩
      exact ⟨g.base x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩)))

/-- The `Over S` version of `IsOpenImmersion.isPullback_of_preimage_range_subset`. -/
lemma IsOpenImmersion.isPullback_over_of_preimage_range_subset {S : Scheme.{u}} {U Y : Over S}
    (j : U ⟶ Y) [IsOpenImmersion j.left] {g : U ⟶ U} {f : Y ⟶ Y} (w : g ≫ j = j ≫ f)
    (h : f.left.base ⁻¹' Set.range j.left.base ⊆ Set.range j.left.base) : IsPullback g j j f :=
  IsPullback.of_map (Over.forget S) w
    (IsOpenImmersion.isPullback_of_preimage_range_subset j.left (congrArg CommaMorphism.left w) h)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Frobenius open squares -/

section FrobeniusSquare

variable {k : Type u} [Field k] {Y U : Over (Spec (.of k))} {ΦY : Y ⟶ Y}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {Y₀ : Scheme.{u}}
  {f₀ : Y₀ ⟶ Spec (.of k₀)} {p : Y.left ⟶ Y₀}

/-- **Frobenius preserves an open subscheme defined over the finite field** (blueprint
`lem-trf-frobenius-open-square`): let `Φ_Y` be the model Frobenius of `Y = Y₀ ×_{k₀} k`, let
`j : U ⟶ Y` be the base change of an open immersion `j₀ : U₀ ⟶ Y₀` (the square
`q ≫ j₀ = j ≫ p` is cartesian) and let `Φ_U : U ⟶ U` satisfy `Φ_U ≫ j = j ≫ Φ_Y`. Then for every
`m ≥ 0` the square `Φ_U^m ≫ j = j ≫ Φ_Y^m` is cartesian: the Frobenius of `Y₀` is the identity
on points, so `Φ_Y⁻¹(U) = U`. -/
theorem isPullback_frobeniusIterate_of_isOpenImmersion (hΦ : IsModelFrobenius ΦY f₀ p)
    {U₀ : Scheme.{u}} (j₀ : U₀ ⟶ Y₀) {q : U.left ⟶ U₀} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hq : IsPullback q j.left j₀ p) {ΦU : U ⟶ U} (hw : ΦU ≫ j = j ≫ ΦY) (m : ℕ) :
    IsPullback (frobeniusIterate ΦU m) j j (frobeniusIterate ΦY m) := by
  have h₁ : IsPullback ΦU j j ΦY := by
    refine IsOpenImmersion.isPullback_over_of_preimage_range_subset j hw ?_
    obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
    rintro y ⟨x, hx⟩
    have e : j₀.base (q.base x) = p.base y := by
      rw [← Scheme.Hom.comp_apply, hq.w,Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply,
        hp, Scheme.Hom.comp_apply, hF₀.base_apply f₀]
    obtain ⟨z, -, hz⟩ := exists_preimage_of_isPullback hq _ _ e
    exact ⟨z, hz⟩
  induction m with
  | zero =>
    rw [frobeniusIterate_zero, frobeniusIterate_zero]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ m ih =>
    rw [frobeniusIterate_succ, frobeniusIterate_succ]
    exact h₁.paste_horiz ih

end FrobeniusSquare

/-! ### The open-square exchange -/

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U Y U' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
  [IsSeparated U'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {j : U ⟶ Y} {g : Y' ⟶ Y} {j' : U' ⟶ Y'} {gU : U' ⟶ U}
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

/-- **The open-square exchange** (blueprint `lem-trf-open-square-exchange`): for a cartesian
square `g_U ≫ j = j' ≫ g` with `j`, `j'` open immersions, the base change isomorphism
`b_g : Lg^* j_! ≅ j'_! Lg_U^*` of the extension by zero, the inverse of the canonical exchange
morphism `Lg_U^* ⋙ j'_! ⟶ j_! ⋙ Lg^*`. -/
noncomputable abbrev openSquareExchange (sq : IsPullback gU j' j g) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gU ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j' :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' _ ℓ sq

omit [Fact ℓ.Prime] in
/-- Abstract form of `unit_comp_map_openSquareExchange_inv`: the restriction of the exchange
morphism `exchangeLeft aj aj' θ` along the right adjoint `jU'` is `θ`, up to the units. -/
lemma Adjunction.unit_comp_map_exchangeLeft_app {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B'] {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU')
    (K : A) :
    aj'.unit.app (H.obj K) ≫ jU'.map ((Adjunction.exchangeLeft aj aj' θ).app K) =
      H.map (aj.unit.app K) ≫ θ.hom.app (jS.obj K) := by
  have h := aj'.unit.naturality (H.map (aj.unit.app K) ≫ θ.hom.app (jS.obj K))
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at h
  rw [Adjunction.exchangeLeft_app, ← Functor.map_comp_assoc, Functor.map_comp, ← Category.assoc,
    ← h, Category.assoc, Adjunction.right_triangle_components, Category.comp_id]

/-- `unit_comp_map_openSquareExchange_inv` for an arbitrary coefficient ring `Λ`. -/
lemma unit_comp_map_baseChangeIso_inv_aux (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : IsPullback gU j' j g) (K : Dᵇc(U.left)⟦Λ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app
        ((boundedConstructibleUpperStar Λ ℓ gU).obj K) ≫
      (boundedConstructibleUpperStar Λ ℓ j').map
        ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).inv.app K) =
    (boundedConstructibleUpperStar Λ ℓ gU).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app K) ≫
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv]
  exact Adjunction.unit_comp_map_exchangeLeft_app _ _ _ K

/-- **The open-square exchange restricts to the identity on `U'`** (blueprint
`lem-trf-open-square-exchange`): after restriction along `Lj'^*`, the inverse of `b_g` at `K` is
the pullback comparison `Lj^* ⋙ Lg_U^* ≅ Lg^* ⋙ Lj'^*` of the square at `j_! K`, up to the units
of `j_! ⊣ Lj^*` and `j'_! ⊣ Lj'^*` (which are isomorphisms):
```
Lg_U^* K ⟶ Lj'^* j'_! Lg_U^* K --Lj'^* b_g⁻¹--> Lj'^* Lg^* j_! K
  =  Lg_U^* K ⟶ Lg_U^* Lj^* j_! K ≅ Lj'^* Lg^* j_! K.
```
-/
lemma unit_comp_map_openSquareExchange_inv (sq : IsPullback gU j' j g)
    (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j').unit.app
        ((boundedConstructibleUpperStar _ ℓ gU).obj K) ≫
      (boundedConstructibleUpperStar _ ℓ j').map ((openSquareExchange ℓ sq).inv.app K) =
    (boundedConstructibleUpperStar _ ℓ gU).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).unit.app K) ≫
      (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq.flip).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj K) := by
  exact unit_comp_map_baseChangeIso_inv_aux ℓ _ sq K
end Exchange

section IdSquare

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U Y : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

end IdSquare

/-! ### The Weil extension by zero -/

section Weil

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U Y : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {ΦU : U ⟶ U} {ΦY : Y ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j.left]

/-- **The Weil extension by zero** (blueprint `def-trf-weil-extension-zero`): for an open
immersion `j : U ⟶ Y` and a cartesian square `Φ_U ≫ j = j ≫ Φ_Y` (for instance that of
`isPullback_frobeniusIterate_of_isOpenImmersion`), a Weil object `(K, φ)` for `Φ_U` is sent to
`(j_! K, j_! φ ∘ b_{Φ_Y})`, with
```
LΦ_Y^* j_! K --b_{Φ_Y}--> j_! LΦ_U^* K --j_! φ--> j_! K,
```
`b_{Φ_Y}` the open-square exchange `openSquareExchange` (blueprint
`rem-ptr-trf-weil-extension-zero-10`). Being a functor between categories of Weil objects, the
pair `(j_! K, j_! φ ∘ b_{Φ_Y})` is again a Weil object and the construction is functorial in
`(K, φ)` (blueprint `rem-ptr-trf-weil-extension-zero-11`). -/
noncomputable def weilOpenLowerShriek (sq : IsPullback ΦU j j ΦY) :
    WeilBoundedConstructible ℓ ΦU ⥤ WeilBoundedConstructible ℓ ΦY :=
  IsoAlgebra.mapOfNatIso (openSquareExchange ℓ sq)

@[simp]
lemma weilOpenLowerShriek_obj_carrier (sq : IsPullback ΦU j j ΦY)
    (K : WeilBoundedConstructible ℓ ΦU) :
    ((weilOpenLowerShriek ℓ sq).obj K).carrier =
      (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        K.carrier :=
  rfl

end Weil

end AlgebraicGeometry.ProEtale.CondensedRing
