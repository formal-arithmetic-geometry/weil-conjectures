/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.CategoryTheory.Triangulated.CompactObjExtension
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleEmbedding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The exceptional inverse image on `Loc(Dᵇc)`, `ℓ`-adic coefficients

Let `Λ` be a commutative condensed ring. For a scheme `X` the localizing closure
`Loc(Dᵇc(X)⟦Λ⟧)` (blueprint `sk-def-localizing-closure`) is the smallest triangulated
subcategory of `D(X_proét, Λ_X)` (module objects over `Λ_X = p_X^* Λ`) containing the bounded
constructible complexes `Dᵇc(X)⟦Λ⟧` and closed under direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). For the `ℓ`-adic
coefficient rings `Λ = 𝒪_E, E, ℚ̄_ℓ` (`ℤ_ℓ` and `ℚ_ℓ` being the case `E = ℚ_ℓ`), one has
`Dctf(X, Λ) = Dᵇc(X, Λ)`, so this is the blueprint's `Loc(Dctf(X, Λ))`.

For a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f : X ⟶ Y` such that `Rf_!(c)⟦Λ⟧` maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`, its restriction is the functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekLocalizing`). Under the
hypotheses of Brown representability (blueprint `sk-lem-brown-hypotheses`) and the properties of
`Rf_!(c)` of blueprint `det-sf-comp-coherence-single`, it has an exact right adjoint `f^!`,
which preserves direct sums and is unique up to unique isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`,
blueprint `sk-prop-sf-existence`). This is uniform in `Λ`.

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible and which is finite or separably closed (so that
`cd_ℓ(k)` is finite; without this, the compact generation fails, e.g. for `k = ℝ`), the two
inputs are the theorems

| `Λ` | `sk-lem-brown-hypotheses` | `det-sf-comp-coherence-single` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`), and the existence theorem
follows. The finite coefficient rings are treated in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing`.

## The formal reductions

For `sk-lem-brown-hypotheses`, on a separated finite-type (hence noetherian) `k`-scheme `X`:
`Loc(Dᵇc(X)⟦Λ⟧)` is idempotent complete, as is any pretriangulated category with countable
coproducts (`ObjectProperty.isIdempotentComplete_localizingClosure`); `Dᵇc(X)⟦Λ⟧` is stable under
shifts, so its objects detect zero objects of `Loc(Dᵇc(X)⟦Λ⟧)`
(`ObjectProperty.isZero_of_forall_eq_zero_localizingClosure`); and it is essentially small, its
objects being iterated extensions of shifted constructible sheaves
(`exists_skeleton_boundedConstructible`). What remains is the compactness of the bounded
constructible complexes in `Loc(Dᵇc(X)⟦Λ⟧)` (`compactlyGenerates_of_isCompactObj`), which reduces
to that of the constructible sheaves.

For `det-sf-comp-coherence-single`, with `X̄` noetherian: `j_!` is exact and preserves direct sums,
so it maps `Dᵇc` into `Dᵇc`, as it maps constructible sheaves to constructible sheaves
(`isConstructibleModuleObject_openImmersionLowerShriek_obj`), and then
`Loc` into `Loc` (`localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj`);
the composite `Rp_* ∘ j_!` then has the required properties as soon as `Rp_*` does
(`lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses`).

The statements of `det-sf-comp-coherence-single` take a noetherian base `Y`: over a merely
quasi-compact quasi-separated base, `Rp_*` need not preserve constructibility. For instance the
inclusion `p` of the origin into `Y = Spec k[x₁, x₂, …]` is proper, but `p_* Λ` is supported on
the closed point, which is not a constructible subset of `Y`.

## Sorried input

- The inputs of `isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj`,
  `isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj` (blueprint
  `sk-thm-constructible-compactness`) and
  `isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj` (blueprint
  `sk-prop-int-compactness`), that constructible sheaves are compact in `Loc(Dᵇc(X)⟦Λ⟧)`: the
  closure properties of the ind-constructible sheaves (`sk-prop-ind-heart`), the continuity of
  `Ext` out of a constructible sheaf (`sk-lem-constructible-ext-continuity`) and the uniform
  `Ext` bound (`sk-lem-uniform-constructible-ext`), see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic`. The
  compactness follows by the finite-window argument and left completeness. By dévissage, all
  bounded constructible complexes are compact
  (`isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible`).
- The inputs of `properLowerStarHypotheses_continuousMapRingObj`,
  `properLowerStarHypotheses_padicAlgClRingObj` and
  `properLowerStarHypotheses_padicIntegersRingObj` (for `p` proper, `Rp_*` preserves `Dᵇc` and
  direct sums on `Loc(Dᵇc)`): that `Rp_*` preserves `Dᵇc` (blueprint
  `sk-thm-sfb-proper-base-change`) and has finite amplitude and commutes with direct sums on the
  ind-constructible heart (blueprints `sk-lem-proper-heart-bound`,
  `det-prop-int-compactness-direct-sums` (1)), see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic`. The
  commutation with direct sums on `Loc(Dᵇc)` follows by dévissage and left completeness
  (`ProperLowerStarHeartHypotheses.preservesColimitsOfShape`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Blueprint `sk-def-localizing-closure`: the localizing closure `Loc(Dᵇc(X)⟦Λ⟧)`, the smallest
triangulated subcategory of `D(X_proét, Λ_X)` closed under isomorphisms and direct sums which
contains the bounded constructible complexes. For the `ℓ`-adic coefficient rings these are the
blueprint's `Dctf(X, Λ)`. -/
noncomputable abbrev localizingBoundedConstructible (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (boundedConstructible (condensedRingObj Λ X)).localizingClosure

/-- The category `Loc(Dᵇc(X)⟦Λ⟧)`, a full subcategory of `D(X_proét, Λ_X)`. It is
pretriangulated and has direct sums. -/
abbrev LocalizingBoundedConstructible (X : Scheme.{u}) : Type _ :=
  (localizingBoundedConstructible Λ X).FullSubcategory

/-- The derived category `D(X_proét, Λ_X)` of module objects has direct sums. -/
instance hasCoproducts_derivedCategory (X : Scheme.{u}) :
    HasCoproducts.{u + 1} (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) := by
  intro J
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  exact DerivedCategory.hasColimitsOfShape_discrete J

section General

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The properties of the compact-support direct image `Rf_!(c)⟦Λ⟧ = Rp_* ∘ j_!` along a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of blueprint `det-sf-comp-coherence-single`: it maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)` and `Dᵇc(X)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`, and its restriction
to `Loc(Dᵇc(X)⟦Λ⟧)` preserves direct sums. -/
def LowerShriekLocalizingHypotheses : Prop :=
  (∀ K, localizingBoundedConstructible Λ X K →
    localizingBoundedConstructible Λ Y ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  (∀ K, boundedConstructible (condensedRingObj Λ X) K →
    boundedConstructible (condensedRingObj Λ Y)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)

variable {Λ c} (hc : LowerShriekLocalizingHypotheses Λ c)

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` attached to a
compactification `c` of `f`: the restriction of `Rf_!(c)⟦Λ⟧`. -/
noncomputable abbrev rightDerivedLowerShriekLocalizing :
    LocalizingBoundedConstructible Λ X ⥤ LocalizingBoundedConstructible Λ Y :=
  ObjectProperty.localizingClosureLift _ _ (rightDerivedLowerShriekOfCompactification Λ c) hc.1

/-- `Rf_!` on the localizing closures preserves direct sums (blueprint
`det-sf-comp-coherence-single`). -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing hc) :=
  have := hc.2.2 J
  ObjectProperty.preservesColimitsOfShape_localizingClosureLift _ _ _ _ J

omit [IsCommMonObj Λ] in
/-- Blueprint `sk-prop-sf-existence`, uniformly in the coefficient ring `Λ`: if
`Dᵇc(X)⟦Λ⟧` and `Dᵇc(Y)⟦Λ⟧` compactly generate their localizing closures (blueprint
`sk-lem-brown-hypotheses`) and `Rf_!(c)⟦Λ⟧` has the properties of blueprint
`det-sf-comp-coherence-single`, then the coproduct-preserving functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` has a right adjoint `f^!`, which commutes with shifts
compatibly with the adjunction, is exact (triangulated), preserves direct sums and is unique up
to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing
    (hX : (boundedConstructible (condensedRingObj Λ X)).CompactlyGeneratesLocalizingClosure)
    (hY : (boundedConstructible (condensedRingObj Λ Y)).CompactlyGeneratesLocalizingClosure) :
    ∃ (G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
      (adj : rightDerivedLowerShriekLocalizing hc ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
        (adj' : rightDerivedLowerShriekLocalizing hc ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing hc).map (e.hom.app N) ≫
          adj'.counit.app N = adj.counit.app N :=
  have := hc.2.2
  ObjectProperty.exists_rightAdjoint_localizingClosureLift _ _ _ _ hX hY hc.2.1

end General

/-! ### Reduction to the coefficient-specific inputs -/

section Reduction

/-- The bounded constructible complexes are stable under shifts: `Hᵃ(K⟦n⟧) ≅ Hⁿ⁺ᵃ(K)`. -/
instance isStableUnderShift_boundedConstructible (X : Scheme.{u}) :
    (boundedConstructible (condensedRingObj Λ X)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ ⟨DerivedCategory.TStructure.t.bounded.le_shift n K hK.1,
    fun a ↦ IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso n a (n + a) rfl).app K).symm (hK.2 (n + a))⟩⟩

/-- Constructibility of module objects is invariant under isomorphisms. -/
instance isClosedUnderIsomorphisms_isConstructibleModuleObject (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ X)) where
  of_iso e h := IsConstructibleModuleObject.of_iso e h

/-- Blueprint `det-brown-hypotheses-small` (constructible hearts): the constructible module
objects on a noetherian scheme are essentially small. A constructible sheaf embeds into a finite
product of pushforwards of pullbacks of finitely presented module objects, which form a set
(`essentiallySmall_isConstructibleModuleObject_of_noetherianSpace`). -/
theorem essentiallySmall_isConstructibleModuleObject (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstructibleModuleObject (condensedRingObj Λ X)) :=
  essentiallySmall_isConstructibleModuleObject_of_noetherianSpace Λ X

/-- Blueprint `det-brown-hypotheses-small`: the bounded constructible complexes on a noetherian
scheme are essentially small: a bounded complex with constructible cohomology is obtained from
its shifted cohomology sheaves by finitely many extensions
(`DerivedCategory.essentiallySmall_bounded_inf`), and the constructible sheaves are essentially
small (`essentiallySmall_isConstructibleModuleObject`). -/
theorem exists_skeleton_boundedConstructible (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ∃ (ι : Type (u + 1)) (S : ι → DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj Λ X))), (∀ i, boundedConstructible _ (S i)) ∧
      ∀ K, boundedConstructible (condensedRingObj Λ X) K → ∃ i, Nonempty (S i ≅ K) := by
  have := essentiallySmall_isConstructibleModuleObject Λ X
  have : ObjectProperty.EssentiallySmall.{u + 1} (boundedConstructible (condensedRingObj Λ X)) :=
    DerivedCategory.essentiallySmall_bounded_inf _
  obtain ⟨Q, _, hQ, hle⟩ := ObjectProperty.EssentiallySmall.exists_small_le
    (boundedConstructible (condensedRingObj Λ X))
  refine ⟨Shrink.{u + 1} (Subtype Q), fun i ↦ ((equivShrink _).symm i).1,
    fun i ↦ hQ _ ((equivShrink _).symm i).2, fun K hK ↦ ?_⟩
  obtain ⟨K', hK', ⟨e⟩⟩ := hle K hK
  exact ⟨equivShrink _ ⟨K', hK'⟩, ⟨by simpa using e.symm⟩⟩

/-- The formal part of blueprint `sk-lem-brown-hypotheses`: on a noetherian scheme `X`,
`Loc(Dᵇc(X)⟦Λ⟧)` is idempotent complete (`det-brown-hypotheses-ambient`), and if the bounded
constructible complexes are compact in it, they compactly generate it
(`det-brown-hypotheses-generation`). -/
theorem compactlyGenerates_of_isCompactObj (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (h : ∀ K : LocalizingBoundedConstructible Λ X,
      boundedConstructible (condensedRingObj Λ X) K.obj → BrownRepresentability.IsCompactObj K) :
    (boundedConstructible (condensedRingObj Λ X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible Λ X) :=
  ⟨.of_isStableUnderShift (exists_skeleton_boundedConstructible Λ X) h,
    ObjectProperty.isIdempotentComplete_localizingClosure _⟩

omit [IsCommMonObj Λ] in
/-- The shifted constructible sheaves `M[-n]` are bounded constructible complexes. -/
lemma boundedConstructible_singleFunctor_obj (X : Scheme.{u}) (n : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ n).obj M) := by
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i ↦ ?_⟩
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ n i hi)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ n i hi)

/-- A constructible sheaf `M`, placed in degree `0`, as an object of `Loc(Dᵇc(X)⟦Λ⟧)`. -/
noncomputable abbrev singleLocalizingBoundedConstructible (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    LocalizingBoundedConstructible Λ X :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj M, ObjectProperty.le_localizingClosure _ _
    (boundedConstructible_singleFunctor_obj Λ X 0 M hM)⟩

omit [IsCommMonObj Λ] in
/-- Blueprint `det-constructible-compactness-devissage`: if the constructible sheaves are compact
objects of `Loc(Dᵇc(X)⟦Λ⟧)`, then so are all bounded constructible complexes. Compact objects
are stable under shifts and extensions, and a bounded constructible complex is an iterated
extension of shifted constructible sheaves
(`DerivedCategory.exists_iteratedExtensions_of_bounded`). -/
theorem isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible (X : Scheme.{u})
    (h : ∀ M hM, BrownRepresentability.IsCompactObj (singleLocalizingBoundedConstructible Λ X M hM))
    (K : LocalizingBoundedConstructible Λ X)
    (hK : boundedConstructible (condensedRingObj Λ X) K.obj) :
    BrownRepresentability.IsCompactObj K := by
  let P := IsConstructibleModuleObject (condensedRingObj Λ X)
  have hle : DerivedCategory.singleObjects P ≤ localizingBoundedConstructible Λ X := by
    rintro L ⟨n, M, hM, ⟨e⟩⟩
    exact ObjectProperty.le_localizingClosure _ _ (ObjectProperty.prop_of_iso _ e.symm
      (boundedConstructible_singleFunctor_obj Λ X n M hM))
  have hsingle (L : LocalizingBoundedConstructible Λ X)
      (hL : DerivedCategory.singleObjects P L.obj) :
      BrownRepresentability.IsCompactObj L := by
    obtain ⟨n, M, hM, ⟨e⟩⟩ := hL
    let S := singleLocalizingBoundedConstructible Λ X M hM
    exact ((h M hM).shift (-n)).of_iso
      ((localizingBoundedConstructible Λ X).fullyFaithfulι.preimageIso
      (e ≪≫ (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by simp)).app M).symm ≪≫
        (((localizingBoundedConstructible Λ X).ι.commShiftIso (-n)).app S).symm))
  obtain ⟨d, hd⟩ := DerivedCategory.exists_iteratedExtensions_of_bounded P K.obj hK.1 hK.2
  clear hK
  induction d generalizing K with
  | zero => exact hsingle K hd
  | succ d ih =>
    obtain ⟨Y, Z, f, g, k, hT, hY, hZ⟩ := hd
    have hY' := DerivedCategory.iteratedExtensions_le P hle d Y hY
    exact ObjectProperty.FullSubcategory.isCompactObj_of_distTriang _ (Y := ⟨Y, hY'⟩)
      (Z := ⟨Z, hle Z hZ⟩) f g k hT (ih ⟨Y, hY'⟩ hY) (hsingle ⟨Z, hle Z hZ⟩ hZ)

/-- Blueprint `sk-prop-proper-image-localizing` (extension by zero): for an open immersion
`j : U ⟶ X` into a noetherian scheme, `j_!` maps `Dᵇc(U)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`: `j_!` is exact,
so `Hⁿ(j_! K) ≅ j_! Hⁿ(K)`. -/
theorem boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : boundedConstructible (condensedRingObj Λ U) K) :
    boundedConstructible (condensedRingObj Λ X) ((D((j)_!open⟦Λ⟧)).obj K) := by
  let e (n : ℤ) := ((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app K
  obtain ⟨⟨a, b, hab⟩, hK⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (Functor.map_isZero (j)_!open⟦Λ⟧ (hab i hi)).of_iso (e i).symm
  · exact IsConstructibleModuleObject.of_iso (e n)
      (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ j _ (hK n))

/-- The properties of the derived direct image `Rp_*` along a proper morphism `p` used in
blueprint `det-sf-comp-coherence-single`: it maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` (blueprint
`sk-thm-sfb-proper-base-change`) and its restriction to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums
(blueprint `sk-prop-proper-image-localizing`). -/
def ProperLowerStarHypotheses {Z Y : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  (∀ K, boundedConstructible (condensedRingObj Λ Z) K →
    boundedConstructible (condensedRingObj Λ Y) ((R((p)_*⟦Λ⟧)).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ Z).ι ⋙ R((p)_*⟦Λ⟧))

/-- The extension by zero `j_!` along an open immersion preserves direct sums. -/
instance preservesColimitsOfShape_mapDerivedCategory_openImmersionLowerShriek {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) D((j)_!open⟦Λ⟧) := by
  have (T : Scheme.{u}) : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (j)_!open⟦Λ⟧ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).leftAdjoint_preservesColimits
  exact Functor.preservesColimitsOfShape_mapDerivedCategory _ J

/-- Blueprint `sk-prop-proper-image-localizing` (extension by zero, formal part): for an open
immersion `j : U ⟶ X` into a noetherian scheme, `j_!` maps `Loc(Dᵇc(U)⟦Λ⟧)` into
`Loc(Dᵇc(X)⟦Λ⟧)`. -/
theorem localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : localizingBoundedConstructible Λ U K) :
    localizingBoundedConstructible Λ X ((D((j)_!open⟦Λ⟧)).obj K) :=
  ObjectProperty.localizingClosure_obj_of_le _ _ _ (fun K hK ↦ ObjectProperty.le_localizingClosure
    _ _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ j K hK)) K hK

/-- Blueprint `det-sf-comp-coherence-single`, reduced to its inputs: for a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` with `X̄` noetherian, if `Rp_*` has the properties
`ProperLowerStarHypotheses`, then `Rf_!(c) = Rp_* ∘ j_!` has the properties
`LowerShriekLocalizingHypotheses`: each factor maps `Dᵇc` into `Dᵇc` and its restriction to the
localizing closures preserves direct sums, hence so does the composite, which therefore maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`. -/
theorem lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) [TopologicalSpace.NoetherianSpace c.Z]
    (hp : ProperLowerStarHypotheses Λ c.g) : LowerShriekLocalizingHypotheses Λ c := by
  have h₂ (K) (hK : boundedConstructible (condensedRingObj Λ X) K) :
      boundedConstructible (condensedRingObj Λ Y)
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K) :=
    hp.1 _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ c.i K hK)
  have h₃ (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J)
      ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c) := by
    have := hp.2 J
    let L := ObjectProperty.localizingClosureLift _ _ D((c.i)_!open⟦Λ⟧)
      (localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ c.i)
    exact preservesColimitsOfShape_of_natIso
      (F := L ⋙ (localizingBoundedConstructible Λ c.Z).ι ⋙ R((c.g)_*⟦Λ⟧))
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (ObjectProperty.localizingClosureLiftCompιIso _ _ _ _) _ ≪≫ Functor.associator _ _ _)
  exact ⟨ObjectProperty.localizingClosure_obj_of_le _ _ _
    (fun K hK ↦ ObjectProperty.le_localizingClosure _ _ (h₂ K hK)), h₂, h₃⟩

end Reduction

/-! ### The `ℓ`-adic coefficient rings -/

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! #### The coefficient ring `E` -/

/-- Blueprint `sk-thm-constructible-compactness` (`det-constructible-compactness-sheaf`): for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`,
the constructible sheaves are compact objects of `Loc(Dᵇc(X)⟦E⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X M hM) :=
  isCompactObj_singleFunctor_continuousMapRingObj ℓ E aX hk M hM _

/-- Blueprint `sk-thm-constructible-compactness`: for the coefficient ring `E` of a finite
extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, the bounded constructible
complexes are compact objects of `Loc(Dᵇc(X)⟦E⟧)`, by dévissage to constructible sheaves. -/
theorem isCompactObj_boundedConstructible_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj ℓ E aX hk) K hK

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `E = ℚ_ℓ`) and a separated
finite-type `k`-scheme `X`. The category `Loc(Dᵇc(X)⟦E⟧)` is locally small, triangulated and has
direct sums (by construction); it has split idempotents, and `Dᵇc(X)⟦E⟧ = Dctf(X, E)` is
essentially small, with a small skeleton forming a set of compact generators. -/
theorem compactlyGenerates_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.continuousMapRingObj E) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_continuousMapRingObj ℓ E aX hk)

/-- Blueprints `sk-thm-sfb-proper-base-change` and `sk-prop-proper-image-localizing`: for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a
noetherian `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦E⟧` into `Dᵇc(Y)⟦E⟧` and preserves direct sums on
`Loc(Dᵇc(Z)⟦E⟧)`. -/
theorem properLowerStarHypotheses_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.continuousMapRingObj.{u} E) p :=
  ⟨boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj ℓ E aY p,
    (properLowerStarHeartHypotheses_continuousMapRingObj ℓ E aY p).preservesColimitsOfShape⟩

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a
noetherian `k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!`
maps `Loc(Dctf(X, E))` into `Loc(Dctf(Y, E))` and `Dctf(X, E)` into `Dctf(Y, E)`, and preserves
direct sums on `Loc(Dctf(X, E))`. -/
theorem lowerShriek_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.continuousMapRingObj.{u} E) c :=
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_continuousMapRingObj ℓ E aY c.g)

/-- `lowerShriek_continuousMapRingObj` for a separated finite-type `k`-scheme `Y`, which is
noetherian. -/
theorem lowerShriek_continuousMapRingObj_of_finiteType (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.continuousMapRingObj.{u} E) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  lowerShriek_continuousMapRingObj ℓ E aY c

/-! #### The coefficient ring `𝒪_E` -/

/-- Blueprint `sk-prop-int-compactness` (compactness of constructible sheaves): for the
coefficient ring `𝒪_E` of the ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a
separated finite-type `k`-scheme `X`, the constructible sheaves are compact objects of
`Loc(Dᵇc(X)⟦𝒪_E⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X M hM) :=
  isCompactObj_singleFunctor_padicIntegersRingObj ℓ E aX hk M hM _

/-- Blueprint `sk-prop-int-compactness`: for the coefficient ring `𝒪_E` of the ring of integers
of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, the bounded
constructible complexes are compact objects of `Loc(Dᵇc(X)⟦𝒪_E⟧)`, by dévissage to constructible
sheaves. -/
theorem isCompactObj_boundedConstructible_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj ℓ E aX hk) K hK

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `𝒪_E` of the ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(including `ℤ_ℓ`, for `E = ℚ_ℓ`) and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦𝒪_E⟧)`
has split idempotents, and `Dᵇc(X)⟦𝒪_E⟧ = Dctf(X, 𝒪_E)` is essentially small, with a small
skeleton forming a set of compact generators. -/
theorem compactlyGenerates_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete
        (LocalizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_padicIntegersRingObj ℓ E aX hk)

/-- Blueprints `sk-thm-sfb-proper-base-change` and `sk-prop-int-compactness` (direct sums): for
the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism
`p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧` and
preserves direct sums on `Loc(Dᵇc(Z)⟦𝒪_E⟧)`. -/
theorem properLowerStarHypotheses_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) p :=
  ⟨boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj ℓ E aY p,
    (properLowerStarHeartHypotheses_padicIntegersRingObj ℓ E aY p).preservesColimitsOfShape⟩

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
and a noetherian `k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`,
`Rp_* ∘ j_!` maps `Loc(Dctf(X, 𝒪_E))` into `Loc(Dctf(Y, 𝒪_E))` and `Dctf(X, 𝒪_E)` into
`Dctf(Y, 𝒪_E)`, and preserves direct sums on `Loc(Dctf(X, 𝒪_E))`. -/
theorem lowerShriek_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) c :=
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_padicIntegersRingObj ℓ E aY c.g)

/-- `lowerShriek_padicIntegersRingObj` for a separated finite-type `k`-scheme `Y`, which is
noetherian. -/
theorem lowerShriek_padicIntegersRingObj_of_finiteType (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  lowerShriek_padicIntegersRingObj ℓ E aY c

/-! #### The coefficient ring `ℚ̄_ℓ` -/

/-- Blueprint `sk-thm-constructible-compactness` (`det-constructible-compactness-sheaf`): for the
coefficient ring `ℚ̄_ℓ` and a separated finite-type `k`-scheme `X`, the constructible sheaves are
compact objects of `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X M hM) :=
  isCompactObj_singleFunctor_padicAlgClRingObj ℓ aX hk M hM _

/-- Blueprint `sk-thm-constructible-compactness`: for the coefficient ring `ℚ̄_ℓ` and a separated
finite-type `k`-scheme `X`, the bounded constructible complexes are compact objects of
`Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)`, by dévissage to constructible sheaves. -/
theorem isCompactObj_boundedConstructible_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj ℓ aX hk) K hK

/-- Blueprint `sk-lem-brown-hypotheses`: Hypotheses of Brown representability, for the
coefficient ring `ℚ̄_ℓ` and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)` has split
idempotents, and `Dᵇc(X)⟦ℚ̄_ℓ⟧ = Dctf(X, ℚ̄_ℓ)` is essentially small, with a small skeleton
forming a set of compact generators. -/
theorem compactlyGenerates_padicAlgClRingObj {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_padicAlgClRingObj ℓ aX hk)

/-- Blueprints `sk-thm-sfb-proper-base-change` and `sk-prop-proper-image-localizing`: for the
coefficient ring `ℚ̄_ℓ` and a proper morphism `p : Z ⟶ Y` to a noetherian `k`-scheme, `Rp_*` maps
`Dᵇc(Z)⟦ℚ̄_ℓ⟧` into `Dᵇc(Y)⟦ℚ̄_ℓ⟧` and preserves direct sums on `Loc(Dᵇc(Z)⟦ℚ̄_ℓ⟧)`. -/
theorem properLowerStarHypotheses_padicAlgClRingObj {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) p :=
  ⟨boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj ℓ aY p,
    (properLowerStarHeartHypotheses_padicAlgClRingObj ℓ aY p).preservesColimitsOfShape⟩

/-- Blueprint `det-sf-comp-coherence-single`: Compact support along one compactification on the
localizing category, for the coefficient ring `ℚ̄_ℓ` and a noetherian `k`-scheme `Y`: for a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!` maps `Loc(Dctf(X, ℚ̄_ℓ))` into
`Loc(Dctf(Y, ℚ̄_ℓ))` and `Dctf(X, ℚ̄_ℓ)` into `Dctf(Y, ℚ̄_ℓ)`, and preserves direct sums on
`Loc(Dctf(X, ℚ̄_ℓ))`. -/
theorem lowerShriek_padicAlgClRingObj {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsNoetherian Y] {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) c :=
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_padicAlgClRingObj ℓ aY c.g)

/-- `lowerShriek_padicAlgClRingObj` for a separated finite-type `k`-scheme `Y`, which is
noetherian. -/
theorem lowerShriek_padicAlgClRingObj_of_finiteType {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  lowerShriek_padicAlgClRingObj ℓ aY c

variable {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)
  (hk : Finite k ∨ IsSepClosed k)

include aX hk in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `ℚ_ℓ`) and separated
finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, E)) ⥤ Loc(Dctf(Y, E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
        LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
          LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj_of_finiteType ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_continuousMapRingObj ℓ E aX hk).1
    (compactlyGenerates_continuousMapRingObj ℓ E aY hk).1

include aX hk in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (including `ℤ_ℓ`) and
separated finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, 𝒪_E)) ⥤ Loc(Dctf(Y, 𝒪_E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj_of_finiteType ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicIntegersRingObj ℓ E aX hk).1
    (compactlyGenerates_padicIntegersRingObj ℓ E aY hk).1

include aX hk in
/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional inverse image, for the
coefficient ring `ℚ̄_ℓ` and separated finite-type `k`-schemes `X`, `Y`. For a compactification
`c` of `f : X ⟶ Y`, the coproduct-preserving functor
`Rf_! : Loc(Dctf(X, ℚ̄_ℓ)) ⥤ Loc(Dctf(Y, ℚ̄_ℓ))` has a right adjoint `f^!`, which commutes with
shifts compatibly with the adjunction, is exact (triangulated), preserves direct sums and is
unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj_of_finiteType ℓ aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicAlgClRingObj ℓ aX hk).1
    (compactlyGenerates_padicAlgClRingObj ℓ aY hk).1

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
