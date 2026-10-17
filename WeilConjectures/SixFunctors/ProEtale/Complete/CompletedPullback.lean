/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The completed pullback on the pro-étale site

Let `Λ` be a commutative ring, `I` an ideal of `Λ` and `g : X ⟶ Y` a morphism of schemes. For
`K` in `D(Y_proét, Λ)` the *completed pullback* is the homotopy limit of the reductions of the
derived pullback,
```
Lg^*_comp K = R lim_n (Lg^* K ⊗ᴸ Λ/Iⁿ)
```
in `D(X_proét, Λ)` (blueprint `def-weil-pbc-completed-pullback`). The homotopy limit exists
because countable products of pro-étale sheaves are exact (`Scheme.ProEt.countableAB4Star`), so
that `D(X_proét, Λ)` has countable products (`derivedCategory_hasCountableProducts`); it is the
chosen homotopy limit `CategoryTheory.Pretriangulated.homotopyLimitCone` of the tower
`DerivedCategory.derivedCompletionDiagram` of reductions, and is therefore only well defined up
to non-unique isomorphism, and only on objects.

## Main definitions

- `AlgebraicGeometry.ProEtale.completedPullbackCone`: the homotopy limit cone of the reductions
  `Lg^* K ⊗ᴸ Λ/Iⁿ`.
- `AlgebraicGeometry.ProEtale.completedPullback`: its point `Lg^*_comp K`.

## Main statements

- `AlgebraicGeometry.ProEtale.isHomotopyLimit_completedPullbackCone`: `Lg^*_comp K` is the
  homotopy limit of the reductions of `Lg^* K`.
- `AlgebraicGeometry.ProEtale.exists_iso_completedPullback`: for `Lg^* K` derived complete (for
  instance `g = 𝟙`, `K` derived complete), `Lg^*_comp K ≅ Lg^* K` compatibly with the reduction
  maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section DerivedCompletion

open MonoidalCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)
  [HasCountableProducts (_root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))]

noncomputable local instance (priority := high) completedPullbackMonoidalCategory :
    MonoidalCategory (_root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (_root_.DerivedCategory.sheafTensorStructure J R).monoidalCategory

/-- A chosen homotopy limit cone `R lim_n (K ⊗ᴸ R/Iⁿ)` over the tower of reductions
`DerivedCategory.derivedCompletionDiagram` of an object `K` of `D(J, R)`. -/
noncomputable def _root_.DerivedCategory.derivedCompletionLimitCone
    (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    Cone (_root_.DerivedCategory.derivedCompletionDiagram J I K) :=
  homotopyLimitCone _

lemma _root_.DerivedCategory.isHomotopyLimit_derivedCompletionLimitCone
    (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    IsHomotopyLimit (_root_.DerivedCategory.derivedCompletionLimitCone J I K) :=
  isHomotopyLimit_homotopyLimitCone _


/-- The derived completion `K^∧ = R lim_n (K ⊗ᴸ R/Iⁿ)` of an object `K` of `D(J, R)`: the
point of the chosen homotopy limit `DerivedCategory.derivedCompletionLimitCone`. It is only
determined up to non-unique isomorphism. -/
noncomputable def _root_.DerivedCategory.derivedCompletion
    (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (_root_.DerivedCategory.derivedCompletionLimitCone J I K).pt

/-- The morphism `K ⊗ᴸ R/Iⁿ ⟶ K' ⊗ᴸ R/Iⁿ` of towers of reductions induced by `f : K ⟶ K'`. -/
noncomputable def _root_.DerivedCategory.derivedCompletionDiagramMap
    {K K' : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : K ⟶ K') :
    _root_.DerivedCategory.derivedCompletionDiagram J I K ⟶
      _root_.DerivedCategory.derivedCompletionDiagram J I K' :=
  { app n := f ▷ (_root_.DerivedCategory.quotPowFunctor J I).obj n
    naturality _ _ φ := whisker_exchange f _ }

instance _root_.DerivedCategory.isIso_derivedCompletionDiagramMap_app
    {K K' : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : K ⟶ K') [IsIso f]
    (n : ℕᵒᵖ) : IsIso ((_root_.DerivedCategory.derivedCompletionDiagramMap J I f).app n) :=
  inferInstanceAs (IsIso (f ▷ (_root_.DerivedCategory.quotPowFunctor J I).obj n))

lemma _root_.DerivedCategory.derivedCompletionDiagramMap_comp
    {K K' K'' : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : K ⟶ K')
    (f' : K' ⟶ K'') :
    _root_.DerivedCategory.derivedCompletionDiagramMap J I (f ≫ f') =
      _root_.DerivedCategory.derivedCompletionDiagramMap J I f ≫
        _root_.DerivedCategory.derivedCompletionDiagramMap J I f' := by
  ext n
  rw [NatTrans.comp_app]
  exact comp_whiskerRight f f' _

/-- The map `K^∧ ⟶ K'^∧` of chosen derived completions induced by `f : K ⟶ K'`
(`CategoryTheory.Pretriangulated.homotopyLimitMap`); it is a choice, and an isomorphism when
`f` is. -/
noncomputable def _root_.DerivedCategory.derivedCompletionMap
    {K K' : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))} (f : K ⟶ K') :
    _root_.DerivedCategory.derivedCompletion J I K ⟶
      _root_.DerivedCategory.derivedCompletion J I K' :=
  homotopyLimitMap (_root_.DerivedCategory.derivedCompletionDiagramMap J I f)

/-- The completion map `K ⟶ K^∧`, a lift of the reduction maps `K ⟶ K ⊗ᴸ R/Iⁿ` to the chosen
homotopy limit (`CategoryTheory.Pretriangulated.homotopyLimitLift`); it is a choice. -/
noncomputable def _root_.DerivedCategory.derivedCompletionUnit
    (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    K ⟶ _root_.DerivedCategory.derivedCompletion J I K :=
  homotopyLimitLift _ (_root_.DerivedCategory.derivedCompletionCone J I K)

end DerivedCompletion

variable {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]

instance hasCountableProducts_derivedCategory :
    HasCountableProducts
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  derivedCategory_hasCountableProducts _

variable {Λ} (I : Ideal Λ) (g : X ⟶ Y)

/-- The homotopy limit cone `R lim_n (Lg^* K ⊗ᴸ Λ/Iⁿ)` over the tower of reductions of the
derived pullback `Lg^* K` (`DerivedCategory.derivedCompletionDiagram`), a choice of homotopy
limit (`CategoryTheory.Pretriangulated.homotopyLimitCone`). -/
noncomputable def completedPullbackCone
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    Cone (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology X) I
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  _root_.DerivedCategory.derivedCompletionLimitCone _ I _

/-- Blueprint `def-weil-pbc-completed-pullback`: Completed pullback.

For `g : X ⟶ Y`, an ideal `I` of the coefficient ring `Λ` and `K` in `D(Y_proét, Λ)`, the
completed pullback
```
Lg^*_comp K = R lim_n (Lg^* K ⊗ᴸ Λ/Iⁿ)
```
in `D(X_proét, Λ)`: the homotopy limit of the reductions of the derived pullback `Lg^* K`
(`AlgebraicGeometry.ProEtale.completedPullbackCone`). The `n`-th reduction `Lg^* K ⊗ᴸ Λ/Iⁿ` is
the derived pullback `Lg_n^* K_n` of the reduction `K_n = K ⊗ᴸ Λ/Iⁿ`. The homotopy limit is a
chosen one: it is only determined up to non-unique isomorphism, and its formation is not made
functorial in `K`. -/
noncomputable def completedPullback
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  (completedPullbackCone I g K).pt

lemma completedPullbackCone_pt
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (completedPullbackCone I g K).pt = completedPullback I g K :=
  rfl

/-- The completed pullback `Lg^*_comp K` is the homotopy limit of the reductions
`Lg^* K ⊗ᴸ Λ/Iⁿ`. -/
lemma isHomotopyLimit_completedPullbackCone
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    IsHomotopyLimit (completedPullbackCone I g K) :=
  _root_.DerivedCategory.isHomotopyLimit_derivedCompletionLimitCone _ I _

/-- If the derived pullback `Lg^* K` is derived complete, the completed pullback is `Lg^* K`
itself: there is an isomorphism `Lg^* K ≅ Lg^*_comp K` carrying the reduction maps
`Lg^* K ⟶ Lg^* K ⊗ᴸ Λ/Iⁿ` to the legs of the homotopy limit. -/
lemma exists_iso_completedPullback
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hK : _root_.DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    ∃ e : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ≅ completedPullback I g K,
      ∀ n : ℕ, e.hom ≫ (completedPullbackCone I g K).π.app (op n) =
        (_root_.DerivedCategory.derivedCompletionCone (Scheme.ProEt.topology X) I
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)).π.app (op n) :=
  (_root_.DerivedCategory.derivedComplete_iff_exists_iso _
    (isHomotopyLimit_completedPullbackCone I g K)).1 hK

end AlgebraicGeometry.ProEtale
