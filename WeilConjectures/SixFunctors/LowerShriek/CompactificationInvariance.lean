/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.Category
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Invariance of the lower shriek under the choice of compactification

For a morphism `f : X ⟶ Y` admitting a compactification, the lower shriek
`Etale.lowerShriek A f` is defined via a *chosen* compactification
`HasCompactification.compactification f`. This file sets up the comparison system making
`f_!` independent of that choice, in the following precise sense.

For every compactification `c` of `f` there is the functor

`Etale.lowerShriekAt A c := (c.i)_! ⋙ (c.g)_* : Sheaf X_ét ⥤ Sheaf Y_ét`,

and for every morphism of compactifications `u : c' ⟶ c` a *specified* transition
morphism

`Etale.lowerShriekTransition A u : Etale.lowerShriekAt A c ⟶ Etale.lowerShriekAt A c'`,

natural in nothing less than a functor: the transitions assemble into the
**compactification diagram**

`Etale.lowerShriekDiagram A f : (Compactification f)ᵒᵖ ⥤ (Sheaf X_ét ⥤ Sheaf Y_ét)`.

(The diagram is indexed by the opposite category because our transition morphism goes
from the coarser to the finer compactification; this is a pure convention with no
mathematical content.)

Each transition morphism is an isomorphism
(`Etale.isIso_lowerShriekTransition`, currently `sorry`ed), and the index category
`(Compactification f)ᵒᵖ` is filtered (`WeilConjectures.Compactification.Category`). A
functor from a filtered category inverting every morphism admits a *canonical* system of
comparison isomorphisms between the values at any two objects, characterized by
compatibility with the transition morphisms and satisfying the cocycle identities; this
elementary categorical fact is proved in the first section of this file
(`CategoryTheory.Functor.filteredComparisonIso`). Note that mere connectedness would give
*some* isomorphism between any two values; filteredness is what makes the comparison
*canonical*, i.e. independent of the chosen zigzag.

Applying it to the compactification diagram yields the canonical comparison

`Etale.lowerShriekCompactificationIso A c d : Etale.lowerShriekAt A c ≅ Etale.lowerShriekAt A d`

satisfying `κ c c = Iso.refl` and `κ c d ≪≫ κ d e = κ c e`, and agreeing with the
transition morphisms along refinements. Since `Etale.lowerShriek A f` is *definitionally*
`Etale.lowerShriekAt A (HasCompactification.compactification f)`, this specializes to

`Etale.lowerShriekIsoLowerShriekAt A f c : Etale.lowerShriek A f ≅ Etale.lowerShriekAt A c`,

the invariance of `f_!` under the choice of compactification. Later constructions (the
lower-shriek base-change isomorphism, and the Weil structure on `Rf_! K`) must use this
specified comparison system rather than the bare existence of an isomorphism.

## Construction of the transition morphism

For `u : c' ⟶ c` the transition morphism is assembled from two mates:

- `Etale.compactificationRestrictionComparison A u : u_* ⋙ (c.i)^* ⟶ (c'.i)^*` is the
  mate of the composition isomorphism `(c'.i)_* ⋙ u_* ≅ (c.i)_*` under the adjunctions
  `(c.i)^* ⊣ (c.i)_*` and `(c'.i)^* ⊣ (c'.i)_*`. It is an isomorphism
  (`Etale.isIso_compactificationRestrictionComparison`, currently `sorry`ed) precisely
  because the square of `u` is **Cartesian**: for `T` étale over `X`, the base change
  `T ×_{c.Z} c'.Z` is canonically `T` again.
- `Etale.compactificationShriekComparison A u : (c.i)_! ⟶ (c'.i)_! ⋙ u_*` is the mate of
  the *inverse* of the previous comparison under the adjunctions `(c.i)_! ⊣ (c.i)^*` and
  `(c'.i)_! ⊣ (c'.i)^*`. This is the ordinary-category avatar of the canonical
  isomorphism `u_* (c'.i)_! ≅ (c.i)_!` of the reference.

Whiskering with `(c.g)_*` and composing with the composition isomorphism
`u_* ⋙ (c.g)_* ≅ (c'.g)_*` gives the transition morphism.

## Remaining `sorry`s

- `Etale.isIso_compactificationRestrictionComparison`: the geometric input from the
  Cartesian square, see its docstring.
- `Etale.isIso_lowerShriekTransition`: the transition morphisms are isomorphisms; this is
  the underived avatar of `Ru_* j_{c'!} ≅ j_{c!}` and rests on `u` being proper with
  `u⁻¹(X) = X`.
- `Etale.lowerShriekTransition_id` and `Etale.lowerShriekTransition_comp`: the coherence
  of the transitions (functoriality of the compactification diagram); pure mate-calculus
  diagram chases.
- the cofilteredness inputs of `WeilConjectures.Compactification.Category`.

-/

@[expose] public section

universe w v' u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

/-!
### Canonical comparison isomorphisms for a functor inverting a filtered category

This is Lemma 1 of the reference (stated there for a cofiltered index category; we use
the filtered formulation, which is what applies to `(Compactification f)ᵒᵖ`): a functor
`F` from a filtered category sending every morphism to an isomorphism admits a canonical
isomorphism `F.obj i ≅ F.obj j` for every pair of objects, characterized by compatibility
with the transition morphisms, and these satisfy the cocycle identities.
-/

namespace Functor

variable {J : Type*} [Category J] {C : Type*} [Category C]
variable (F : J ⥤ C) [∀ (i j : J) (φ : i ⟶ j), IsIso (F.map φ)]

/-- Extending a cospan `i ⟶ k ⟵ j` along any morphism `k ⟶ m` does not change the
composite `F.map a ≫ inv (F.map b)`. -/
lemma map_comp_inv_map_of_comp {i j k m : J} (a : i ⟶ k) (b : j ⟶ k) (p : k ⟶ m) :
    F.map (a ≫ p) ≫ CategoryTheory.inv (F.map (b ≫ p)) =
      F.map a ≫ CategoryTheory.inv (F.map b) := by
  rw [IsIso.comp_inv_eq]
  simp

variable [IsFiltered J]

/-- The canonical comparison isomorphism `F.obj i ≅ F.obj j` for a functor `F` from a
filtered category sending every morphism to an isomorphism: pass to a common target of
`i` and `j` and compose one leg with the inverse of the other. By
`Functor.filteredComparisonIso_hom_eq` this does not depend on the choice of cospan, and
by `Functor.filteredComparisonIso_trans` the comparisons satisfy the cocycle identity. -/
noncomputable def filteredComparisonIso (i j : J) : F.obj i ≅ F.obj j :=
  asIso (F.map (IsFiltered.leftToMax i j)) ≪≫ (asIso (F.map (IsFiltered.rightToMax i j))).symm

/-- The canonical comparison isomorphism is computed by *any* cospan `i ⟶ k ⟵ j`: this
is the independence of the comparison from all choices, and rests on the filteredness of
the index category (two cospans can be equalized after a further extension). -/
lemma filteredComparisonIso_hom_eq {i j k : J} (a : i ⟶ k) (b : j ⟶ k) :
    (F.filteredComparisonIso i j).hom = F.map a ≫ CategoryTheory.inv (F.map b) := by
  set l := IsFiltered.leftToMax i j
  set r := IsFiltered.rightToMax i j
  -- Extend the two cospans to a common one.
  set p₀ : IsFiltered.max i j ⟶ IsFiltered.max (IsFiltered.max i j) k :=
    IsFiltered.leftToMax (IsFiltered.max i j) k
  set q₀ : k ⟶ IsFiltered.max (IsFiltered.max i j) k :=
    IsFiltered.rightToMax (IsFiltered.max i j) k
  set e₁ := IsFiltered.coeqHom (l ≫ p₀) (a ≫ q₀)
  set e₂ := IsFiltered.coeqHom (r ≫ p₀ ≫ e₁) (b ≫ q₀ ≫ e₁)
  have hleq : l ≫ p₀ ≫ e₁ ≫ e₂ = a ≫ q₀ ≫ e₁ ≫ e₂ := by
    simpa using congrArg (fun t => t ≫ e₂) (IsFiltered.coeq_condition (l ≫ p₀) (a ≫ q₀))
  have hreq : r ≫ p₀ ≫ e₁ ≫ e₂ = b ≫ q₀ ≫ e₁ ≫ e₂ := by
    simpa using IsFiltered.coeq_condition (r ≫ p₀ ≫ e₁) (b ≫ q₀ ≫ e₁)
  calc (F.filteredComparisonIso i j).hom
      = F.map l ≫ CategoryTheory.inv (F.map r) := rfl
    _ = F.map (l ≫ p₀ ≫ e₁ ≫ e₂) ≫ CategoryTheory.inv (F.map (r ≫ p₀ ≫ e₁ ≫ e₂)) :=
        (F.map_comp_inv_map_of_comp l r (p₀ ≫ e₁ ≫ e₂)).symm
    _ = F.map (a ≫ q₀ ≫ e₁ ≫ e₂) ≫ CategoryTheory.inv (F.map (b ≫ q₀ ≫ e₁ ≫ e₂)) := by
        rw [hleq, hreq]
    _ = F.map a ≫ CategoryTheory.inv (F.map b) :=
        F.map_comp_inv_map_of_comp a b (q₀ ≫ e₁ ≫ e₂)

/-- The canonical comparison isomorphism along a morphism `φ : i ⟶ j` is `F.map φ`
itself: the abstract comparison system extends the concrete transition morphisms. -/
lemma filteredComparisonIso_hom_eq_map {i j : J} (φ : i ⟶ j) :
    (F.filteredComparisonIso i j).hom = F.map φ := by
  rw [F.filteredComparisonIso_hom_eq φ (𝟙 j)]
  simp

@[simp]
lemma filteredComparisonIso_refl (i : J) :
    F.filteredComparisonIso i i = Iso.refl (F.obj i) :=
  Iso.ext (by simpa using F.filteredComparisonIso_hom_eq_map (𝟙 i))

/-- The cocycle identity for the canonical comparison isomorphisms. -/
lemma filteredComparisonIso_trans (i j k : J) :
    F.filteredComparisonIso i j ≪≫ F.filteredComparisonIso j k =
      F.filteredComparisonIso i k := by
  apply Iso.ext
  -- A common cospan for the three objects.
  set p₁ : IsFiltered.max i j ⟶ IsFiltered.max (IsFiltered.max i j) (IsFiltered.max j k) :=
    IsFiltered.leftToMax (IsFiltered.max i j) (IsFiltered.max j k)
  set p₂ : IsFiltered.max j k ⟶ IsFiltered.max (IsFiltered.max i j) (IsFiltered.max j k) :=
    IsFiltered.rightToMax (IsFiltered.max i j) (IsFiltered.max j k)
  set e := IsFiltered.coeqHom (IsFiltered.rightToMax i j ≫ p₁) (IsFiltered.leftToMax j k ≫ p₂)
  set ai := IsFiltered.leftToMax i j ≫ p₁ ≫ e
  set aj := IsFiltered.rightToMax i j ≫ p₁ ≫ e with haj'
  set ak := IsFiltered.rightToMax j k ≫ p₂ ≫ e
  have haj : aj = IsFiltered.leftToMax j k ≫ p₂ ≫ e := by
    simpa [haj'] using IsFiltered.coeq_condition (IsFiltered.rightToMax i j ≫ p₁)
      (IsFiltered.leftToMax j k ≫ p₂)
  rw [Iso.trans_hom, F.filteredComparisonIso_hom_eq ai aj,
    F.filteredComparisonIso_hom_eq ai ak,
    F.filteredComparisonIso_hom_eq (IsFiltered.leftToMax j k ≫ p₂ ≫ e) ak, ← haj]
  simp

end Functor

end CategoryTheory

namespace AlgebraicGeometry

open Scheme Compactification

variable (A : Type u') [Category.{v'} A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y}
variable [HasInitial A] [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology A]

/-!
### The compactification diagram

This is the diagram `c ↦ F_c := (c.i)_! ⋙ (c.g)_*` of the reference, together with its
transition morphisms and their (partly `sorry`ed) coherences.
-/

/-- The lower shriek of `f` computed at the compactification `c`: the extension by zero
`(c.i)_!` followed by the pushforward `(c.g)_*`. The lower shriek `Etale.lowerShriek A f`
is definitionally this functor at the chosen compactification, see
`Etale.lowerShriek_eq_lowerShriekAt`. -/
noncomputable def Etale.lowerShriekAt (c : Compactification f) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  Etale.openImmersionLowerShriek A c.i ⋙ Etale.lowerStar A c.g

variable (f) in
/-- The lower shriek of `f` is definitionally the lower shriek computed at the chosen
compactification. -/
lemma Etale.lowerShriek_eq_lowerShriekAt [HasCompactification f] :
    Etale.lowerShriek A f =
      Etale.lowerShriekAt A (HasCompactification.compactification f) :=
  rfl

section Transition

variable {c'' c' c : Compactification f}

/-- The comparison `u_* ⋙ (c.i)^* ⟶ (c'.i)^*` for a morphism of compactifications
`u : c' ⟶ c`: the mate of the composition isomorphism `(c'.i)_* ⋙ u_* ≅ (c.i)_*` under
the adjunctions `(c'.i)^* ⊣ (c'.i)_*` and `(c.i)^* ⊣ (c.i)_*`.

Its component at a sheaf `H` on `c'.Z` and an étale `T ⟶ X` is the map
`H(T ×_{c.Z} c'.Z) ⟶ H(T)` induced by the canonical morphism `T ⟶ T ×_{c.Z} c'.Z`; it
is an isomorphism because the square of `u` is Cartesian, see
`Etale.isIso_compactificationRestrictionComparison`. -/
noncomputable def Etale.compactificationRestrictionComparison (u : c' ⟶ c) :
    Etale.lowerStar A u.hom ⋙ Etale.openImmersionRestriction A c.i ⟶
      Etale.openImmersionRestriction A c'.i :=
  ((mateEquiv (Etale.openImmersionRestrictionLowerStarAdjunction A c'.i)
      (Etale.openImmersionRestrictionLowerStarAdjunction A c.i)).symm
    (TwoSquare.mk _ _ _ _
      ((Etale.lowerStarComp A c'.i u.hom).hom ≫ eqToHom (by rw [u.i_hom]) ≫
        (Functor.leftUnitor _).inv))).natTrans ≫ (Functor.rightUnitor _).hom

/-- The comparison `u_* ⋙ (c.i)^* ⟶ (c'.i)^*` is an isomorphism.

This is where the **Cartesian** condition on morphisms of compactifications enters: for
`T` étale over `X`, viewed in `c.Z` via `c.i`, the base change `T ×_{c.Z} c'.Z` is
canonically isomorphic to `T` because `X` is the preimage of `X` under `u.hom`
(`u.isPullback`), so the component `H(T ×_{c.Z} c'.Z) ⟶ H(T)` of the comparison is the
map induced by an isomorphism of the small étale site of `c'.Z`. -/
theorem Etale.isIso_compactificationRestrictionComparison (u : c' ⟶ c) :
    IsIso (Etale.compactificationRestrictionComparison A u) :=
  sorry

/-- The comparison `(c.i)_! ⟶ (c'.i)_! ⋙ u_*` for a morphism of compactifications
`u : c' ⟶ c`: the mate of the inverse of
`Etale.compactificationRestrictionComparison A u` under the adjunctions
`(c'.i)_! ⊣ (c'.i)^*` and `(c.i)_! ⊣ (c.i)^*`. This is the ordinary-category form of the
canonical isomorphism `u_* j_{c'!} ≅ j_{c!}`; that it is an isomorphism is recorded at
the level of the full transition morphism, `Etale.isIso_lowerShriekTransition`. -/
noncomputable def Etale.compactificationShriekComparison (u : c' ⟶ c) :
    Etale.openImmersionLowerShriek A c.i ⟶
      Etale.openImmersionLowerShriek A c'.i ⋙ Etale.lowerStar A u.hom :=
  have := Etale.isIso_compactificationRestrictionComparison A u
  (Functor.leftUnitor _).inv ≫
    ((mateEquiv (Etale.openImmersionLowerShriekAdjunction A c'.i)
        (Etale.openImmersionLowerShriekAdjunction A c.i)).symm
      (TwoSquare.mk _ _ _ _
        ((Functor.rightUnitor _).hom ≫
          inv (Etale.compactificationRestrictionComparison A u)))).natTrans

/-- The transition morphism of the compactification diagram along `u : c' ⟶ c`, from the
lower shriek computed at the *coarser* compactification `c` to the one computed at the
*finer* compactification `c'`: whisker `Etale.compactificationShriekComparison A u` with
`(c.g)_*` and contract `u_* ⋙ (c.g)_* ≅ (c'.g)_*`. -/
noncomputable def Etale.lowerShriekTransition (u : c' ⟶ c) :
    Etale.lowerShriekAt A c ⟶ Etale.lowerShriekAt A c' :=
  Functor.whiskerRight (Etale.compactificationShriekComparison A u)
      (Etale.lowerStar A c.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.openImmersionLowerShriek A c'.i)
      ((Etale.lowerStarComp A u.hom c.g).hom ≫ eqToHom (by rw [u.w]))

/-- The transition morphisms of the compactification diagram are isomorphisms: this is
the underived form of the canonical isomorphism `Ru_* j_{c'!} ≅ j_{c!}` of the
reference. On stalks it holds because `u` is proper with `u⁻¹(X) = X` (the Cartesian
condition), so the extension by zero along `c'.i` pushes forward along `u` to the
extension by zero along `c.i`: over points of `X` nothing changes, and over points
outside `X` both sides vanish. -/
theorem Etale.isIso_lowerShriekTransition [HasZeroObject A] (u : c' ⟶ c) :
    IsIso (Etale.lowerShriekTransition A u) :=
  sorry

/-- The transition morphism along the identity is the identity. Together with
`Etale.lowerShriekTransition_comp` this makes the transitions into a functor, the
compactification diagram `Etale.lowerShriekDiagram`. -/
theorem Etale.lowerShriekTransition_id (c : Compactification f) :
    Etale.lowerShriekTransition A (𝟙 c) = 𝟙 (Etale.lowerShriekAt A c) :=
  sorry

/-- The transition morphisms are compatible with composition of refinements (note the
contravariance). Together with `Etale.lowerShriekTransition_id` this makes the
transitions into a functor, the compactification diagram `Etale.lowerShriekDiagram`; it
is the coherence that ultimately makes the comparison between two compactifications
independent of the choice of a common refinement. -/
theorem Etale.lowerShriekTransition_comp (v : c'' ⟶ c') (u : c' ⟶ c) :
    Etale.lowerShriekTransition A (v ≫ u) =
      Etale.lowerShriekTransition A u ≫ Etale.lowerShriekTransition A v :=
  sorry

end Transition

variable (f) in
/-- The compactification diagram: the functor sending a compactification `c` of `f` to
the lower shriek `(c.i)_! ⋙ (c.g)_*` computed at `c`, and a morphism of
compactifications to its transition morphism. It is indexed by the opposite category
because the transition morphisms go from coarser to finer compactifications. Every
morphism is sent to an isomorphism (`Etale.isIso_lowerShriekTransition`), which over the
filtered index category produces the canonical comparison system
`Etale.lowerShriekCompactificationIso`. -/
noncomputable def Etale.lowerShriekDiagram :
    (Compactification f)ᵒᵖ ⥤ Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A where
  obj c := Etale.lowerShriekAt A c.unop
  map u := Etale.lowerShriekTransition A u.unop
  map_id c := Etale.lowerShriekTransition_id A c.unop
  map_comp u v := Etale.lowerShriekTransition_comp A v.unop u.unop

/-!
### The canonical comparison isomorphisms

Applying the general comparison system for functors inverting a filtered category to the
compactification diagram.
-/

section Comparison

variable [HasZeroObject A]

/-- The transition morphisms, packaged as the morphism part of the compactification
diagram, are isomorphisms; instance form of `Etale.isIso_lowerShriekTransition`, feeding
the canonical comparison system `CategoryTheory.Functor.filteredComparisonIso`. -/
instance Etale.isIso_lowerShriekDiagram_map {c d : (Compactification f)ᵒᵖ} (φ : c ⟶ d) :
    IsIso ((Etale.lowerShriekDiagram A f).map φ) :=
  Etale.isIso_lowerShriekTransition A φ.unop

variable [HasCompactification f] [QuasiCompact f]

/-- The canonical comparison isomorphism between the lower shrieks computed at two
compactifications of `f`. It satisfies the cocycle identities
(`Etale.lowerShriekCompactificationIso_refl`, `Etale.lowerShriekCompactificationIso_trans`)
and agrees with the transition morphisms along refinements
(`Etale.lowerShriekCompactificationIso_hom_eq_transition`); by the elementary Lemma
`CategoryTheory.Functor.filteredComparisonIso_hom_eq` it is *characterized* by the latter
compatibility, which is the precise meaning of `f_!` being independent of the choice of
compactification. -/
noncomputable def Etale.lowerShriekCompactificationIso (c d : Compactification f) :
    Etale.lowerShriekAt A c ≅ Etale.lowerShriekAt A d :=
  (Etale.lowerShriekDiagram A f).filteredComparisonIso (op c) (op d)

@[simp]
lemma Etale.lowerShriekCompactificationIso_refl (c : Compactification f) :
    Etale.lowerShriekCompactificationIso A c c = Iso.refl (Etale.lowerShriekAt A c) :=
  (Etale.lowerShriekDiagram A f).filteredComparisonIso_refl (op c)

/-- The cocycle identity for the canonical comparison isomorphisms: the comparisons
between the lower shrieks at different compactifications compose coherently. -/
lemma Etale.lowerShriekCompactificationIso_trans (c d e : Compactification f) :
    Etale.lowerShriekCompactificationIso A c d ≪≫ Etale.lowerShriekCompactificationIso A d e =
      Etale.lowerShriekCompactificationIso A c e :=
  (Etale.lowerShriekDiagram A f).filteredComparisonIso_trans (op c) (op d) (op e)

/-- Along a refinement `u : c' ⟶ c` the canonical comparison isomorphism is the
transition morphism itself: the abstract comparison system extends the geometrically
defined transitions. -/
lemma Etale.lowerShriekCompactificationIso_hom_eq_transition {c' c : Compactification f}
    (u : c' ⟶ c) :
    (Etale.lowerShriekCompactificationIso A c c').hom = Etale.lowerShriekTransition A u :=
  (Etale.lowerShriekDiagram A f).filteredComparisonIso_hom_eq_map u.op

variable (f) in
/-- **Invariance of the lower shriek under the choice of compactification**: the lower
shriek `f_!`, defined via the chosen compactification
`HasCompactification.compactification f`, is canonically isomorphic to the lower shriek
computed at *any* compactification `c` of `f`. The isomorphism is part of the coherent
comparison system `Etale.lowerShriekCompactificationIso`; all constructions relying on
the choice of compactification (notably the lower-shriek base-change isomorphism and the
Weil structure on `f_! K`) must use it. -/
noncomputable def Etale.lowerShriekIsoLowerShriekAt (c : Compactification f) :
    Etale.lowerShriek A f ≅ Etale.lowerShriekAt A c :=
  Etale.lowerShriekCompactificationIso A (HasCompactification.compactification f) c

end Comparison

end AlgebraicGeometry
