/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Formal glueing data for modules

Source: Stacks Project, More on Algebra, Remark 05EL, items (1) and (2)
(blueprint: def-weil-pbc-formal-glueing-data).
-/

@[expose] public section

universe u v w w₁ w₂

namespace FormalGlueing

noncomputable section

open CategoryTheory
open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Restriction of scalars along a ring homomorphism: Mathlib's
`ModuleCat.restrictScalars`. Source: Stacks, Remark 05EL
(blueprint: def-weil-pbc-formal-glueing-data). -/
abbrev restrict (φ : R →+* S) (M : ModuleCat.{w} S) : ModuleCat.{w} R :=
  (ModuleCat.restrictScalars φ).obj M

/-- Localization of an `R`-module at one element. Source: Stacks, Remark 05EL
(blueprint: def-weil-pbc-formal-glueing-data). -/
abbrev localize (f : R) (M : ModuleCat.{w} R) : ModuleCat.{max u w} R :=
  ModuleCat.of R (LocalizedModule.Away f M)

/-- Scalar extension, in Mathlib's factor order `S ⊗[R] M`. Source: Stacks,
Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
abbrev extend (φ : R →+* S) (M : ModuleCat.{w} R) : ModuleCat.{max v w} S :=
  letI : Algebra R S := φ.toAlgebra
  ModuleCat.of S (S ⊗[R] M)

/-- The `S`-action on the localization of an `S`-module, induced by localizing
each multiplication map. For each `s : S`, multiplication by `s` is R-linear
on the restriction of `M`. Localize this map using
[def-weil-pbc-module-localization]. The fraction formula is `m/t ↦ (s • m)/t`.
It is well-defined because multiplication by `s` commutes with R-scalars.
The module axioms follow on fractions from the corresponding axioms on `M`;
every localized element is a fraction [def-weil-pbc-module-localization-away].
Source: Stacks, Remark 05EL; canonical maps, clause (1)
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps);
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem exists_localized_s_module (φ : R →+* S) (f : R) (M : ModuleCat.{w} S) :
    ∃ sm : Module S (localize f (restrict φ M)),
      ∀ (s : S) (m : M) (t : Submonoid.powers f),
        sm.smul s (LocalizedModule.mk (show restrict φ M from m) t) =
          LocalizedModule.mk (show restrict φ M from s • m) t := by
  sorry

/-- The canonical `S`-module structure from the localized multiplication maps.
Source: Stacks, Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
@[instance_reducible] noncomputable def localizedSModule
    (φ : R →+* S) (f : R) (M : ModuleCat.{w} S) :
    Module S (localize f (restrict φ M)) :=
  (exists_localized_s_module φ f M).choose

/-- Localization of a linear map. Source: Stacks, Remark 05EL and Mathlib's
`IsLocalizedModule.map` (blueprint: def-weil-pbc-formal-glueing-data). -/
noncomputable def localMap (f : R) {M : ModuleCat.{w₁} R}
    {N : ModuleCat.{w₂} R} (h : M →ₗ[R] N) :
    localize f M →ₗ[R] localize f N :=
  IsLocalizedModule.map (Submonoid.powers f)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) h

/-- Restrict an `S`-linear map to the underlying `R`-modules. Source: Stacks,
Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
def restrictMap (φ : R →+* S) {M : ModuleCat.{w₁} S}
    {N : ModuleCat.{w₂} S} (h : M →ₗ[S] N) :
    restrict φ M →ₗ[R] restrict φ N :=
  { toFun := h
    map_add' := h.map_add
    map_smul' := fun r x => h.map_smul (φ r) x }

/-- Tensoring an `R`-linear map with `S`. Source: Stacks, Remark 05EL
(blueprint: def-weil-pbc-formal-glueing-data). -/
noncomputable def extendMap (φ : R →+* S) {M : ModuleCat.{w₁} R}
    {N : ModuleCat.{w₂} R}
    (h : M →ₗ[R] N) : extend φ M →ₗ[S] extend φ N :=
  letI : Algebra R S := φ.toAlgebra
  LinearMap.baseChange S h

/-- Interchanging two localizations is uniquely determined on the image of
the original module. Both `f` and `g` act invertibly on the target.
First extend `M → (M_g)_f` across localization at `f`, then across localization
at `g`, using [def-weil-pbc-module-localization-away]. This gives the displayed
map. For uniqueness, two successive applications of the same universal
property show that agreement on `M` determines the map. On fractions, division
by `f` and `g` gives `(m/f^a)/g^b ↦ (m/g^b)/f^a`.
Source: Stacks, Remark 05EL, canonical maps, clause (2)
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps);
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem exists_swap (f g : R) (M : ModuleCat.{w} R) :
    ∃! h : localize g (localize f M) →ₗ[R] localize f (localize g M),
      ∀ m : M,
        h (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
          LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  sorry

/-- The canonical interchange of two localizations. Source: Stacks, Remark
05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
noncomputable def swap (f g : R) (M : ModuleCat.{w} R) :
    localize g (localize f M) →ₗ[R] localize f (localize g M) :=
  (exists_swap f g M).exists.choose

/-- Localization commutes with scalar extension by the unique map specified
on the image of scalar extension. On pure tensors it sends `(s ⊗ m)/1` to
`s ⊗ (m/1)`. Tensor the localization map `M → M_f` with `S`, using
[def-weil-module-base-change]. Multiplication by `f` is invertible on `M_f`,
and its inverse tensors with the identity of `S`, so it is invertible on
`S ⊗[R] M_f`. The universal property
[def-weil-pbc-module-localization-away] extends the tensor map uniquely across
localization at `f`. This proves the displayed equation and uniqueness, and
gives `(s ⊗ m)/f^e ↦ s ⊗ (m/f^e)` on pure-tensor fractions.
Source: Stacks, Remark 05EL, canonical maps, clause (3)
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps);
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem exists_compare (φ : R →+* S) (f : R) (M : ModuleCat.{w} R) :
    ∃! h : localize f (restrict φ (extend φ M)) →ₗ[R]
        restrict φ (extend φ (localize f M)),
      h.comp (LocalizedModule.mkLinearMap _ (restrict φ (extend φ M))) =
        restrictMap φ (extendMap φ (LocalizedModule.mkLinearMap _ M)) := by
  sorry

/-- The canonical comparison `(M ⊗ S)_f → M_f ⊗ S`. Source: Stacks,
Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
noncomputable def compare (φ : R →+* S) (f : R) (M : ModuleCat.{w} R) :
    localize f (restrict φ (extend φ M)) →ₗ[R]
      restrict φ (extend φ (localize f M)) :=
  (exists_compare φ f M).exists.choose

/-- The comparison map commutes with the localized `S`-action. This follows
on fractions from its formula on pure tensors: multiplying `(a ⊗ m)/f^e`
by `s` replaces `a` by `s * a` on either side of the comparison. Every tensor
is a finite sum of pure tensors, and every localized element is a fraction;
additivity therefore extends the equality to every element.
Source: Stacks, Remark 05EL,
canonical maps, clause (3) (blueprint: lem-weil-pbc-formal-glueing-canonical-maps);
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem compare_smul (φ : R →+* S) (f : R) (M : ModuleCat.{w} R)
    (s : S) (x : localize f (restrict φ (extend φ M))) :
    compare φ f M ((localizedSModule φ f (extend φ M)).smul s x) =
      (s • (compare φ f M x : extend φ (localize f M))) := by
  sorry

/-- Localization of an `S`-linear map remains `S`-linear for the localized
actions. Write the element as `m/t` using
[def-weil-pbc-module-localization-away]. The two sides are respectively
`h (s • m)/t` and `(s • h m)/t`, by the fraction formulas for localization
[def-weil-pbc-module-localization] and the localized action. They agree because
`h` is S-linear. Source: Stacks, Remark 05EL, canonical maps, clause (1)
(blueprint: lem-weil-pbc-formal-glueing-canonical-maps);
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem localMap_smul (φ : R →+* S) (f : R) {M N : ModuleCat.{w} S}
    (h : M →ₗ[S] N) (s : S) (x : localize f (restrict φ M)) :
    localMap f (restrictMap φ h) ((localizedSModule φ f M).smul s x) =
      (localizedSModule φ f N).smul s (localMap f (restrictMap φ h) x) := by
  sorry

/-- A module over `R_f`, regarded as an `R`-module. Source: Stacks,
Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
abbrev piece (f : R) (M : ModuleCat.{w} (Localization.Away f)) : ModuleCat.{w} R :=
  restrict (algebraMap R (Localization.Away f)) M

/-- The base change of an `R`-linear map, viewed as an `R`-linear map.
Source: Stacks, Remark 05EL (blueprint: def-weil-pbc-formal-glueing-data). -/
noncomputable def extendMapR (φ : R →+* S) {M N : ModuleCat.{w} R}
    (h : M →ₗ[R] N) : restrict φ (extend φ M) →ₗ[R] restrict φ (extend φ N) :=
  restrictMap φ (extendMap φ h)

/-- An object of the formal glueing category. The first equation identifies
the two paths from `(M'_fi)_fj` to `(M_j)_fi ⊗ S`; the second is the threefold
cocycle equation. Source: Stacks, Remark 05EL, item (1)
(blueprint: def-weil-pbc-formal-glueing-data). -/
structure Data (φ : R →+* S) {t : ℕ} (f : Fin t → R) where
  M' : ModuleCat.{w} S
  M : ∀ i : Fin t, ModuleCat.{w} (Localization.Away (f i))
  alpha : ∀ i : Fin t,
    localize (f i) (restrict φ M') ≃ₗ[R]
      restrict φ (extend φ (piece (f i) (M i)))
  alpha_smul : ∀ (i : Fin t) (s : S) (x : localize (f i) (restrict φ M')),
    alpha i ((localizedSModule φ (f i) M').smul s x) =
      (s • (alpha i x : extend φ (piece (f i) (M i))))
  alpha_overlap : ∀ i j : Fin t,
    localize (f j) (piece (f i) (M i)) ≃ₗ[R]
      localize (f i) (piece (f j) (M j))
  square : ∀ i j : Fin t,
    (extendMapR φ (alpha_overlap i j).toLinearMap).comp
        ((compare φ (f j) (piece (f i) (M i))).comp
          (localMap (f j) (alpha i).toLinearMap)) =
      (compare φ (f i) (piece (f j) (M j))).comp
        ((localMap (f i) (alpha j).toLinearMap).comp
          (swap (f i) (f j) (restrict φ M')))
  cocycle : ∀ i j k : Fin t,
    (localMap (f i) (alpha_overlap j k).toLinearMap).comp
        ((swap (f i) (f k) (piece (f j) (M j))).comp
          (localMap (f k) (alpha_overlap i j).toLinearMap)) =
      (swap (f i) (f j) (piece (f k) (M k))).comp
        ((localMap (f j) (alpha_overlap i k).toLinearMap).comp
          (swap (f j) (f k) (piece (f i) (M i))))

/-- A morphism of formal glueing data is a family of compatible linear maps.
Source: Stacks, Remark 05EL, item (2)
(blueprint: def-weil-pbc-formal-glueing-data). -/
structure Hom {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (X Y : Data φ f) where
  prime : X.M' →ₗ[S] Y.M'
  chart : ∀ i : Fin t, piece (f i) (X.M i) →ₗ[R] piece (f i) (Y.M i)
  prime_compat : ∀ i : Fin t,
    (Y.alpha i).toLinearMap.comp (localMap (f i) (restrictMap φ prime)) =
      (extendMapR φ (chart i)).comp (X.alpha i).toLinearMap
  chart_compat : ∀ i j : Fin t,
    (Y.alpha_overlap i j).toLinearMap.comp (localMap (f j) (chart i)) =
      (localMap (f i) (chart j)).comp (X.alpha_overlap i j).toLinearMap

/-- Identity maps satisfy both glueing compatibilities, since localization
and base change preserve identities [def-weil-pbc-module-localization],
[def-weil-module-base-change]. Replace each localized or base-changed identity
by the identity; both sides of each equation then equal the same structural
map. Source: Stacks, Remark 05EL, item (2)
(blueprint: def-weil-pbc-formal-glueing-data). -/
theorem id_compat {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (X : Data φ f) :
    (∀ i : Fin t,
      (X.alpha i).toLinearMap.comp
          (localMap (f i) (restrictMap φ (LinearMap.id : X.M' →ₗ[S] X.M'))) =
        (extendMapR φ (LinearMap.id : piece (f i) (X.M i) →ₗ[R]
          piece (f i) (X.M i))).comp (X.alpha i).toLinearMap) ∧
    (∀ i j : Fin t,
      (X.alpha_overlap i j).toLinearMap.comp
          (localMap (f j) (LinearMap.id : piece (f i) (X.M i) →ₗ[R]
            piece (f i) (X.M i))) =
        (localMap (f i) (LinearMap.id : piece (f j) (X.M j) →ₗ[R]
          piece (f j) (X.M j))).comp (X.alpha_overlap i j).toLinearMap) := by
  sorry

/-- Componentwise composition respects both glueing compatibilities, by
functoriality of localization [def-weil-pbc-module-localization] and scalar
extension [def-weil-module-base-change]. For the prime equation, expand the
localization of `v.prime.comp u.prime`, apply `v.prime_compat`, then
`u.prime_compat`, and combine the two base-changed chart maps. For the overlap
equation expand the localization of each composite chart map, apply
`v.chart_compat` then `u.chart_compat`, and combine the localized chart maps.
Source: Stacks, Remark
05EL, item (2) (blueprint: def-weil-pbc-formal-glueing-data). -/
theorem comp_compat {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    {X Y Z : Data φ f} (u : Hom X Y) (v : Hom Y Z) :
    (∀ i : Fin t,
      (Z.alpha i).toLinearMap.comp
          (localMap (f i) (restrictMap φ (v.prime.comp u.prime))) =
        (extendMapR φ ((v.chart i).comp (u.chart i))).comp
          (X.alpha i).toLinearMap) ∧
    (∀ i j : Fin t,
      (Z.alpha_overlap i j).toLinearMap.comp
          (localMap (f j) ((v.chart i).comp (u.chart i))) =
        (localMap (f i) ((v.chart j).comp (u.chart j))).comp
          (X.alpha_overlap i j).toLinearMap) := by
  sorry

/-- The identity morphism has identity maps in every component. Source:
Stacks, Remark 05EL, item (2) (blueprint: def-weil-pbc-formal-glueing-data). -/
def idHom {t : ℕ} {φ : R →+* S} {f : Fin t → R} (X : Data φ f) : Hom X X where
  prime := LinearMap.id
  chart := fun _ => LinearMap.id
  prime_compat := (id_compat X).1
  chart_compat := (id_compat X).2

/-- Composition of morphisms is componentwise. Source: Stacks, Remark 05EL,
item (2) (blueprint: def-weil-pbc-formal-glueing-data). -/
def compHom {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    {X Y Z : Data φ f} (u : Hom X Y) (v : Hom Y Z) : Hom X Z where
  prime := v.prime.comp u.prime
  chart := fun i => (v.chart i).comp (u.chart i)
  prime_compat := (comp_compat u v).1
  chart_compat := (comp_compat u v).2

/-- The category laws follow componentwise from the category laws for
linear maps [def-nagata-category]. For each identity law, the prime and every
chart component reduce to the corresponding identity law for linear maps.
For associativity, these components are equal by associativity of linear-map
composition. Equality of the components gives equality of the `Hom`
structures, since their remaining fields are propositions.
Source: Stacks, Remark 05EL,
item (2) (blueprint: def-weil-pbc-formal-glueing-data). -/
theorem category_laws {t : ℕ} {φ : R →+* S} {f : Fin t → R} :
    (∀ {X Y : Data.{u, v, w} φ f} (u : Hom X Y), compHom (idHom X) u = u) ∧
    (∀ {X Y : Data.{u, v, w} φ f} (u : Hom X Y), compHom u (idHom Y) = u) ∧
    (∀ {W X Y Z : Data.{u, v, w} φ f} (u : Hom W X) (v : Hom X Y) (t : Hom Y Z),
      compHom (compHom u v) t = compHom u (compHom v t)) := by
  sorry

/-- The category `Glue(R → S, (f_i))`. Source: Stacks, Remark 05EL,
items (1) and (2) (blueprint: def-weil-pbc-formal-glueing-data). -/
instance {t : ℕ} (φ : R →+* S) (f : Fin t → R) :
    CategoryTheory.Category.{w} (Data.{u, v, w} φ f) where
  Hom := fun X Y => Hom X Y
  id := fun X => idHom X
  comp := fun {X Y Z} (u : Hom X Y) (v : Hom Y Z) => compHom u v
  id_comp := (category_laws.{u, v, w} (φ := φ) (f := f)).1
  comp_id := (category_laws.{u, v, w} (φ := φ) (f := f)).2.1
  assoc := by
    intro W X Y Z u v t
    exact (category_laws.{u, v, w} (φ := φ) (f := f)).2.2 u v t

end

end FormalGlueing
