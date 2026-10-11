/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # The subsheaf of sections annihilated by an ideal

Source: Stacks Project, Properties, Lemma 01PO and Definition 01PP
(blueprint: lem-weil-pbc-sections-annihilated-by-ideal).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The subsheaf of sections annihilated by a quasi-coherent ideal of finite type.
Source: Stacks Project, Properties, Lemma 01PO and Definition 01PP
(blueprint: lem-weil-pbc-sections-annihilated-by-ideal).

The quasi-coherent ideal is `J : X.IdealSheafData` (quasi-coherence is built in), with
ideal sheaf `J.toModules ⊆ 𝒪_X` via `J.toModulesι`; finite type is Mathlib's
`SheafOfModules.IsFiniteType` of `J.toModules`. Its sections over an open `V` are
`J.idealOfOpens V` (`range_toModulesι_app_eq_idealOfOpens`), over an affine open `J.ideal U`.
The image of the inclusion on every open is specified by local annihilation, so `G`
is the subsheaf in the node, rather than an arbitrary quasi-coherent submodule.
The stalk clause uses `RingedSpace.moduleStalkFunctor`. It expresses annihilation by
the ideal stalk through all germs of ideal sections: every element of `J_x` is such a
germ, and its image in `𝒪_{X,x}` is the germ of the section. The stalk maps of both
inclusions are injective.

Proof (the five steps of the node):
1. Restrictions, sums and scalar multiples preserve local annihilation. Compatible
sections glue in `F`, and the product with any local ideal section vanishes on a
cover and hence vanishes. This gives a subsheaf of modules (def-weil-sheaf-of-modules-category).
2. On an affine open write `F = M~` and `I = I~` using the affine tilde/Gamma
adjunction (lem-weil-pbc-affine-tilde-gamma-adjunction). The ideal has finitely many
generators by lem-weil-pbc-quasi-coherent-finite-type-affine. On principal opens,
sections are localizations (lem-weil-pbc-spec-module-tilde-sections). Global
annihilation implies local annihilation, and the converse takes `V = U`.
3. Put `M' = {m : I m = 0}`. If `m/f^n` is killed by the localized ideal, clear
the denominator for each ideal generator, then take a common power of `f`.
This proves `(M')_f = {z : I_f z = 0}` (def-weil-pbc-module-localization-away).
For the empty generator family take exponent zero.
4. These identifications commute with restrictions on principal opens, a basis
(def-weil-affine-spectrum), and identify `G` with `(M')~` locally. Hence `G` is
quasi-coherent (pqf-def-coherent, lem-weil-pbc-spec-module-tilde-sections).
5. At a prime, use stalk localization (lem-weil-pbc-spec-tilde-stalk-localization,
lem-weil-pbc-affine-open-stalk-localization, def-weil-pbc-module-localization).
Clear one denominator outside the prime for each generator and multiply them;
the numerator then lies in `M'`. The empty product is one. Exactness of stalks
(lem-weil-pbc-module-stalk-exact) makes both inclusion stalk maps injective.
Germs and their scalar action are those of def-weil-pbc-module-stalk.
-/
theorem sections_annihilated_by_ideal
    (X : Scheme.{u}) (J : X.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (ι : G ⟶ F),
      Mono ι ∧ G.IsQuasicoherent ∧
      (∀ (U : X.Opens) (s : Γ(F, U)),
        s ∈ Set.range (ι.app U) ↔
          ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
            a • F.presheaf.map (homOfLE h).op s = 0) ∧
      (∀ (U : X.affineOpens) (s : Γ(F, U.1)),
        s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0) ∧
      (∀ x : X,
        Function.Injective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map J.toModulesι).hom ∧
        Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom ∧
        ∀ s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
          s ∈ Set.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom ↔
            ∀ (U : X.Opens) (hx : x ∈ U), ∀ a ∈ J.idealOfOpens U,
              X.presheaf.germ U x hx a • s = 0) := by
  sorry

end AlgebraicGeometry
