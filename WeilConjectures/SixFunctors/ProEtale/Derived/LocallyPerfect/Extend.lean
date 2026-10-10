/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Glue
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# Extending a perfect top part by one degree

This is the inductive step of Stacks, Tag 0FPV, once the relevant subcomplex has been found.
Let `M` be a complex of pro-étale sheaves of `Λ`-modules containing the constant complex `c(E₀)`
of a bounded complex `E₀` of finite free modules vanishing below `m`, equal to `M` in degrees
`≥ m`. Let `ι : L' ⟶ M` be a subcomplex, equal to `M` in degrees `≥ m`, such that

* `Q(ι)` has a section `s : Q(M) ⟶ Q(L')` in the derived category;
* `H^m(ι)` is an isomorphism;
* the term `L'^{m-1}` is a quotient of a constant finite free sheaf `c(V₀)`, the composite
  `c(V₀) ⟶ L'^{m-1} ⟶ L'^m = c(E₀^m)` being induced by a linear map `A : V₀ ⟶ E₀^m`.

Then the constant complex `c(E₀')` of the mapping cone `E₀'` of `A : V₀[-m] ⟶ E₀` maps to `M`,
inducing isomorphisms in cohomology in degrees `≥ m` and an epimorphism in degree `m - 1`.
By the gluing lemma `CochainComplex.exists_iso_Q_obj_of_homologyMap`, `Q(M)` has a perfect top
part in degrees `≥ m - 1` (`AlgebraicGeometry.ProEtale.hasPerfectTop_sub_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

theorem hasPerfectTop_sub_one {Y : Scheme.{u}} [Nonempty Y] {m b : ℤ}
    (M L' : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ)
    (E₀ : CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
    (j : ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      _).obj E₀ ⟶ M) (hj : ∀ i, Mono (j.f i)) (hj' : ∀ i, m ≤ i → IsIso (j.f i))
    [E₀.IsStrictlyGE m] [E₀.IsStrictlyLE b]
    (hfree : ∀ i, Module.Free Λ (E₀.X i) ∧ Module.Finite Λ (E₀.X i))
    (ι : L' ⟶ M) (hι : ∀ i, Mono (ι.f i)) (hι' : ∀ i, m ≤ i → IsIso (ι.f i))
    (s : DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj L')
    (hs : s ≫ DerivedCategory.Q.map ι = 𝟙 _) (hm : IsIso (HomologicalComplex.homologyMap ι m))
    (V₀ : ModuleCat.{u + 1} Λ) [Module.Free Λ V₀] [Module.Finite Λ V₀]
    (gen : (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj V₀ ⟶
      L'.X (m - 1)) [Epi gen]
    (A : V₀ ⟶ E₀.X m)
    (hA : gen ≫ L'.d (m - 1) m ≫ ι.f m =
      (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).map A ≫ j.f m) :
    HasPerfectTop (DerivedCategory.Q.obj M) (m - 1) := by
  sorry

end AlgebraicGeometry.ProEtale
