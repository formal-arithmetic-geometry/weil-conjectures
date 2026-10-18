/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
public import WeilConjectures.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Symbols of filtered morphisms into an injective filtered object

Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-target-hom-symbol).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits DirectSum
open scoped BigOperators

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The condition that a morphism has filtered degree at least `r`.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).
This is the condition `f(F^p X) ⊆ F^(p+r) Y` written by its factorisation through the
subobject inclusion. -/
def HasFilteredDegree (X Y : FilteredObject C) (r : ℤ) (f : X.obj ⟶ Y.obj) : Prop :=
  ∀ p : ℤ, ∃ l : (X.filtration.F p : C) ⟶ (Y.filtration.F (p + r) : C),
    l ≫ (Y.filtration.F (p + r)).arrow = (X.filtration.F p).arrow ≫ f

/-- The subgroup `G^r(X,Y)` of morphisms of filtered degree at least `r`.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol). -/
def filteredHomSubgroup (X Y : FilteredObject C) (r : ℤ) :
    AddSubgroup (X.obj ⟶ Y.obj) where
  carrier := {f | HasFilteredDegree X Y r f}
  zero_mem' := by
    intro p
    exact ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg p
    obtain ⟨lf, hlf⟩ := hf p
    obtain ⟨lg, hlg⟩ := hg p
    refine ⟨lf + lg, ?_⟩
    rw [Preadditive.add_comp, hlf, hlg, Preadditive.comp_add]
  neg_mem' := by
    intro f hf p
    obtain ⟨lf, hlf⟩ := hf p
    refine ⟨-lf, ?_⟩
    rw [Preadditive.neg_comp, hlf, Preadditive.comp_neg]

/-- A filtered morphism induces a map on its `p`-th graded pieces after a shift.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).
The map is characterized by the quotient equation for the inclusion
`F^(p+1)X ≤ F^pX`; this makes the construction canonical.

Proof: the restriction `F^pX ⟶ F^(p+r)Y` of `f`, composed with the inclusion
`F^(p+1)X ⟶ F^pX`, factors through `F^(p+r+1)Y` because `f` also has degree `r` at
`p + 1`; hence its composite with the quotient to `gr^(p+r)Y` kills `F^(p+1)X` and
descends along the cokernel. -/
theorem exists_shiftedGradedMap (X Y : FilteredObject C) (r : ℤ)
    (f : filteredHomSubgroup X Y r) (p : ℤ) :
    ∃ g : X.filtration.gr p ⟶ Y.filtration.gr (p + r),
      cokernel.π (Subobject.ofLE (X.filtration.F (p + 1)) (X.filtration.F p)
          (X.filtration.antitone (by omega))) ≫ g =
        Classical.choose (f.2 p) ≫
          cokernel.π (Subobject.ofLE (Y.filtration.F (p + r + 1))
            (Y.filtration.F (p + r)) (Y.filtration.antitone (by omega))) := by
  sorry

/-- The `p`-th component `σ_r(f)_p : gr^pX ⟶ gr^(p+r)Y` of the symbol of `f ∈ G^r(X,Y)`.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).
It is the unique map satisfying the quotient equation of `exists_shiftedGradedMap`
(the cokernel projection is an epimorphism). -/
noncomputable def shiftedGradedMap (X Y : FilteredObject C) (r : ℤ)
    (f : filteredHomSubgroup X Y r) (p : ℤ) :
    X.filtration.gr p ⟶ Y.filtration.gr (p + r) :=
  Classical.choose (exists_shiftedGradedMap X Y r f p)

/-- The canonical additive component map of the shifted graded symbol.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).
Its existence and additivity are the standard functoriality of passage to the quotient;
the theorem is postponed for the stage-3 proof.

Proof: the restriction of `f + g` is the sum of the restrictions (the subobject arrow is a
monomorphism), so by uniqueness of the descended map along the epimorphic cokernel
projection, `shiftedGradedMap` is additive in `f`. -/
theorem exists_shiftedGradedMapHom (X Y : FilteredObject C) (r p : ℤ) :
    ∃ φ : filteredHomSubgroup X Y r →+ (X.filtration.gr p ⟶ Y.filtration.gr (p + r)),
      ∀ f : filteredHomSubgroup X Y r, φ f = shiftedGradedMap X Y r f p := by
  sorry

/-- The canonical additive `p`-th symbol component `f ↦ σ_r(f)_p`.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol). -/
noncomputable def shiftedGradedMapHom (X Y : FilteredObject C) (r p : ℤ) :
    filteredHomSubgroup X Y r →+ (X.filtration.gr p ⟶ Y.filtration.gr (p + r)) :=
  Classical.choose (exists_shiftedGradedMapHom X Y r p)

/-- The symbol map into the finite direct sum of graded Hom groups.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).
The sum is over the finite interval supplied by the filtration bound on `X`. -/
noncomputable def filteredHomSymbol (X Y : FilteredObject C) (r a b : ℤ) :
    filteredHomSubgroup X Y r →+
      (⨁ p : ℤ, (X.filtration.gr p ⟶ Y.filtration.gr (p + r))) where
  toFun f := ∑ p ∈ Finset.Icc a b,
    (DirectSum.of (fun p : ℤ => (X.filtration.gr p ⟶ Y.filtration.gr (p + r))) p
      (shiftedGradedMapHom X Y r p f))
  map_zero' := by simp
  map_add' f g := by
    simp only [map_add, Finset.sum_add_distrib]

/-- Precomposition by a filtration-preserving map preserves filtered degree.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).

Proof: compose the restriction `F^pX' ⟶ F^pX` of `u` with the restriction
`F^pX ⟶ F^(p+r)Y` of `f`. -/
theorem precomp_mem (X' X Y : FilteredObject C) (r : ℤ) (u : FilteredObject.Hom X' X)
    (f : filteredHomSubgroup X Y r) : u.hom ≫ f.1 ∈ filteredHomSubgroup X' Y r := by
  sorry

/-- Postcomposition by a filtration-preserving map preserves filtered degree.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol).

Proof: compose the restriction `F^pX ⟶ F^(p+r)Y` of `f` with the restriction
`F^(p+r)Y ⟶ F^(p+r)Y'` of `v`. -/
theorem postcomp_mem (X Y Y' : FilteredObject C) (r : ℤ) (v : FilteredObject.Hom Y Y')
    (f : filteredHomSubgroup X Y r) : f.1 ≫ v.hom ∈ filteredHomSubgroup X Y' r := by
  sorry

/-- The additive precomposition map `f ↦ f ∘ u` on filtered Hom subgroups.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol). -/
noncomputable def precompHom (X' X Y : FilteredObject C) (r : ℤ) (u : FilteredObject.Hom X' X) :
    filteredHomSubgroup X Y r →+ filteredHomSubgroup X' Y r where
  toFun f := ⟨u.hom ≫ f.1, precomp_mem X' X Y r u f⟩
  map_zero' := by simp
  map_add' f g := by
    simp

/-- The additive postcomposition map `f ↦ v ∘ f` on filtered Hom subgroups.
Source: Stacks Project, Derived Categories, Tag 05TP
(blueprint: lem-trf-injective-target-hom-symbol). -/
noncomputable def postcompHom (X Y Y' : FilteredObject C) (r : ℤ) (v : FilteredObject.Hom Y Y') :
    filteredHomSubgroup X Y r →+ filteredHomSubgroup X Y' r where
  toFun f := ⟨f.1 ≫ v.hom, postcomp_mem X Y Y' r v f⟩
  map_zero' := by simp
  map_add' f g := by
    simp

/-- Exact symbol sequence and its naturality for finite filtered objects with injective target
graded pieces.

Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-target-hom-symbol).

Proof:
1. Choose bounds for the finite filtrations and split the target filtration by
   `lem-trf-injective-graded-filtration-splits`. Extend each prescribed graded component
   across `gr^p X ↪ X/F^(p+1)X` using injectivity of the corresponding target summand.
2. Sum the finitely many extended components. The resulting map has filtered degree `r`,
   and its symbols are the prescribed family, proving surjectivity of the symbol map.
3. A degree-`r` map has zero symbol exactly when its image of every `F^p X` lies in
   `F^(p+r+1)Y`; this identifies the kernel with `G^(r+1)` and gives exactness.
4. Passage to filtration steps and quotients commutes with precomposition and postcomposition;
   the resulting component identities are the naturality of the quotient isomorphisms. -/
theorem injectiveTargetHomSymbol
    (X Y : FilteredObject C)
    (a b c d : ℤ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hXa : X.filtration.F a = ⊤) (hXb : X.filtration.F (b + 1) = ⊥)
    (hYc : Y.filtration.F c = ⊤) (hYd : Y.filtration.F (d + 1) = ⊥)
    (hgr : ∀ q : ℤ, Injective (Y.filtration.gr q))
    (r : ℤ) :
    filteredHomSubgroup X Y (r + 1) ≤ filteredHomSubgroup X Y r ∧
      (∀ f : filteredHomSubgroup X Y r,
        filteredHomSymbol X Y r a b f = 0 ↔ f.1 ∈ filteredHomSubgroup X Y (r + 1)) ∧
      Function.Surjective (filteredHomSymbol X Y r a b) ∧
      (∀ (X' : FilteredObject C) (a' b' : ℤ), a' ≤ b' →
          X'.filtration.F a' = ⊤ → X'.filtration.F (b' + 1) = ⊥ →
          ∀ (u : FilteredObject.Hom X' X) (f : filteredHomSubgroup X Y r) (p : ℤ),
            shiftedGradedMapHom X' Y r p (precompHom X' X Y r u f) =
              FilteredObject.gradedMap u p ≫ shiftedGradedMapHom X Y r p f) ∧
      (∀ (Y' : FilteredObject C) (c' d' : ℤ), c' ≤ d' →
          Y'.filtration.F c' = ⊤ → Y'.filtration.F (d' + 1) = ⊥ →
          (∀ q : ℤ, Injective (Y'.filtration.gr q)) →
          ∀ (v : FilteredObject.Hom Y Y') (f : filteredHomSubgroup X Y r) (p : ℤ),
            shiftedGradedMapHom X Y' r p (postcompHom X Y Y' r v f) =
              shiftedGradedMapHom X Y r p f ≫ FilteredObject.gradedMap v (p + r)) := by
  sorry

end CategoryTheory.FilteredObject
