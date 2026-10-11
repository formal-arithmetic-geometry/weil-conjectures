/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Assembly of compatible null-homotopies

Source: Stacks Project, Derived Categories, Tag 015I, boundary/cycle exact sequences;
Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-compatible-homotopy-assembly).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

/-- A prescribed null-homotopy on the subcomplex extends to compatible null-homotopies
on the middle complex and quotient. Source: Stacks Project, Tag 015I, boundary/cycle
exact sequences; Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-ce-compatible-homotopy-assembly).

The source augmentations are quasi-isomorphisms from `single₀`, expressing exactness
of the augmented complexes. The target resolutions may resolve different objects:
`S` is the source augmentation sequence and `T` the target augmentation sequence.
The complexes are indexed from zero, as in the node's proof. A homotopy's components
out of degree zero are all zero; this encodes the absent degree minus one term.

Proof, step 1: extend each component of `sZ` across the monomorphism `i` by
injectivity of `JZ`. Injectivity also splits `j`, giving a section of `ρ`.
Apply `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` to the augmented exact
complex `B` and its augmentation-zero map `RB`, obtaining a null-homotopy `sB`.
Step 2: combine the extended `sZ` and the lift of `sB` to a graded map `t` with
`t i = j sZ` and `ρ t = sB π`. The defect `RI - (d t + t d)` vanishes on `i` and
under `ρ`, so exactness factors it as `j E' π`. The induced chain map `E'` from
`B` to `JZ` vanishes on the augmentation, using that `t` vanishes in degree zero
and that the augmentation quotient map is epic.
Step 3: the same acyclic-to-injective lemma gives a null-homotopy `k` of `E'`.
Set `sI = t + j k π`. This kills the defect and preserves both compatibility
identities since `π i = 0` and `ρ j = 0`.
Step 4: all constructed homotopies vanish in degree zero, giving the stated
normalization and all four identities. -/
theorem exists_compatible_nullHomotopies
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact)
    (Z I B : CochainComplex C ℕ)
    (i : Z ⟶ I) (π : I ⟶ B) (hiπ : i ≫ π = 0)
    (hsource : ∀ n : ℕ, ((ShortComplex.mk i π hiπ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (εZ : (CochainComplex.single₀ C).obj S.X₁ ⟶ Z)
    (εI : (CochainComplex.single₀ C).obj S.X₂ ⟶ I)
    (εB : (CochainComplex.single₀ C).obj S.X₃ ⟶ B)
    [QuasiIso εZ] [QuasiIso εI] [QuasiIso εB]
    (hεi : εZ ≫ i = (CochainComplex.single₀ C).map S.f ≫ εI)
    (hεπ : εI ≫ π = (CochainComplex.single₀ C).map S.g ≫ εB)
    (JZ : InjectiveResolution T.X₁) (JI : InjectiveResolution T.X₂)
    (JB : InjectiveResolution T.X₃)
    (j : JZ.cocomplex ⟶ JI.cocomplex) (ρ : JI.cocomplex ⟶ JB.cocomplex)
    (hjρ : j ≫ ρ = 0)
    (htarget : ∀ n : ℕ, ((ShortComplex.mk j ρ hjρ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hιj : JZ.ι ≫ j = (CochainComplex.single₀ C).map T.f ≫ JI.ι)
    (hιρ : JI.ι ≫ ρ = (CochainComplex.single₀ C).map T.g ≫ JB.ι)
    (RZ : Z ⟶ JZ.cocomplex) (RI : I ⟶ JI.cocomplex) (RB : B ⟶ JB.cocomplex)
    (hRi : i ≫ RI = RZ ≫ j) (hRπ : RI ≫ ρ = π ≫ RB)
    (hRε : εI ≫ RI = 0) (sZ : Homotopy RZ 0)
    (hsZε : ∀ m : ℕ, εZ.f 0 ≫ sZ.hom 0 m = 0) :
    ∃ (sI : Homotopy RI 0) (sB : Homotopy RB 0),
      (∀ m : ℕ, sI.hom 0 m = 0 ∧ sB.hom 0 m = 0) ∧
      (∀ n m : ℕ, i.f n ≫ sI.hom n m = sZ.hom n m ≫ j.f m) ∧
      (∀ n m : ℕ, sI.hom n m ≫ ρ.f m = π.f n ≫ sB.hom n m) := by
  sorry

end CategoryTheory
