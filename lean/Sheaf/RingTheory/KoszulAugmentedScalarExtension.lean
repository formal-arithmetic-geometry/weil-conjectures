/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Augmented Koszul scalar extension

Source: Stacks Project, more-algebra.tex, Tag 062H, first identity in the proof,
and Tags 0622/0623, with the explicit balanced quotient and augmentation calculation
(blueprint: lem-trf-koszul-augmented-scalar-extension).

The mixed tensor puts the scalar ring first. Its unit is removed explicitly, so
`s ⊗ x` below represents `x ⊗ s` in the factor order of the source statement.
The existential augmentations and comparison are fixed by their component formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ExteriorAlgebra.KoszulAugmentedScalarExtension

/-- The given Koszul complex in cochain degrees `-q`, using the standard extension.
Source: Stacks, Tags 0622/0623 (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
abbrev complex (R : Type u) [CommRing R] {r : ℕ} (g : Fin r → R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (koszulComplex R r g).extend ComplexShape.embeddingDownNat

/-- The quotient by the specified finite sequence, as a module.
Source: Stacks, Tag 0623 (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
abbrev quotient (R : Type u) [CommRing R] {r : ℕ} (g : Fin r → R) : ModuleCat.{u} R :=
  ModuleCat.of R (R ⧸ Ideal.span (Set.range g))

/-- The augmentation target, with the quotient in degree zero.
Source: Stacks, Tag 0623 (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
abbrev quotientComplex (R : Type u) [CommRing R] {r : ℕ} (g : Fin r → R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (quotient R g)

/-- Scalar extension as the specified mixed total tensor, with its scalar-ring action.
Source: Stacks, Tag 062H (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
def total {A S : Type u} [CommRing A] [CommRing S] (φ : A →+* S) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.mixedTotalTensor φ).obj
    ((CochainComplex.singleFunctor (ModuleCat.{u} S) (0 : ℤ)).obj (ModuleCat.of S S))

/-- The canonical component identification removing the total tensor's degree-zero unit.
Source: Stacks, Tag 062H (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
def totalDegreeIso {A S : Type u} [CommRing A] [CommRing S] (φ : A →+* S)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((total φ).obj E).X n ≅ (ModuleCat.extendScalars φ).obj (E.X n) :=
  (HomologicalComplex.eval (ModuleCat.{u} S) (.up ℤ) n).mapIso
      (CochainComplex.mapBifunctorSingle₁Iso (ModuleCat.mixedTensor φ)
        (ModuleCat.of S S) E) ≪≫
    λ_ ((ModuleCat.extendScalars φ).obj (E.X n))

/-- The canonical identification of the total tensor of a single with a single tensor.
Source: Stacks, Tag 062H (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
def totalSingleIso {A S : Type u} [CommRing A] [CommRing S] (φ : A →+* S)
    (M : ModuleCat.{u} A) :
    (total φ).obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj M) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} S) (0 : ℤ)).obj
        ((ModuleCat.extendScalars φ).obj M) :=
  CochainComplex.mapBifunctorSingle₁Iso (ModuleCat.mixedTensor φ) (ModuleCat.of S S) _ ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((ModuleCat.mixedTensor φ).obj (ModuleCat.of S S)) (.up ℤ) (0 : ℤ)).app M ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} S) (0 : ℤ)).mapIso
      (λ_ ((ModuleCat.extendScalars φ).obj M))

/-- The standard identification of cochain degree `-q` with the exterior power.
Source: Stacks, Tags 0622/0623 (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
def degreeIso (R : Type u) [CommRing R] {r : ℕ} (g : Fin r → R) (q : ℕ) :
    (complex R g).X (-(q : ℤ)) ≅ ModuleCat.of R (⋀[R]^q (Fin r →₀ R)) :=
  (koszulComplex R r g).extendXIso ComplexShape.embeddingDownNat rfl

/-- The prescribed quotient component of the augmentation, before the target single's unit.
Source: Stacks, Tag 0623 (blueprint: lem-trf-koszul-augmented-scalar-extension). -/
def quotientComponent (R : Type u) [CommRing R] {r : ℕ} (g : Fin r → R) :
    (complex R g).X 0 ⟶ quotient R g :=
  (degreeIso R g 0).hom ≫
    (exteriorPower.zeroEquiv R (Fin r →₀ R)).toModuleIso.hom ≫
    ModuleCat.ofHom (Ideal.span (Set.range g)).mkQ

/-- The normalized scalar-extension isomorphism preserves the quotient augmentation.
Source: Stacks, Tag 062H, first identity in its proof, and Tags 0622/0623
(blueprint: lem-trf-koszul-augmented-scalar-extension).

Proof:
1. Use `lem-weil-pbc-tensor-quotient-base-change`, and flip the tensor factors.
   The balanced map sends `s ⊗ ā` to the class of `φ(a)s`; its inverse sends the
   class of `s` to `s ⊗ 1`. The extended ideal is the span of the images of `g`.
2. In `def-pc-mixed-total-tensor`, put `S[0]` first. Only first degree zero
   survives; the differential sign is `(-1)^0 = 1`. Removing its tensor unit
   gives `totalDegreeIso`, naturally in the other complex. For a single complex
   this is `totalSingleIso`.
3. Use `lem-weil-pbc-exterior-power-free-basis`. Send each scalar-extended
   standard wedge to the corresponding wedge over `S`. Its inverse sends a
   wedge with coefficient `s` to that wedge tensored with `s`. Basis expansions
   and tensor balancing prove both inverse identities, including degree zero.
4. On a wedge indexed by `i₁ < ... < i_q`, contraction is the alternating sum
   of omitted wedges with coefficients `(-1)^(k-1)g(i_k)`. Scalar extension
   changes these coefficients to `(-1)^(k-1)φ(g(i_k))`. Thus these inverse
   component maps form a cochain isomorphism `b` on the given Koszul complexes.
5. Quotient kills each generator, so the degree-zero quotient components
   define the augmentations. Both composites in their square send `a ⊗ s`
   to the class of `φ(a)s`; away from degree zero their target is zero.
6. Apply `def-weil-abstract-derived-category`'s localization functor to `b`
   and the square. This gives `β` and the asserted derived equation. Empty
   sequences reduce to the tensor unit, and zero rings satisfy the same
   component and inverse identities. No flatness or regularity is used. -/
theorem exists_augmented_scalar_extension {A S : Type u} [CommRing A] [CommRing S]
    (φ : A →+* S) (r : ℕ) (g : Fin r → A)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    ∃ θ : (ModuleCat.extendScalars φ).obj (quotient A g) ≅ quotient S (φ ∘ g),
      (∀ (a : A) (s : S),
        θ.hom (s ⊗ₜ[A, φ] Ideal.Quotient.mk (Ideal.span (Set.range g)) a) =
          Ideal.Quotient.mk (Ideal.span (Set.range (φ ∘ g))) (φ a * s)) ∧
      (∀ s : S,
        θ.inv (Ideal.Quotient.mk (Ideal.span (Set.range (φ ∘ g))) s) =
          s ⊗ₜ[A, φ] (1 : A ⧸ Ideal.span (Set.range g))) ∧
      ∃ εA : complex A g ⟶ quotientComplex A g,
      ∃ εS : complex S (φ ∘ g) ⟶ quotientComplex S (φ ∘ g),
        εA.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (quotient A g)).hom = quotientComponent A g ∧
        εS.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (quotient S (φ ∘ g))).hom = quotientComponent S (φ ∘ g) ∧
        ∃ b : (total φ).obj (complex A g) ≅ complex S (φ ∘ g),
          (∀ (q : ℕ) (i : Fin q → Fin r) (s : S),
            b.hom.f (-(q : ℤ))
              ((totalDegreeIso φ (complex A g) (-(q : ℤ))).inv
                (s ⊗ₜ[A, φ] (degreeIso A g q).inv
                  (exteriorPower.ιMulti A q (fun j ↦ Finsupp.single (i j) 1)))) =
              (degreeIso S (φ ∘ g) q).inv
                (s • exteriorPower.ιMulti S q (fun j ↦ Finsupp.single (i j) 1))) ∧
          ∃ β : DerivedCategory.Q.obj ((total φ).obj (complex A g)) ≅
              DerivedCategory.Q.obj (complex S (φ ∘ g)),
            β = DerivedCategory.Q.mapIso b ∧
            DerivedCategory.Q.map ((total φ).map εA) ≫
                DerivedCategory.Q.map (totalSingleIso φ (quotient A g)).hom ≫
                DerivedCategory.Q.map
                  ((CochainComplex.singleFunctor (ModuleCat.{u} S) (0 : ℤ)).map θ.hom) =
              β.hom ≫ DerivedCategory.Q.map εS := by
  sorry

end ExteriorAlgebra.KoszulAugmentedScalarExtension
