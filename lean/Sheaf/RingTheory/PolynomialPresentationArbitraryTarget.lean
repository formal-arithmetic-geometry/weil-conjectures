/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.CategoryTheory.Opposites

/-!
# Bounded polynomial presentation categories over an arbitrary target

Source: Stacks Project, Cotangent Complex, equation-three-maps and Tag 08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target).

These are the arbitrary-target extension of the polynomial-target coordinates in
`Algebra.PolynomialPresentation`. Variables are subsets of the same infinite bound.
The base-changed algebra is B[T]; its specialization models Q tensor_P B.
`PairHom.baseSquare` uniquely determines the stored base-change map, so morphisms
are exactly compatible augmented pairs, without a choice of additional map.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace Algebra.PolynomialPresentation.ArbitraryTarget

variable (I A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C]

/-- An augmented polynomial B-algebra, in small coordinates. Source: Stacks 08QR/08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
structure Target (I B C : Type u) [CommRing B] [CommRing C] [Algebra B C] where
  vars : Set I
  values : vars → C

/-- The augmentation, obtained by polynomial evaluation. Source: Stacks 08QR/08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable def Target.augmentation (T : Target I B C) :
    MvPolynomial T.vars B →ₐ[B] C := MvPolynomial.aeval T.values

/-- Augmentation-preserving B-algebra maps. Source: Stacks 08QR/08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
def TargetHom (T U : Target I B C) :=
  { f : MvPolynomial T.vars B →ₐ[B] MvPolynomial U.vars B //
    U.augmentation.comp f = T.augmentation }

/-- The ordinary category of augmented polynomial algebras; the site is its opposite.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable instance targetCategory : SmallCategory (Target I B C) where
  Hom := TargetHom I B C
  id T := ⟨AlgHom.id B _, by ext; rfl⟩
  comp f g := ⟨g.val.comp f.val, by rw [← AlgHom.comp_assoc, g.property, f.property]⟩
  id_comp f := Subtype.ext (by ext; rfl)
  comp_id f := Subtype.ext (by ext; rfl)
  assoc f g h := Subtype.ext (by ext; rfl)

/-- A compatible pair P = A[S], Q = P[T] augmented to B and C. The second augmentation
is determined by the displayed values of T and the first augmentation on coefficients.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
structure Pair (I A B C : Type u) [CommRing A] [CommRing B] [Algebra A B] where
  lowerVars : Set I
  upperVars : Set I
  lower : MvPolynomial lowerVars A →ₐ[A] B
  upperValues : upperVars → C

/-- The polynomial B-algebra Q ⊗_P B = B[T], with its induced augmentation.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
def Pair.target (W : Pair I A B C) : Target I B C := ⟨W.upperVars, W.upperValues⟩

/-- Coefficient specialization Q → B[T]. Source: Stacks 08QR/08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable def Pair.specialize (W : Pair I A B C) :
    MvPolynomial W.upperVars (MvPolynomial W.lowerVars A) →+*
      MvPolynomial W.upperVars B := MvPolynomial.map W.lower.toRingHom

/-- The upper augmentation Q → C, including compatibility with P → B → C.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable def Pair.augmentation (W : Pair I A B C) :
    MvPolynomial W.upperVars (MvPolynomial W.lowerVars A) →+* C :=
  W.target.augmentation.toRingHom.comp W.specialize

/-- Commuting augmented pairs and their canonical base change. `baseChange` is uniquely
fixed by `baseSquare`, since the specialization sends each X to X and baseChange is B-linear.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
@[ext] structure PairHom (W V : Pair I A B C) where
  lower : MvPolynomial W.lowerVars A →ₐ[A] MvPolynomial V.lowerVars A
  upper : MvPolynomial W.upperVars (MvPolynomial W.lowerVars A) →+*
    MvPolynomial V.upperVars (MvPolynomial V.lowerVars A)
  baseChange : W.target ⟶ V.target
  lowerAug : V.lower.comp lower = W.lower
  upperBase : upper.comp MvPolynomial.C = MvPolynomial.C.comp lower.toRingHom
  upperAug : V.augmentation.comp upper = W.augmentation
  baseSquare : baseChange.val.toRingHom.comp W.specialize = V.specialize.comp upper

/-- The ordinary category of compatible presentation pairs, before taking opposites.
Source: Stacks 08QR/08QW (blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable instance pairCategory : SmallCategory (Pair I A B C) where
  Hom := PairHom I A B C
  id W :=
    { lower := AlgHom.id A _
      upper := RingHom.id _
      baseChange := 𝟙 W.target
      lowerAug := by ext; rfl
      upperBase := RingHom.ext (fun _ ↦ rfl)
      upperAug := RingHom.ext (fun _ ↦ rfl)
      baseSquare := RingHom.ext (fun _ ↦ rfl) }
  comp f g :=
    { lower := g.lower.comp f.lower
      upper := g.upper.comp f.upper
      baseChange := f.baseChange ≫ g.baseChange
      lowerAug := by rw [← AlgHom.comp_assoc, g.lowerAug, f.lowerAug]
      upperBase := by
        rw [RingHom.comp_assoc, f.upperBase, ← RingHom.comp_assoc, g.upperBase]
        rfl
      upperAug := by rw [← RingHom.comp_assoc, g.upperAug, f.upperAug]
      baseSquare := by
        change (g.baseChange.val.toRingHom.comp f.baseChange.val.toRingHom).comp _ = _
        rw [RingHom.comp_assoc, f.baseSquare, ← RingHom.comp_assoc, g.baseSquare]
        rfl }
  id_comp f := by ext <;> rfl
  comp_id f := by ext <;> rfl
  assoc f g h := by ext <;> rfl

/-- Base change of a presentation pair. On morphisms this is the canonical coefficient
specialization, fixed by the commuting square in PairHom. Source: Stacks 08QR/08QW
(blueprint: def-trf-polynomial-presentation-arbitrary-target). -/
noncomputable def baseChange : Pair I A B C ⥤ Target I B C where
  obj W := W.target
  map f := f.baseChange

end Algebra.PolynomialPresentation.ArbitraryTarget
