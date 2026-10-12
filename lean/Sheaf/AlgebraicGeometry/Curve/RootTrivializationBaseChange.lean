/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Primitive-root trivializations commute with field extension

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, compatible primitive-root trivializations
(blueprint: lem-sc-root-trivialization-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
proof of thm-sc-constant-invariance, compatible primitive roots in the proper case
(blueprint: lem-sc-root-trivialization-base-change).

Proof: compose both sides with the inclusion of roots of unity into Gm. The defining
commutative square of φ replaces its first component by the units comparison after the
pulled-back inclusion. The original trivialization sends a locally constant class a to
ζ^a. Pullback of units preserves powers and sends ζ to algebraMap k K ζ, so both composites
send a to (algebraMap k K ζ)^a. This equality can be checked on constant presheaf sections,
because the constant sheaf is their sheafification and pullback commutes with sheafification.
The roots-of-unity inclusion is a monomorphism, so cancel it. No smoothness, connectedness,
properness or algebraic closedness is needed for this identity. For n = 1 the constant and
roots-of-unity sheaves are zero and the identity still holds. -/
theorem constant_root_trivialization_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (n : ℕ) [NeZero n]
    (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (hζK : IsPrimitiveRoot (algebraMap k K ζ) n)
    (φ : ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).mapShortComplex.obj
        (C.kummerSequence n)) ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerSequence n)
    (hφ : φ.τ₂ = upperStarGmSheafToGmSheaf
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map
        (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom ≫ φ.τ₁ =
      (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) ≫
      ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZModIsoRootsOfUnitySheaf n
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom := by sorry

end AlgebraicGeometry
