/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Affine comparison of the completed arrows

Source: Stacks Project, Lemma 0881, affine identification in its proof, and Lemma 087W.
(blueprint: lem-weil-pbc-formal-completion-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The restricted completed arrows identify with adic completions of an original
short exact module sequence. This is a comparison statement: it asserts neither
injectivity nor exactness of the completed maps.

Source: Stacks Project, Lemma 0881, the affine identification in its proof;
Lemma 087W; Algebra, Lemma 00MB (2) supplies the subsequent exactness argument.
(blueprint: lem-weil-pbc-formal-completion-affine-comparison).

Proof:
1. Take A to be the ring of sections on U, and J the sections of I on U. The affine
open of a Noetherian scheme has a Noetherian ring of sections. Restrict S and take
sections. The coherent inclusion preserves kernels and cokernels, open restriction
is exact, and affine sections on quasi-coherent modules are exact. Thus the resulting
module short complex M is short exact. Coherence gives finite sections, in particular
Module.Finite A M.X₂.
2. Identify U.toScheme with Spec A by its canonical affine isomorphism. Transport
formal systems along this isomorphism and use the equivalence of Lemma 087W. Compose
its functor with the finite-module inclusion and restriction of scalars from the
completed ring to A, obtaining F. Each constituent preserves zero morphisms.
The equivalence and full inclusion reflect limits. Scalar restriction creates limits
and reflects isomorphisms, hence reflects limits. Their composite therefore reflects
limits of parallel pairs, without any assertion that formal kernels are termwise.
3. Open restriction commutes with ideal products and their positive powers, and with
quotient cokernels. Affine sections identify these quotients with Mᵢ/J^(n+1)Mᵢ and
identify the induced maps with reductions of M.f and M.g. The equality hρ identifies
these very systems with the underlying systems of V.
4. The natural limiting cones in the affine equivalence identify F.obj V.Xᵢ with
AdicCompletion J M.Xᵢ. Mathlib indexes all nonnegative powers; deleting the initial
zero quotient is cofinal and gives the same limit. Uniqueness of the limit comparison
gives A-linear equivalences eᵢ. Naturality of the cones, checked on every quotient
projection, gives the two displayed equations on arrows.
For J = 0 these are the original modules; for J = A all completions are zero.
Empty affine opens give the zero ring, and zero modules cause no exceptional case.
-/
theorem formalCompletion_affine_comparison (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (h : (completion X I).Additive)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hz : ρ.PreservesZeroMorphisms)
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι))
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
    let V := @ShortComplex.map _ _ _ _ _ _ T ρ hz
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (J : Ideal A)
      (M : ShortComplex (ModuleCat.{u} A)),
      Module.Finite A M.X₂ ∧ M.ShortExact ∧
      ∃ F : CoherentFormalModule U.toScheme (I.comap U.ι) ⥤ ModuleCat.{u} A,
        F.PreservesZeroMorphisms ∧ ReflectsLimitsOfShape WalkingParallelPair F ∧
        ∃ (e₁ : F.obj V.X₁ ≃ₗ[A] AdicCompletion J M.X₁)
          (e₂ : F.obj V.X₂ ≃ₗ[A] AdicCompletion J M.X₂)
          (e₃ : F.obj V.X₃ ≃ₗ[A] AdicCompletion J M.X₃),
          (∀ x, e₂ ((F.map V.f) x) = AdicCompletion.map J M.f.hom (e₁ x)) ∧
          (∀ x, e₃ ((F.map V.g) x) = AdicCompletion.map J M.g.hom (e₂ x)) := by sorry

end AlgebraicGeometry
