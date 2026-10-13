/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Natural affine comparison for coherent completion

Source: Stacks Project, Lemmas 087W and 0881, affine identification of quotient systems.
(blueprint: lem-weil-pbc-formal-completion-affine-natural-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine formal-module realization identifies completion with adic completion
of affine sections, naturally for every coherent module map. No exact sequence is assumed.

Source: Stacks Project, Lemma 087W and the affine identification in Lemma 0881.
(blueprint: lem-weil-pbc-formal-completion-affine-natural-comparison).

Proof:
1. Set A = Gamma(X,U) and J = I(U). Identify U with Spec A by its canonical affine
isomorphism. The restricted ideal corresponds to J by the affine ideal dictionary.
Transport coherent formal modules along this isomorphism and apply the equivalence
of Lemma 087W. Compose its functor with the full finite-module inclusion and scalar
restriction from the J-adic completion to A; call the resulting functor F.
2. The equivalences and full inclusion reflect limits. Scalar restriction preserves
limits and reflects isomorphisms, and therefore reflects limits since its source has
limits. Their composite reflects parallel-pair limits. Naturality of the specified
limit cones, evaluated on quotient projections, proves that F preserves zero maps.
3. Open restriction preserves ideal products and their powers, and quotient cokernels.
Affine sections of the restricted positive-power quotient system of G are thus
Gamma(G,U)/J^(n+1)Gamma(G,U), with transitions the canonical quotient reductions.
The equation hρ identifies this system with the underlying system of ρ(completion G).
4. The limit cones of Lemma 087W identify F(ρ(completion G)) with the limit of these
quotients. Adjoining the initial zero quotient identifies this with Mathlib's adic
completion. The unique limit isomorphisms are A-linear. Evaluate on every quotient
projection to prove naturality for a coherent map f: both composites reduce f on each
level, so the jointly monomorphic limit projections give the displayed equality.
For J = 0 the system is constant; for J = A it is zero. The empty affine open and
zero modules are covered by the same limit argument.
-/
theorem formalCompletion_affine_natural_comparison
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι)) :
    ∃ F : CoherentFormalModule U.toScheme (I.comap U.ι) ⥤ ModuleCat.{u} Γ(X, U),
      F.PreservesZeroMorphisms ∧ ReflectsLimitsOfShape WalkingParallelPair F ∧
      ∃ e : ∀ G : CoherentModules X,
        F.obj (ρ.obj ((completion X I).obj G)) ≃ₗ[Γ(X, U)]
          AdicCompletion (I.ideal ⟨U, hU⟩) Γ(G.obj, U),
        ∀ (G H : CoherentModules X) (f : G ⟶ H) (x),
          e H ((F.map (ρ.map ((completion X I).map f))) x) =
            AdicCompletion.map (I.ideal ⟨U, hU⟩) (f.hom.val.app (op U)).hom (e G x) := by sorry

end AlgebraicGeometry
