/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.CoefficientRingedSequenceSite

/-! # Restriction on a finite evaluation of a strict coefficient system

The underlying restriction map is the restriction of the sequence presheaf along
its vertical arrow. No property of transitions is required.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf

universe t u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] coefficientSequenceCommRingSystem integralCoefficientCommRingSheaf

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite evaluation retains the vertical restriction map of the whole system.
Source: the sequence-site construction and the inverse-image section coordinates;
blueprint integral transport proof, coefficient and unit compatibility
(blueprint: lem-trf-point-restriction-sequence-evaluation).
Proof: coefficientSequenceEvaluation is pushforward along U ↦ (n,U), with only
its scalar structure transported. Its underlying presheaf map on the restriction
arrow is therefore the map of the original presheaf on (id_n, alpha_g).
pointRestrictionRaw is exactly this underlying restriction map. Both sides are
thus definitionally equal. This applies to zero systems and arbitrary transitions,
and also to g=id; no exactness, characteristic or constructibility is used. -/
theorem pointRestrictionRaw_coefficientSequenceEvaluation
    {S : Scheme.{t}} (g : S ⟶ S) [IsIso g] (n : ℕ)
    (P : coefficientSequenceModules l E S) :
    (fun y : P.val.obj (op (n, ProEt.mk (𝟙 S))) ↦
      pointRestrictionRaw l E g (some n)
        ((coefficientSequenceEvaluation l E S n).obj P) y) =
    (fun y ↦ P.val.map (Prod.mkHom (𝟙 n) (pointRestrictionArrow g)).op y) := by
  have h := SheafOfModules.forget₂_map_pushforward_obj_val_map
    (eqToHom (coefficientSequenceEvaluationRing_eq l E S n).symm)
    (pointRestrictionArrow g).op P
  exact congrArg (fun f ↦ fun y ↦ f.hom y) h

end WeilConjectures
