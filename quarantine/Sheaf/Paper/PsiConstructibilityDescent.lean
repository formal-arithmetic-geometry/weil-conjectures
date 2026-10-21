/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.OrientedConstructibleSheafVanishing
public import Sheaf.Paper.OrientedNearbyCycles
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.CategoryTheory.Sites.CoherentConservativeReflection
import Sheaf.Paper.OrientedConstructibleCoherent
import Sheaf.TraceFormula.ProperBaseChangeCoherentConservative

/-!
# Proper-surjective descent of constructibility on a vanishing topos

Source: Orgogozo, “Modifications et cycles proches sur une base générale”, Lemma 9.1.5,
printed p. 21 (published as Lemma 10.5 and cited in Lu--Zheng, proof of Theorem 4.27(2));
(blueprint: lem-trf-psi-constructibility-descent).

The constructibility predicate is the vanishing-topos specialization recorded in
`OrientedConstructibleSheaf.IsConstructibleVanishing`.  The induced inverse image is
the canonical square module pullback from `OrientedNearbyCycles`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles
open AlgebraicGeometry.OrientedConstructibleSheaf

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- Constructibility descends along a proper surjective change of the base.
Source: Orgogozo, “Modifications et cycles proches sur une base générale”, Lemma 9.1.5,
printed p. 21; published Lemma 10.5 (blueprint: lem-trf-psi-constructibility-descent).

Proof plan, following the node's four steps:
1. Apply lem-trf-proper-base-change-coherent-conservative to the proper surjective p.
   The Noetherian base and finite-presentation f give coherent topoi E = V_f and
   E' = V_{f_T}, and the induced morphism is coherent and conservative. Properness
   also gives a Noetherian T, and finite presentation is stable under base change.
2. Let A be the underlying sheaf of sets of F. By def-trf-oriented-nearby-cycles,
   constant-coefficient module inverse image is exact and its underlying sheaf is v⁻¹A.
   Apply lem-trf-oriented-constructible-coherent to f_T and v*F: the hypothesis says
   v⁻¹A is a coherent object, with the same finite coefficient ring.
3. Apply lem-trf-coherent-conservative-reflection to v and A. Step 1 supplies coherence
   and conservativity, while step 2 supplies coherence of v⁻¹A; hence A is coherent.
4. Apply the reverse implication of lem-trf-oriented-constructible-coherent to f and F.
   This gives finite constructible strata on X and S with locally constant finite
   module values on each oriented stratum, exactly the conclusion.
-/
theorem constructibility_descent {X S T : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (p : T ⟶ S) [IsProper p] [Surjective p]
    (F : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ))
    (_hF : IsConstructibleVanishing (pullback.snd f p) Λ
      (((squareModules f (pullback.snd f p) (pullback.fst f p) p
        (pullback.condition (f := f) (g := p))).modulePull
          (Coeff.{u, v} Λ)).obj F)) :
    IsConstructibleVanishing f Λ F := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
