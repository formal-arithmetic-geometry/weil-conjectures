/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods
import Sheaf.AlgebraicGeometry.FiniteThickeningCartesian
import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.Paper.AlgebraizeFiniteOverProper
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-!
# Lifting finite étale covers over a complete Noetherian base

Source: Stacks Project, Fundamental Groups, Tag 0GS2, essential-surjectivity proof,
complete Noetherian case (blueprint: lem-weil-pbc-finite-etale-lifting-complete).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every finite étale cover of the closed fibre of a proper scheme over an `I`-adically
complete Noetherian ring lifts to a finite étale cover of the scheme.
Source: Stacks Project, Tag 0GS2, complete Noetherian essential-surjectivity paragraph
(blueprint: lem-weil-pbc-finite-etale-lifting-complete).

Proof:
1. Put `S_n = Spec (A / I^(n+1))` and `Y_n = Y ×_S S_n`. For `m ≤ n`, the quotient ideal
   defining `Y_m → Y_n` is nilpotent; this is a surjective closed immersion, hence a universal
   homeomorphism (lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-surjective-base-change,
   lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism).
2. Topological invariance lifts `V` inductively to étale schemes `V_n` over `Y_n` with
   cartesian transition squares (lemma-weil-pbc-universal-homeomorphism-site-equivalence).
3. Each `V_n → Y_n` is finite, since its restriction to the finite-order thickening `Y_0`
   is finite (lem-weil-pbc-thickening-finite-cartesian).
4. The morphism `V → Spec (A/I)` is proper: `Y_0` is proper by base change and `V → Y_0`
   is finite (lem-weil-pbc-proper-base-change, lem-weil-pbc-finite-morphism-permanence).
5. Algebraize the compatible finite morphisms to a finite `g : U → Y` with each restriction
   isomorphic to `V_n`; `U` is proper over `Spec A`
   (lem-weil-pbc-algebraize-finite-over-proper).
6. `Y` is locally Noetherian and `g` is of finite type. Since all infinitesimal restrictions
   are étale, `g` is étale on an open `W` containing the inverse image of `Y_0`
   (pqf-lem-locnoeth-lft, lem-weil-pbc-etale-infinitesimal-neighbourhoods).
7. For every `u : U`, the proper image of its closure is a nonempty closed subset of
   `Spec A`. Since `I` lies in the Jacobson radical, this image contains a maximal ideal
   containing `I` (lem-weil-pbc-adic-complete-jacobson-radical). Thus `u` specializes to
   a point over `Y_0`, which lies in `W`. Openness implies `u ∈ W`; hence `W = U`.
8. Consequently `g` is finite and étale, and its restriction is isomorphic to `V` over `Y_0`.
No additional henselian hypothesis is needed. -/
theorem Scheme.exists_finiteEtale_lift_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  sorry

end AlgebraicGeometry
