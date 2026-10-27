/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Projective-bundle projectivity under arbitrary base change

Source: Stacks Project, Morphisms, Tag 02V6, lemma-base-change-projective;
Constructions, Tags 01OA and 01OB
(blueprint: lem-sfb-projective-bundle-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Projectivity in the finite-type quasi-coherent projective-bundle convention is
preserved by arbitrary base change. Neither base is assumed Noetherian, and the
bundle module need not be locally free.

Source: Stacks Project, Morphisms, Tag 02V6, lemma-base-change-projective;
Constructions, Tags 01OA and 01OB
(blueprint: lem-sfb-projective-bundle-base-change).

Proof:
1. Unpack `IsProjectiveBundle f` (def-trf-projective-bundle-morphism) to obtain a
   finite-type quasi-coherent module E and a closed immersion i into P(E) over S.
   Its pullback a*E is quasi-coherent and finite type, by
   lem-weil-pbc-module-pullback-quasi-coherent and
   lem-weil-pbc-module-pullback-finite-type, using def-pc-module-pullback.
2. Put Q = P(E) times_S S'. Pull the universal quotient on P(E) back to Q.
   The composition comparison for module pullbacks identifies it with a line
   quotient of the pullback of a*E, giving b : Q to P(a*E) over S'. Conversely
   the universal quotient on P(a*E) gives c : P(a*E) to P(E) over S, and its
   pair with the structural map gives t : P(a*E) to Q. These constructions use
   lem-trf-projective-bundle-quotient-geometry and def-pc-fibre-product.
3. The quotient classified by b composed with t is the original universal
   quotient, so uniqueness in the quotient classification gives b t = id.
   Also c b and the structural map composed with b are the two projections
   of Q. The fibre-product universal property therefore gives t b = id.
   Thus b identifies Q with P(a*E) over S'.
4. The induced map j : X times_S S' to Q is a base change of i by the
   fibre-product universal property. It is a closed immersion by
   lem-weil-pbc-closed-immersion-base-change. Composing with the isomorphism b
   preserves closed immersions (def-weil-closed-immersion).
5. The composite b j is over S', and a*E is finite type and quasi-coherent.
   This is precisely the witness required by def-trf-projective-bundle-morphism.
-/
theorem isProjectiveBundle_pullback_snd {X S S' : Scheme.{u}}
    (f : X ⟶ S) (a : S' ⟶ S) (hf : IsProjectiveBundle f) :
    IsProjectiveBundle (pullback.snd f a) := by
  sorry

end AlgebraicGeometry
