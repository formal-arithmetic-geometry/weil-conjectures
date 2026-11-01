/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerDerivedPullback
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.NativeReductionPullbackRepresentative

/-!
# Composition for normalized proper reduction

The normalized pullback comparisons must be chosen coherently for composition.
This is the categorical part of the native proper direct-image argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Normalized reduction/pullback squares paste compatibly with the two fixed
pullback compositors, in the ordinary derived category of systems.
Source: the normalized scalar/pullback construction in the current blueprint
integral-adjunction direct-image proof, paragraphs (2)--(3), and the parent node's
composition compatibility subargument.
(blueprint: lem-dla1-native-reduction-proper-composition).

Proof: fix composable f and g. Paste their ordinary scalar/pullback isomorphisms
using the integral inverse-image compositor and the recorded system compositor.
Its finite evaluations send 1 tensor the inverse image of x to the inverse image of
1 tensor x, by the generator equations for the two factors and the normalized finite
geometric units. The system compositor has the same normalization: comp_termwise and
comp_evaluation identify it after the fully faithful degree-zero embedding, and
ordinary evaluation is jointly faithful on sequence-site sheaf maps. Thus the pasted
ordinary comparison satisfies the tensor-generator equation for f composed with g.

Paste the two derived comparisons using the fixed integral and system derived
compositors. Resolve by a flat-term K-flat complex. Geometric inverse image preserves
both flat terms and K-flatness. Apply the two representatives equations, naturality of
the universal reduction counit, and the termwise formula for the system compositor.
The resulting pasted comparison satisfies the representatives equation for the ordinary
comparison just constructed. Uniqueness of the normalized ReductionPull for the fixed
evaluation q.evaluation identifies it with q.pullback of the composite. Invert this
identity and reassociate the functors. Whiskering by the inverse system compositor
and the inverse integral compositor yields exactly the displayed TwoSquare equation.
This argument works for any given normalized q. There are no properness, finiteness,
field-characteristic, or boundedness assumptions; identity maps, isomorphisms, empty
schemes and zero objects obey the same generator and representative equations. -/
theorem nativeReductionPullbackComposition (s : Presentation l E)
    (q : ReductionGeometry l E s) :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
          (s.operations.comp f g).inv).whiskerLeft
            (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv =
        TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv := by
  intro X Y Z f g
  apply TwoSquare.ext _ _
  intro K
  exact nativeReductionPullbackComposition_component l E s q
    (fun f g P hP hflat ↦
      nativeReductionPullbackComposition_representative l E s q f g P hP hflat) f g K

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
