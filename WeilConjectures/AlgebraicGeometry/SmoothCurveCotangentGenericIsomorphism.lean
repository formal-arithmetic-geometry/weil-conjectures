/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic

/-!
# Cotangent line bundles on smooth integral curves

Source: Stacks Project, curves.tex, Tag 0C1C, first paragraph of the proof of
`lemma-generically-etale`; morphisms.tex, Tags 02G1 and 02G2.
(blueprint: lem-a1-smooth-curve-cotangent-generic-isomorphism).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Cotangent sheaves on smooth integral curves are line bundles, and a morphism between
these line bundles is nonzero exactly when its generic stalk is nonzero, or equivalently
when it is invertible on some nonempty affine open. Restricted cotangent stalks are
nonzero free modules of rank one over the original local ring, using restriction of
scalars along the canonical open-immersion stalk map.

Source: Stacks Project, curves.tex, Tag 0C1C, first paragraph of the proof of
`lemma-generically-etale`; morphisms.tex, Tags 02G1, 02G2; varieties.tex, Tag 0A21;
properties.tex, Tag 01ON; schemes.tex, Tags 01HZ, 01I3, 01IT.
(blueprint: lem-a1-smooth-curve-cotangent-generic-isomorphism).

Proof:
1. A curve is integral and finite type of dimension one. By 0A21 every nonempty open,
   hence every nonempty affine open, has dimension one, as does the scheme at each point.
   The only fibre over the field is the curve itself, so the smooth structure morphism
   has relative dimension one, in the sense of 02G2.
2. By 02G1 the two cotangent sheaves are locally free of rank one. Pullback preserves
   invertibility (01C8), so the tensor pullback of the target cotangent sheaf is also
   locally free of rank one. This uses no dominance or nonconstancy of the map.
3. Trivialize both bundles on a common open. A module morphism is multiplication by a
   unique section a, and its restrictions multiply by the restrictions of a. Functions
   on a nonempty open of an integral scheme inject into the generic stalk (01ON).
   Thus a vanishes if its generic germ vanishes. The sheaf axiom then detects the zero
   morphism on a trivializing cover. This proves the first equivalence.
4. A nonzero generic germ is a unit in the function field. Its unit locus is an open
   neighbourhood of the generic point (01HZ). In the same generators multiplication
   by the inverse is a two-sided inverse to the morphism there. Choose an affine chart
   at the generic point and a principal affine open inside that neighbourhood (01IT,
   01I3). This yields the nonempty affine open required for the forward implication.
5. Conversely every nonempty open contains the generic point (01ON). An inverse on
   such an open induces an inverse on the generic stalk. A zero map cannot be invertible
   between rank-one modules over the nonzero generic field. This proves the reverse
   implication and hence the three-way equivalence.
6. At any point of any nonempty open, a local trivialization identifies the restricted
   cotangent stalk with the local ring of that open. The canonical stalk ring map for
   the open immersion is an isomorphism, so restriction of scalars identifies it with
   the original local ring. Its unit is a one-element basis. The integral scheme's
   local rings are nonzero domains (01ON), so the stalk module is nonzero as well.
-/
theorem smoothCurve_cotangent_generic_isomorphism
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsIntegralCurve f] [IsIntegralCurve g] [Smooth f] [Smooth g]
    (h : X ⟶ Y) (_hh : h ≫ g = f) :
    (∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
      topologicalKrullDim U = 1) ∧
    (∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim U = 1) ∧
    SmoothOfRelativeDimension 1 f ∧ SmoothOfRelativeDimension 1 g ∧
    ((Scheme.Modules.tensorPullback h).obj g.relativeDifferentials).IsInvertible ∧
    f.relativeDifferentials.IsInvertible ∧
    (∀ (η : X), IsGenericPoint η (Set.univ : Set X) →
      ∀ a : (Scheme.Modules.tensorPullback h).obj g.relativeDifferentials ⟶
          f.relativeDifferentials,
        (a ≠ 0 ↔ (RingedSpace.moduleStalkFunctor X.toRingedSpace η).map a ≠ 0) ∧
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace η).map a ≠ 0 ↔
          ∃ V : X.Opens, IsAffineOpen V ∧ (V : Set X).Nonempty ∧
            IsIso ((Scheme.Modules.restrictFunctor V.ι).map a))) ∧
    (∀ W : X.Opens, (W : Set X).Nonempty → ∀ x : W.toScheme,
      Nontrivial ((ModuleCat.restrictScalars (W.ι.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor W.ι).obj f.relativeDifferentials))) ∧
      Nonempty (Module.Basis (Fin 1) (X.presheaf.stalk (W.ι x))
        ((ModuleCat.restrictScalars (W.ι.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace x).obj
            ((Scheme.Modules.restrictFunctor W.ι).obj f.relativeDifferentials))))) := by
  sorry

end AlgebraicGeometry
