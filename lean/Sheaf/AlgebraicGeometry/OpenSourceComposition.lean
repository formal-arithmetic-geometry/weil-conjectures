/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! Source-open normalization of compact-support composition. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Keep signature checking from unfolding the compactification and derived constructions.
attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor rightDerivedLowerShriekIso
  rightDerivedLowerShriekOfCompactificationIso unboundedEtaleLowerShriekCompIso

/-- Restricting the source open in a compactification computes the specified composition
comparison. This is the source-open specialization of the compact-support composition law.
Source: Stacks Project, More on Etale Cohomology, Tag 0F7J, the first two equalities in
Lemma `lemma-shriek-composition`, together with the identity normalization of the
proper/open comparison in Tag 0F7B
(blueprint: lem-amb-compact-support-open-source-composition).

Proof: write `c = (j,r)` and put `e = (w ≫ j,id)` and `d = (w,id)`.
Expand the canonical comparison by `unboundedEtaleLowerShriekCompIso_tower` with outer
compactification `c` and inner compactification `e`. The restricted compactification
`e.restrict` has ambient `c.Z ×[c.Z] X` and proper map the second projection, an
isomorphism. Identify this model with `d` by the canonical pullback unit. The refinement
comparison is the inverse open base-change comparison after the direct-image unit;
this follows by transposing under the open adjunction and cancelling its triangle
identities. The proper/open interchange for this identity-proper square cancels that
comparison. Compatibility of derived direct-image composition with its identity unit
cancels the remaining identity-proper factors. What remains is the inverse of the
canonical derived open-composition comparison for `w,j`, followed by the comparison
for `c.precomp w`. Naturality of the comparison for `c` moves it to the input, giving
the displayed formula. Common-refinement coherence transfers the calculation from these
models to the specified chosen compactifications. The pullback unit, open adjunction
units and direct-image identity unit also cover identity and empty opens. -/
theorem unboundedEtaleLowerShriekCompIso_open_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X S : Scheme.{u}} [IsNoetherian V] [IsNoetherian X] [IsNoetherian S]
    (w : V ⟶ X) (f : X ⟶ S) [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification w] [HasCompactification f] [HasCompactification (w ≫ f)]
    (c : Compactification f) :
    Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A w).symm
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A w f =
    Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) w).mapDerivedCategory
        (rightDerivedLowerShriekIso A c).symm ≪≫
      Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) w c.i).symm
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g) ≪≫
      rightDerivedLowerShriekIso A (c.precomp w) := by sorry

end AlgebraicGeometry.Etale
