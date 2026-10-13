/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Stalkwise conjugacy for transported open coordinates.

Source: Stacks Project, perfect.tex, Tag 0DJ9, localization calculation.
(blueprint: lem-pc-single-complex-open-coordinate-stalk-equivalence)

The proof is the termwise stalk calculation: open-immersion stalk isomorphisms
identify the four local rings and complexes, and naturality of tensor extension,
homology, and the representing map conjugates the two comparison arrows.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The restricted and original stalk comparison arrows are isomorphic after
forgetting scalars, for any coordinates of the canonical restricted coefficient.
No invertibility of either comparison is assumed.

Proof: Write U=f⁻¹V and U'=f'⁻¹V'. At z the four open-immersion stalk maps
for U, U', V, V' are invertible. The point equalities follow from hj and the
restriction squares. Transport the four local rings along these stalk maps.
The stalkMap_comp identity and sq.w identify the maps R→A, R→B, A→C and B→C.
The two restrictions of tensorMap then agree, so its tensor-product universal
property identifies both the tensor algebra A⊗_R B and its action on C.

Exact stalks applied to c.e and d.e, together with the restriction-stalk
extension comparison, identify the derived stalks of c.P and d.P after this
ring transport: both represent the stalk of K at g'(z.val). Restriction and
extension along the stalk ring isomorphisms are inverse exact equivalences.
They transport the left-derived scalar-extension universal property. Its unique
counit-compatible isomorphism, followed by the model cohomologyIso, identifies
the base-derived tensor cohomology objects. The cohomologyIso_smul equations
identify multiplication by A; tensor-product induction lifts this identification
from B-linearity to A⊗_R B-linearity. Extend it to C and forget scalars to obtain
the source additive isomorphism. Exact stalks applied to c.e' and d.e' similarly
identify both target homologies with H^i(K') at z.val, giving the target isomorphism.

For commutativity, normalize both comparisons by these target identifications.
The represents equations replace each homology map of the chain map by the map
of the corresponding derived coefficient, after cancellation of its invertible
pullback counit. K-flatness of the stalk representatives follows from the stalk
criterion, so ordinary A→C extension computes their derived pullback. The
comparison_eq and localized_eq equations express the preceding tensor comparisons
by the universal derived counits and their extension/restriction transposes.
Naturality under the ring isomorphisms and derived representative isomorphisms
therefore identifies these normalized comparisons. The coefficient is exactly
singleComplexRestrictedCoefficient: its composition factors identify derived
pullback of the original coefficient with restricted pullback, and the
leftDerivedUnique factorization identity for singleComplexOpenPullbackIso makes
this identification compatible with the pinned counits. Consequently the source
and target isomorphisms give a commuting square for the two complete comparison
maps. Apply Arrow.isoMk. This argument constructs no extra coordinate system and
uses no flatness over R. Empty opens have no z; top opens, zero complexes, zero
rings and unbounded complexes obey the same identities.

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8 and
Tag 0DJ9, first paragraph; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-coordinate-stalk-equivalence). -/
theorem nonempty_singleComplexOpen_stalk_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (d : SingleComplexBaseChange.Coordinates j
      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)
      ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K')
      (singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj)) :
    ∀ (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ),
      Nonempty
        (Arrow.mk ((forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison
                (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i)) ≅
          Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i))) := by sorry

end AlgebraicGeometry
