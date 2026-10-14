/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Local comparison factors

Source: Stacks Project, perfect.tex, Tags 0DJ7 and 0DJ9;
cohomology.tex, Tags 06YB and 0D5S.
(blueprint: lem-pc-standard-single-open-stalk-arrow).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Restriction of the canonical single-module base-change arrow to target opens,
then transport of its stalk back to the original local ring.

Proof: restrict the base direct image to S and the base-changed direct image to V.
Direct image commutes with restriction to a full inverse-image open: identify the
underived section functors, and derive that identification using exact restriction.
The pullback square over V identifies the restricted source with the pullback over
S. The tensor-pullback composition isomorphism identifies the restricted coefficient
module with the pullback of MS. Derived pullback commutes with these restrictions,
by the exact open pullback and its composition comparison. The base-change arrow
is the unit followed by direct image of the coefficient map followed by the counit.
The existing restricted_base_change_compatibility theorem applies to the pinned
single-module comparisons: the adjunction comparison and its inverse cancel,
identifying these comparisons with picardTermwiseSingleMap. It gives conjugacy
of the two derived arrows, before applying homology. Apply degree-n homology and
use exactness of open restriction to pass to restricted cohomology sheaves. Taking
the stalk at xV, the open-immersion stalk isomorphism and restriction of scalars
along its inverse identify these stalks with the original stalk at a. Composing
these identifications gives s, t and the displayed equality. This does not use
flatness, quasi-coherence, affineness, or a representative complex. Empty V admits
no a with hV; for top opens the same comparisons reduce to the identity.
Source: Stacks Project, perfect.tex, equation-bc (Tag 0DJ7), and
Lemma lemma-single-complex-base-change (Tag 0DJ9), locality paragraph.
(blueprint: lem-pc-standard-single-open-stalk-arrow). -/
theorem standardSingle_open_stalk_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hV : a ∈ V) (hVS : V ≤ g ⁻¹ᵁ S) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let xV : V.toScheme := ⟨a, hV⟩
    let F := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace xV ⋙
      ModuleCat.restrictScalars (V.stalkIso xV).inv.hom
    let pS := p ∣_ S
    let MS := M.restrict (p ⁻¹ᵁ S).ι
    let j := g.resLE S V hVS
    ∀ n : ℤ,
      ∃ (s : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
          ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
          F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((derivedPullback j).obj ((schemeDerivedDirectImage pS).obj
              ((DerivedCategory.singleFunctor _ 0).obj MS)))))
        (t : F.obj ((DerivedCategory.homologyFunctor _ n).obj
            ((schemeDerivedDirectImage (pullback.snd pS j)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (Scheme.Modules.tensorPullbackObj (pullback.fst pS j) MS)))) ≅
          (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
            ((DerivedCategory.homologyFunctor _ n).obj
              ((schemeDerivedDirectImage (pullback.snd p g)).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
        (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
            ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
          s.hom ≫ F.map ((DerivedCategory.homologyFunctor _ n).map
            (standardSingleBaseChangeMap pS MS j)) ≫ t.hom := by sorry

end AlgebraicGeometry
