/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGloballyGenerated
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Global generation detected on geometric stalks

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary` (blueprint: lem-kun-global-generated-stalkwise);
Stacks Project, Tags 03DA, 010B, 010C, 03PT and 03PU.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Global generation of an étale sheaf of modules is equivalent to surjectivity
on every geometric stalk.

The evaluation morphism is the one from
`AlgebraicGeometry.Scheme.etaleGlobalSectionsEvaluation`; a geometric stalk is
the `pointSmallEtale` sheaf fibre, as in `def-weil-pbc-geometric-stalks`.
Proof, following the three steps of the node:
1. Form the cokernel `C` of the evaluation map `e`. By
`lem-weil-pbc-module-sheaves-colimits-forgetful`, forgetting scalars preserves this
cokernel and detects zero objects: a sheaf of modules is zero precisely when all
its underlying section groups are trivial. The criterion
`lem-weil-pbc-preadditive-epi-iff-cokernel-zero` identifies global generation with
the vanishing of the underlying abelian sheaf of `C`.
2. By `prop-weil-pbc-geometric-stalks-exact`, its stalk at a geometric point is the
cokernel of the underlying evaluation stalk map. Forgetting scalars does not change
the germs or their equality relation: the map sends a germ represented by a local
section `a` to the germ represented by `e(a)` in both categories. A module map is
surjective precisely when its underlying group map is surjective, equivalently
when this group cokernel is zero.
3. Apply `lemma-weil-pbc-geometric-stalk-conservative` to the map from the underlying
abelian sheaf of `C` to zero. The zero sheaf has zero stalks, so this map is an
isomorphism precisely when all these cokernel stalks vanish. Combining the three
equivalences proves both implications. For the recorded conservative family at
coefficient universe `u + 1`, `uliftSheafFiberIso` identifies the lifted fibres
with the unlifted `pointSmallEtale` fibres used here.
Source: Stacks Project, Tags 03DA, 010B, 010C, 03PT and 03PU; blueprint proof of
`lem-kun-global-generated-stalkwise` (blueprint: lem-kun-global-generated-stalkwise).
-/
theorem isGloballyGeneratedEtaleSheaf_iff_geometricStalk_surjective
    {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsGloballyGeneratedEtaleSheaf F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ T),
        Function.Surjective
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} Λ)).map
            (etaleGlobalSectionsEvaluation F)) := by
  sorry

end AlgebraicGeometry.Scheme
