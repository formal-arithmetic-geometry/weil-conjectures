/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseModels
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Coherence of the local perfect target model
Source: Stacks Project, Tags 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-picard-termwise-target-coherence) -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

variable [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
  (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

/-- The perfect target model has object comparisons compatible with the canonical
composition counit. This assertion involves no morphism out of a source single.
Source: Stacks Project, Tags 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-picard-termwise-target-coherence)

Proof:
1. Fix once the given representing isomorphism for E restricted to U. Transport K
   by the exact open-site equivalence. The equivalence preserves zero terms and
   finite-free retracts, so the resulting complex is bounded above and flat in
   every degree. It is therefore K-flat.
2. Identify derived pullback along the open immersion with exact open restriction,
   followed by the open-site equivalence. Pull back the representing isomorphism
   along s and compose with the K-flat counit at the transported complex. Precompose
   with the inverse derived composition comparison for s followed by U.ι, and
   transport along hf. These are the b_(t,s,hf).
3. Substitute these composites in the displayed equation. Associativity of the
   canonical derived composition isomorphisms identifies the two paths through
   the open immersion. The defining counit equation for composition, evaluated at
   the transported K-flat model, identifies the remaining paths with the termwise
   underived composition comparison. Naturality of the counit moves the fixed
   model isomorphism across the square. Equality transports hs, ht, hf and hf'
   agree by proof irrelevance. No vanishing in negative degrees is used; the
   calculation is unchanged for a zero model or an empty scheme. -/
theorem picard_termwise_target_coherence
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ≅
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (b t' s' hf').hom ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        c.inv.app E ≫ (derivedPullback i).map (b t s hf).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s) := by sorry

end
end AlgebraicGeometry.Scheme
