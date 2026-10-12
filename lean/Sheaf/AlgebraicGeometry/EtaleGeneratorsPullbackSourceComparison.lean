/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # EtaleGeneratorsPullbackSourceComparison

Source: Stacks Project, Tags 0097 and 040E.
(blueprint: lem-sc-etale-generators-pullback-source-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-source-comparison) -/
noncomputable def etaleGeneratorsPullbackSourceIso {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Etale) :
    (pullback (Limits.pullback.snd W.hom f)).obj (unit Y) ≅
      (pullback (Limits.pullback.fst W.hom f)).obj ((pullback W.hom).obj (unit X)) :=
  pullbackObjUnitIso (Limits.pullback.snd W.hom f) ≪≫
    (pullbackObjUnitIso (Limits.pullback.fst W.hom f)).symm ≪≫
    (pullback (Limits.pullback.fst W.hom f)).mapIso (pullbackObjUnitIso W.hom).symm

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-source-comparison) -/
noncomputable def etaleGeneratorsPullbackSquareIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {V W : X.Etale} (i : V ⟶ W) (M : W.left.Modules) :
    (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).obj
      ((pullback (Limits.pullback.fst W.hom f)).obj M) ≅
      (pullback (Limits.pullback.fst V.hom f)).obj ((pullback i.left).obj M) :=
  let j := ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
  let hp : j ≫ Limits.pullback.fst W.hom f =
      Limits.pullback.fst V.hom f ≫ i.left := by
    simp [j, MorphismProperty.Over.pullback_map_left]
  (((pullbackComp j (Limits.pullback.fst W.hom f)) ≪≫ pullbackCongr hp) ≪≫
    (pullbackComp (Limits.pullback.fst V.hom f) i.left).symm).app M

/-- The source comparison commutes with etale restriction.
Source: Stacks Project, Tag 0097, Lemma 6.26.3; Tag 040E, Lemma 21.6.1.
(blueprint: lem-sc-etale-generators-pullback-source-comparison)

Proof: Expand the source factor as U(q) followed by the inverse of U(p) and the pullback of the
inverse of U(W), where U(a) is the canonical structure-module comparison. For composable a,b
with composite h, c(a,b;h).hom followed by U(h) equals a*U(b) followed by U(a): applying the
pullback adjunction identifies both maps with the composite structure-sheaf ring map. This
proves the unit-comparison composition law, also for equal composites. Apply it to j,q_W,q_V and
to the two paths j,p_W and p_V,i. Associativity of the canonical pullback comparisons identifies
those paths since j followed by p_W equals p_V followed by i. Apply the same unit-comparison law
to i,W,V. Substitute these three identities into the expanded left side, cancel adjacent
comparison isomorphisms, and obtain the right side. No generator, coefficient module, or
invertibility is used; empty schemes and zero rings satisfy the same adjunction identities.
-/
theorem etaleGeneratorsPullbackSource_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {V W : X.Etale} (i : V ⟶ W) :
    (pullbackCompOfEq ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
      (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w (unit Y)).inv ≫ (pullback
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
        (etaleGeneratorsPullbackSourceIso f W).hom ≫
      (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj (unit X))).hom =
      (etaleGeneratorsPullbackSourceIso f V).hom ≫
        (pullback (Limits.pullback.fst V.hom f)).map (pullbackCompOfEq i.left W.hom V.hom i.w
          (unit X)).inv := by
  sorry

end AlgebraicGeometry.Scheme.Modules
