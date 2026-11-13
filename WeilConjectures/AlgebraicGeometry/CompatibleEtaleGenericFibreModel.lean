/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.AlgebraicGeometry.EtaleGenericResidueFieldModel

/-! # A compatible étale generic-fibre model

Stacks Project, Tags 0551 and 055G.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Spread a specified finite étale generic field extension with compatible fibres
(Stacks, Tags 0551 and 055G). -/
theorem exists_compatible_etale_generic_fibre_model {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S)
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (a : pullback (f.fiberToSpecResidueField (genericPoint S)) yη ⟶ pullback f g),
      Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧
      IsEmbedding a ∧ Set.range a = (pullback.snd f g) ⁻¹' {η} ∧
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField η))),
        ∃ (zL : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L))
          (e : pullback ((pullback.snd f g).fiberToSpecResidueField η) z ≅
            pullback (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) zL),
          e.hom ≫ pullback.fst _ zL ≫ a =
            pullback.fst _ z ≫ (pullback.snd f g).fiberι η := by
  obtain ⟨T, g, η, r, hg, hη, hgη, hr⟩ :=
    exists_etale_generic_residue_field_model yη
  let s := S.fromSpecResidueField (genericPoint S)
  let t := T.fromSpecResidueField η
  have hr' : yη ≫ s = r.inv ≫ t ≫ g := by
    rw [← hr]
    simp [s]
  let b : pullback f (yη ≫ s) ≅ pullback f (t ≫ g) :=
    asIso (pullback.map _ _ _ _ (𝟙 X) r.inv (𝟙 S) (by simp)
      (by simpa [Category.assoc] using hr'))
  let q : pullback (f.fiberToSpecResidueField (genericPoint S)) yη ≅
      (pullback.snd f g).fiber η :=
    pullbackLeftPullbackSndIso f s yη ≪≫ b ≪≫
      (pullbackLeftPullbackSndIso f g t).symm
  have hq : q.hom ≫ (pullback.snd f g).fiberToSpecResidueField η =
      pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη ≫ r.inv := by
    change q.hom ≫ pullback.snd (pullback.snd f g) t =
      pullback.snd (pullback.snd f s) yη ≫ r.inv
    simp [q, b]
  let a := q.hom ≫ (pullback.snd f g).fiberι η
  refine ⟨T, g, η, a, hg, hη, hgη, ?_, ?_, ?_⟩
  · exact (pullback.snd f g).fiberι η |>.isEmbedding |>.comp q.hom.isEmbedding
  · change Set.range (q.hom ≫ (pullback.snd f g).fiberι η) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      q.hom.surjective.range_eq, Set.image_univ]
    exact (pullback.snd f g).range_fiberι η
  · intro E _ z
    let zL := z ≫ r.hom
    have hqi : (pullback.snd f g).fiberToSpecResidueField η ≫ r.hom =
        q.inv ≫ pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη := by
      rw [← cancel_epi q.hom]
      rw [← Category.assoc, hq]
      simp
    let e : pullback ((pullback.snd f g).fiberToSpecResidueField η) z ≅
        pullback (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) zL :=
      asIso (pullback.map _ _ _ _ q.inv (𝟙 _) r.hom hqi (by simp [zL]))
    refine ⟨zL, e, ?_⟩
    simp [e, a, Category.assoc]


end AlgebraicGeometry
