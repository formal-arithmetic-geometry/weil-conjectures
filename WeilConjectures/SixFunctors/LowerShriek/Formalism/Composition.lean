/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification

/-!
# The composition isomorphism in a compact support formalism

For a triangle of compactifications `T` of composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`
(`AlgebraicGeometry.Compactification.Triangle`) and a compact support formalism `F` satisfying
proper base change, this file constructs the composition isomorphism

`F.compIso T : F.shriek T.cf ⋙ F.shriek T.cg ≅ F.shriek T.cfg`

of blueprint `sk-thm-sf-comp-composition`: it is the exchange isomorphism
`(cg.i)_! (cf.g)_* ≅ p_* q_!` of the cartesian square of `T`, followed by the composition
isomorphisms `(cf.i)_! ⋙ q_! ≅ (cfg.i)_!` and `p_* ⋙ (cg.g)_* ≅ (cfg.g)_*`.

It is natural with respect to morphisms of triangles
(`AlgebraicGeometry.CompactSupportFormalism.compIso_naturality`): the comparison isomorphisms
along the refinements intertwine the composition isomorphisms.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

/-- The triangle of factorizations (`CategoryTheory.ExchangeFormalism.ShriekTriangle`)
underlying a triangle of compactifications. -/
abbrev _root_.AlgebraicGeometry.Compactification.Triangle.toShriekTriangle
    (T : Compactification.Triangle f g) :
    ExchangeFormalism.ShriekTriangle @IsOpenImmersion X Y S where
  Z₁ := T.cf.Z
  Z₂ := T.cg.Z
  W := T.cfg.Z
  i₁ := T.cf.i
  p₁ := T.cf.g
  i₂ := T.cg.i
  p₂ := T.cg.g
  i := T.cfg.i
  p := T.cfg.g
  q := T.q
  r := T.p
  i_q := T.i_q
  r_p := T.p_g
  w := T.isPullback.w

/-- The morphism of triangles of factorizations underlying a morphism of triangles of
compactifications. -/
abbrev _root_.AlgebraicGeometry.Compactification.Triangle.Hom.toShriekTriangleHom
    {T' T : Compactification.Triangle f g} (φ : T'.Hom T) :
    ExchangeFormalism.ShriekTriangle.Hom @IsOpenImmersion T'.toShriekTriangle
      T.toShriekTriangle where
  rf := φ.rf.hom
  rg := φ.rg.hom
  rfg := φ.rfg.hom
  wf := φ.isPullback_rf.flip.w
  hf := φ.rf.hom_g
  wg := φ.isPullback_rg.flip.w
  hg := φ.rg.hom_g
  wfg := φ.isPullback_rfg.flip.w
  hfg := φ.rfg.hom_g
  q_comm := φ.q_comm
  p_comm := φ.p_comm

variable (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]

/-- **The composition isomorphism** attached to a triangle of compactifications `T`:
```
(cf.i)_! ⋙ (cf.g)_* ⋙ (cg.i)_! ⋙ (cg.g)_* ≅ (cf.i)_! ⋙ q_! ⋙ p_* ⋙ (cg.g)_*
                                         ≅ (cfg.i)_! ⋙ (cfg.g)_*
```
built from the exchange isomorphism of the cartesian square `cf.g ≫ cg.i = q ≫ p`
(`CategoryTheory.ExchangeFormalism.compIso`).
(blueprint: `sk-thm-sf-comp-composition`) -/
noncomputable def compIso (T : Compactification.Triangle f g) :
    F.shriek T.cf ⋙ F.shriek T.cg ≅ F.shriek T.cfg :=
  haveI := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  haveI := HasProperExchange.isIso_exchange (F := F) T.isPullback
  ExchangeFormalism.compIso F T.toShriekTriangle

lemma compIso_hom_app (T : Compactification.Triangle f g) (K : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) T.isPullback
    (F.compIso T).hom.app K =
      (F.pf T.cg.g).map ((F.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans.app
          ((F.sh T.cf.i).obj K) ≫
        (F.pf T.p).map ((F.shComp' T.cf.i T.q T.cfg.i T.i_q).inv.app K)) ≫
      (F.pfComp' T.p T.cg.g T.cfg.g T.p_g).inv.app ((F.sh T.cfg.i).obj K) :=
  haveI := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  haveI := HasProperExchange.isIso_exchange (F := F) T.isPullback
  ExchangeFormalism.compIso_hom_app F T.toShriekTriangle K

/-- **Naturality of the composition isomorphism**: for a morphism of triangles `φ : T' ⟶ T`,
the comparisons along the refinements of `φ` intertwine the composition isomorphisms of `T` and
`T'`. (blueprint: `sk-thm-sf-comp-composition`, independence of the compactifications) -/
theorem compIso_naturality {T' T : Compactification.Triangle f g} (φ : T'.Hom T) :
    (F.compIso T).hom ≫ F.refinementComparison φ.rfg φ.isPullback_rfg =
      NatTrans.hcomp (F.refinementComparison φ.rf φ.isPullback_rf)
          (F.refinementComparison φ.rg φ.isPullback_rg) ≫ (F.compIso T').hom := by
  have := HasBaseChange.isIso_baseChange (F := F) T.isPullback
  have := HasProperExchange.isIso_exchange (F := F) T.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) T'.isPullback
  have := HasProperExchange.isIso_exchange (F := F) T'.isPullback
  have := HasBaseChange.isIso_baseChange (F := F) φ.isPullback_rf.flip
  have := HasBaseChange.isIso_baseChange (F := F) φ.isPullback_rg.flip
  have := HasBaseChange.isIso_baseChange (F := F) φ.isPullback_rfg.flip
  have := HasBaseChange.isIso_baseChange (F := F) φ.isPullback_q
  have := HasBaseChange.isIso_baseChange (F := F) φ.isPullback_big
  exact ExchangeFormalism.compIso_naturality F φ.toShriekTriangleHom

/-- **Independence of the triangle of compactifications**: the composition isomorphisms of two
triangles `T₁` and `T₂` agree up to the comparison isomorphisms `F.shriekIso` of their
compactifications. The proof compares both with the common refinement `T₁.inf T₂`.
(blueprint: `sk-thm-sf-comp-composition`, independence of all compactification choices) -/
theorem compIso_hom_eq [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (T₁ T₂ : Compactification.Triangle f g) :
    (F.compIso T₁).hom =
      NatTrans.hcomp (F.shriekIso T₁.cf T₂.cf).hom (F.shriekIso T₁.cg T₂.cg).hom ≫
        (F.compIso T₂).hom ≫ (F.shriekIso T₂.cfg T₁.cfg).hom := by
  set φ₁ := T₁.infFst T₂
  set φ₂ := T₁.infSnd T₂
  rw [F.shriekIso_eq φ₁.rf φ₂.rf φ₁.isPullback_rf φ₂.isPullback_rf,
    F.shriekIso_eq φ₁.rg φ₂.rg φ₁.isPullback_rg φ₂.isPullback_rg,
    F.shriekIso_eq φ₂.rfg φ₁.rfg φ₂.isPullback_rfg φ₁.isPullback_rfg]
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, NatTrans.exchange]
  have h₁ := F.compIso_naturality φ₁
  have h₂ := F.compIso_naturality φ₂
  rw [reassoc_of% h₂, Category.assoc, ← Category.assoc (NatTrans.hcomp (inv _) (inv _)),
    ← NatTrans.exchange, IsIso.inv_hom_id, IsIso.inv_hom_id]
  have hid : NatTrans.hcomp (𝟙 (F.shriek (T₁.inf T₂).cf)) (𝟙 (F.shriek (T₁.inf T₂).cg)) = 𝟙 _ := by
    ext; simp
  rw [hid, Category.id_comp, ← reassoc_of% h₁, IsIso.hom_inv_id, Category.comp_id]

section Unit

end Unit

end AlgebraicGeometry.CompactSupportFormalism
