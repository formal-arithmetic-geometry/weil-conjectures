/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalScalars
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Canonical compactification composition on the completed constructible category
Source: Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.19
(blueprint: def-per-adic-exceptional-composition-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicExceptionalProjection

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]

/-- A whole family of the adjunction conclusions, on every displayed compactification.
Source: Definition 6.7.6 and Lemma 6.7.19
(blueprint: def-per-adic-exceptional-composition-data). -/
abbrev Operations := ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
  (c : Compactification (arrow f)), Operation l E f c

/-- Canonical equality transport of a compact-support presentation.
Source: compactification functoriality (blueprint: def-per-adic-exceptional-composition-data). -/
def supportTransport (E : Coefficient.{u} l) {X Y : Spaces k} {f g : X ⟶ Y}
    (h : f = g) (c : Compactification (arrow g)) :
    support l E f (h.symm ▸ c) ≅ support l E g c := by
  subst h
  exact Iso.refl _

/-- The proper/open word defining the ambient compositor for a compatible triangle.
Source: compactification composition, Definition 6.7.6
(blueprint: def-per-adic-exceptional-composition-data). -/
def ambientComposition (E : Coefficient.{u} l)
    (d : IntegralSystemRealization.RingedModels l E.carrier)
    (a : IntegralSystemRealization.RingedOpenComparisons l E.carrier d)
    (q : IntegralSystemRealization.RingedProperOpen l E.carrier d a)
    {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification (arrow f)) (cg : Compactification (arrow g))
    (cfg : Compactification (arrow (f ≫ g))) (b : cf.Z ⟶ cfg.Z) (p : cfg.Z ⟶ cg.Z)
    [IsOpenImmersion b] [QuasiCompact b] [IsProper p]
    (hb : cf.i ≫ b = cfg.i) (hp : b ≫ p = cf.g ≫ cg.i) (hq : p ≫ cg.g = cfg.g)
    (K : DerivedCategory (scalarReductionSource l E.carrier X.scheme)) :
    (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) cg).obj
      ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) cf).obj K) ⟶
    (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) cfg).obj K := by
  letI : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  exact (IntegralSystemRealization.ringedPush l E.carrier cg.g).map
      ((q.gamma b cf.g p cg.i hp).app
        ((IntegralSystemRealization.ringedOpen l E.carrier cf.i).obj K)) ≫
    (IntegralSystemRealization.ringedPushComp l E.carrier p cg.g).hom.app _ ≫
    (IntegralSystemRealization.ringedPush l E.carrier (p ≫ cg.g)).map
      ((IntegralSystemRealization.ringedOpenComp l E.carrier cf.i b).hom.app K ≫
        (IntegralSystemRealization.ringedOpenCongr l E.carrier hb).hom.app K) ≫
    (eqToIso (congrArg (IntegralSystemRealization.ringedPush l E.carrier) hq)).hom.app _

/-- Compactification independence and composition, fixed by the proper/open mates.
The equations are on full derived maps, before any finite evaluation.
Source: Definition 6.7.6, Lemma 6.7.19, and canonical compactification pasting
(blueprint: def-per-adic-exceptional-composition-data). -/
structure Compositions (O : Operations (k := k) l) where
  ringed : ∀ E : Coefficient.{u} l, IntegralSystemRealization.RingedModels l E.carrier
  openComparison : ∀ E : Coefficient.{u} l,
    IntegralSystemRealization.RingedOpenComparisons l E.carrier (ringed E)
  properOpen : ∀ E : Coefficient.{u} l,
    IntegralSystemRealization.RingedProperOpen l E.carrier (ringed E) (openComparison E)
  change : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c d : Compactification (arrow f)), support l E f c ≅ support l E f d
  changeRefl : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)), change E f c c = Iso.refl _
  changeTrans : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c d e : Compactification (arrow f)), change E f c d ≪≫ change E f d e = change E f c e
  refinementOpen : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    {c d : Compactification (arrow f)} (r : c.Refinement d) (K : C l E X),
    (IntegralSystemRealization.ringedOpen l E.carrier d.i).obj K.obj ≅
      (IntegralSystemRealization.ringedPush l E.carrier r.hom).obj
        ((IntegralSystemRealization.ringedOpen l E.carrier c.i).obj K.obj)
  refinementNormalization : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    {c d : Compactification (arrow f)} (r : c.Refinement d) (K : C l E X),
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.completed l E.carrier) d.i).homEquiv _ _ (refinementOpen E f r K).hom ≫
        PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E.carrier) r
          (PurCompactSupport.completedPull_comp l E.carrier c.i r.hom) K.obj =
      (PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.completed l E.carrier) c.i).unit.app K.obj
  changeRefinement : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    {c d : Compactification (arrow f)} (r : c.Refinement d) (K : C l E X),
    (sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) c).hom.app K ≫
      ((change E f c d).hom.app K).hom =
      ((IntegralSystemRealization.ringedPushComp l E.carrier r.hom d.g ≪≫
        eqToIso (congrArg (IntegralSystemRealization.ringedPush l E.carrier) r.hom_g)).inv.app _) ≫
      (IntegralSystemRealization.ringedPush l E.carrier d.g).map
        (refinementOpen E f r K).inv ≫
      (sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) d).hom.app K
  comp : ∀ (E : Coefficient.{u} l) {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification (arrow f)) (cg : Compactification (arrow g))
    (cfg : Compactification (arrow (f ≫ g))),
    support l E f cf ⋙ support l E g cg ≅ support l E (f ≫ g) cfg
  compNormalization : ∀ (E : Coefficient.{u} l) {X Y Z : Spaces k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (cf : Compactification (arrow f))
    (cg : Compactification (arrow g)) (cfg : Compactification (arrow (f ≫ g)))
    (b : cf.Z ⟶ cfg.Z) (p : cfg.Z ⟶ cg.Z)
    [IsOpenImmersion b] [QuasiCompact b] [IsProper p]
    (hb : cf.i ≫ b = cfg.i) (hp : b ≫ p = cf.g ≫ cg.i) (hq : p ≫ cg.g = cfg.g)
    (K : C l E X),
    (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) cg).map
        ((sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) cf).hom.app K) ≫
      (sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) cg).hom.app ((support l E f cf).obj K) ≫
      ((comp E f g cf cg cfg).hom.app K).hom =
    ambientComposition l E (ringed E) (openComparison E) (properOpen E)
      f g cf cg cfg b p hb hp hq K.obj ≫
      (sfQcqsCompactSupportRealization l E.carrier k
        (Fact.out : IsUnit (l : k)) cfg).hom.app K
  compChange : ∀ (E : Coefficient.{u} l) {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf df : Compactification (arrow f)) (cg dg : Compactification (arrow g))
    (cfg dfg : Compactification (arrow (f ≫ g))) (K : C l E X),
    (support l E g cg).map ((change E f cf df).hom.app K) ≫
      (change E g cg dg).hom.app ((support l E f df).obj K) ≫
      (comp E f g df dg dfg).hom.app K =
        (comp E f g cf cg cfg).hom.app K ≫ (change E (f ≫ g) cfg dfg).hom.app K
  unit : ∀ (E : Coefficient.{u} l) (X : Spaces k)
    (c : Compactification (arrow (𝟙 X))), support l E (𝟙 X) c ≅ 𝟭 (C l E X)
  leftIdentity : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (ci : Compactification (arrow (𝟙 X))) (cf : Compactification (arrow f)) (K : C l E X),
    (support l E f cf).map ((unit E X ci).hom.app K) =
      (comp E (𝟙 X) f ci cf
        ((Category.id_comp f).symm ▸ cf)).hom.app K ≫
      (supportTransport l E (Category.id_comp f) cf).hom.app K
  rightIdentity : ∀ (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (cf : Compactification (arrow f)) (ci : Compactification (arrow (𝟙 Y))) (K : C l E X),
    (unit E Y ci).hom.app ((support l E f cf).obj K) =
      (comp E f (𝟙 Y) cf ci
        ((Category.comp_id f).symm ▸ cf)).hom.app K ≫
      (supportTransport l E (Category.comp_id f) cf).hom.app K

  associativity : ∀ (E : Coefficient.{u} l) {W X Y Z : Spaces k}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (cf : Compactification (arrow f)) (cg : Compactification (arrow g))
    (ch : Compactification (arrow h)) (cfg : Compactification (arrow (f ≫ g)))
    (cgh : Compactification (arrow (g ≫ h)))
    (cfgh : Compactification (arrow (f ≫ (g ≫ h)))) (K : C l E W),
    (support l E h ch).map ((comp E f g cf cg cfg).hom.app K) ≫
      (comp E (f ≫ g) h cfg ch ((Category.assoc f g h).symm ▸ cfgh)).hom.app K ≫
      (supportTransport l E (Category.assoc f g h) cfgh).hom.app K =
    (comp E g h cg ch cgh).hom.app ((support l E f cf).obj K) ≫
      (comp E f (g ≫ h) cf cgh cfgh).hom.app K

/-- The right-adjoint compositor is literally the mate of the displayed support compositor.
Source: Lemma 6.7.19 and mate pasting
(blueprint: def-per-adic-exceptional-composition-data). -/
def exceptionalComposition (O : Operations (k := k) l) (A : Compositions l O)
    (E : Coefficient.{u} l) {X Y Z : Spaces k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification (arrow f)) (cg : Compactification (arrow g))
    (cfg : Compactification (arrow (f ≫ g))) :
    (O E g cg).exceptional ⋙ (O E f cf).exceptional ≅ (O E (f ≫ g) cfg).exceptional :=
  conjugateIsoEquiv ((O E f cf).shriek.adj.comp (O E g cg).shriek.adj)
    (O E (f ≫ g) cfg).shriek.adj (A.comp E f g cf cg cfg).symm

end WeilConjectures.AdicExceptionalProjection
