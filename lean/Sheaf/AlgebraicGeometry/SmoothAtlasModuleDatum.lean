/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Module descent data on the scheme tests of an atlas

Source: Stacks Project, stacks-sheaves.tex, Tag 06WT; spaces-groupoids.tex, Tag 0441
(blueprint: def-sfb-smooth-atlas-module-datum).

The relation is tested on schemes, without choosing a scheme representative for the
algebraic-space relation. Section coordinates use the canonical tensor extension from
small etale modules to big fppf modules. Its adjunction unit fixes the normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Lift the usual regular-function sheaf to a universe containing the scheme site.
Source: Stacks 03DU, 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
abbrev atlasFppfRings (U : Scheme.{u}) :=
  (sheafCompose (Scheme.fppfTopology.over U) (forget₂ CommRingCat RingCat)).obj
    (SheafOfModules.CochainUniverseTransport.ring.{u + 1, u, u, 0, max (u + 1) m}
      (Sheaf.over (⟨Scheme.Γ, Scheme.isSheaf_Γ Scheme.fppfTopology⟩ :
        Sheaf Scheme.fppfTopology CommRingCat.{u}) U))

/-- Restricting a big fppf sheaf to small etale tests preserves its sheaf condition.
Source: Stacks 06WT, 03DX (blueprint: def-sfb-smooth-atlas-module-datum).
Proof: every small etale covering is an fppf covering of the same scheme. Its
iterated fibre products agree in both sites. Thus the matching families and their
unique amalgamations are the matching families and amalgamations of the big sheaf. -/
@[instance] theorem atlasEtaleForget_continuous (U : Scheme.{u}) :
    (Scheme.Etale.forget U).IsContinuous U.smallEtaleTopology
      (Scheme.fppfTopology.over U) := by
  sorry

/-- The usual small etale rings, in the same regular-function coordinates as the big site.
Source: Stacks 03DU, 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
abbrev atlasEtaleRings (U : Scheme.{u}) :=
  ((Scheme.Etale.forget U).sheafPushforwardContinuous RingCat U.smallEtaleTopology
    (Scheme.fppfTopology.over U)).obj (atlasFppfRings.{u, m} U)

/-- Additive sheafification on every small etale slice in the ambient universe.
Source: Stacks 03DA (blueprint: def-sfb-smooth-atlas-module-datum). -/
instance atlasEtaleSliceSheafify (U : Scheme.{u}) (V : U.Etale) :
    HasWeakSheafify (U.smallEtaleTopology.over V) AddCommGrpCat.{max (u + 1) m} :=
  letI := (SheafOfModules.coefficientSheafification.{u + 1, u, max (u + 1) m}
    (U.smallEtaleTopology.over V)).1
  HasSheafify.isRightAdjoint

/-- Local bijectivity describes sheafification on every small etale slice.
Source: Stacks 03DA (blueprint: def-sfb-smooth-atlas-module-datum). -/
instance atlasEtaleSliceLocallyBijective (U : Scheme.{u}) (V : U.Etale) :
    (U.smallEtaleTopology.over V).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  (SheafOfModules.coefficientSheafification.{u + 1, u, max (u + 1) m}
    (U.smallEtaleTopology.over V)).2

/-- The quasi-coherent small etale modules, using the existing local-presentation predicate.
Source: Stacks 03DL, 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
abbrev AtlasEtaleQCoh (U : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent.{max (u + 1) m} (atlasEtaleRings.{u, m} U)).FullSubcategory

/-- Small etale restriction, including its actual structural scalar action.
Source: Stacks 06WT, 03DX (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasEtaleRestriction (U : Scheme.{u}) :
    SheafOfModules.{max (u + 1) m} (atlasFppfRings.{u, m} U) ⥤
      SheafOfModules.{max (u + 1) m} (atlasEtaleRings.{u, m} U) :=
  SheafOfModules.pushforward (F := Scheme.Etale.forget U) (𝟙 _)

/-- Reuse the universe-general tensor-extension adjunction for the restriction map.
Both sites have objects in u+1 and arrows in u; coefficients lie in max (u+1) m.
Source: Stacks 03D7, 06WT (blueprint: def-sfb-smooth-atlas-module-datum);
existing construction: lem-pur-ringed-site-module-pullback-exists-universes. -/
instance atlasEtaleRestriction_isRightAdjoint (U : Scheme.{u}) :
    (atlasEtaleRestriction.{u, m} U).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u,
    max (u + 1) m} (𝟙 _)

/-- The associated big fppf module, as inverse image followed by extension of scalars.
For a quasi-coherent module its sections are the sections of its tensor pullbacks.
Source: Stacks 03DX, 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasAssociated (U : Scheme.{u}) :
    SheafOfModules.{max (u + 1) m} (atlasEtaleRings.{u, m} U) ⥤
      SheafOfModules.{max (u + 1) m} (atlasFppfRings.{u, m} U) :=
  (atlasEtaleRestriction.{u, m} U).leftAdjoint

/-- The adjunction whose unit identifies the original etale sections with their extension.
Source: Stacks 03D7, 03DX (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasAssociatedAdjunction (U : Scheme.{u}) :
    atlasAssociated.{u, m} U ⊣ atlasEtaleRestriction.{u, m} U :=
  Adjunction.ofIsRightAdjoint (atlasEtaleRestriction.{u, m} U)

/-- The atlas object over a scheme test, retaining the original based functor.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasTestObject {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    {T : Over S} (f : T ⟶ U) : X.obj :=
  a.toFunctor.obj (CostructuredArrow.mk (yoneda.map f))

/-- Restriction of an atlas object along a map of scheme tests.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasTestArrow {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    {T' T : Over S} (h : T' ⟶ T) (f : T ⟶ U) :
    atlasTestObject a (h ≫ f) ⟶ atlasTestObject a f :=
  a.toFunctor.map (CostructuredArrow.homMk h)

/-- The corresponding arrow on scheme tests over the atlas scheme.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasSchemeTestArrow {S : Scheme.{u}} {U T' T : Over S}
    (h : T' ⟶ T) (f : T ⟶ U) :
    Over.mk (h ≫ f).left ⟶ Over.mk f.left :=
  Over.homMk h.left

/-- The structural equality of a based functor gives the actual scheme identification.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def atlasTestBaseIso {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    {T : Over S} (f : T ⟶ U) :
    (moduliSchemeForget X).obj (atlasTestObject a f) ≅ T.left :=
  (Over.forget S).mapIso (eqToIso
    (congrArg (fun H ↦ H.obj (CostructuredArrow.mk (yoneda.map f))) a.w))

/-- A point of the self 2-relation: two atlas points and an isomorphism over the identity.
The orientation is reversed so contravariant module restriction goes from f to g.
Source: Stacks 06WT, 0441 (blueprint: def-sfb-smooth-atlas-module-datum). -/
abbrev AtlasRelation {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    {T : Over S} (f g : T ⟶ U) :=
  {q : atlasTestObject a g ≅ atlasTestObject a f //
    X.p.IsHomLift (𝟙 T) q.hom}

/-- Section form of (M, delta), on every scheme point of the algebraic-space relation.
Naturality under all test maps is part of an isomorphism of relation sheaves. Identity
and composition give the diagonal normalization and triple cocycle, respectively.
Source: Stacks 06WT, 0441 (blueprint: def-sfb-smooth-atlas-module-datum). -/
structure SmoothAtlasModuleDatum {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) X) where
  /-- The actual small etale quasi-coherent module on U. -/
  module : AtlasEtaleQCoh.{u, max v w} U.left
  /-- Delta evaluated on an arbitrary scheme test of the relation. -/
  delta {T : Over S} (f g : T ⟶ U) (q : AtlasRelation a f g) :
    ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.obj (op (Over.mk f.left)) ≃+
      ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.obj (op (Over.mk g.left))
  /-- The same regular function on T acts on both modules. -/
  delta_smul {T : Over S} (f g : T ⟶ U) (q : AtlasRelation a f g)
      (r : (atlasFppfRings.{u, max v w} U.left).obj.obj (op (Over.mk f.left)))
      (s : ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.obj
        (op (Over.mk f.left))) :
    delta f g q (r • s) = r • delta f g q s
  /-- Naturality in every scheme test; the square is exactly a relation-test morphism. -/
  naturality {T' T : Over S} (h : T' ⟶ T) (f g : T ⟶ U)
      (q : AtlasRelation a f g) (q' : AtlasRelation a (h ≫ f) (h ≫ g))
      (hq : q'.val.hom ≫ atlasTestArrow a h f = atlasTestArrow a h g ≫ q.val.hom)
      (s : ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.obj
        (op (Over.mk f.left))) :
    delta (h ≫ f) (h ≫ g) q'
      (((atlasAssociated.{u, max v w} U.left).obj module.obj).val.map
        (atlasSchemeTestArrow h f).op s) =
        ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.map (atlasSchemeTestArrow h g).op
          (delta f g q s)
  /-- e*delta = 1, including all test schemes of the diagonal. -/
  identity {T : Over S} (f : T ⟶ U) (q : AtlasRelation a f f)
      (hq : q.val = Iso.refl _) : delta f f q = AddEquiv.refl _
  /-- delta_23 after delta_12 is delta_13 on every triple-relation test. -/
  cocycle {T : Over S} (f g h : T ⟶ U)
      (q : AtlasRelation a f g) (r : AtlasRelation a g h) (t : AtlasRelation a f h)
      (ht : t.val = r.val ≪≫ q.val)
      (s : ((atlasAssociated.{u, max v w} U.left).obj module.obj).val.obj
        (op (Over.mk f.left))) :
    delta g h r (delta f g q s) = delta f h t s

namespace SmoothAtlasModuleDatum

variable {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)} {U : Over S}
  {a : BasedFunctor (discreteModuli (yoneda.obj U)) X}

/-- All module maps commuting with delta; no isomorphism condition on maps is imposed.
Source: Stacks 06WT, 0441 (blueprint: def-sfb-smooth-atlas-module-datum). -/
def Compatible (M N : SmoothAtlasModuleDatum a) (b : M.module.obj ⟶ N.module.obj) : Prop :=
  ∀ (T : Over S) (f g : T ⟶ U) (q : AtlasRelation a f g)
    (s : ((atlasAssociated.{u, max v w} U.left).obj M.module.obj).val.obj
      (op (Over.mk f.left))),
    N.delta f g q (((atlasAssociated U.left).map b).val.app (op (Over.mk f.left)) s) =
      ((atlasAssociated U.left).map b).val.app (op (Over.mk g.left)) (M.delta f g q s)

/-- The category of descent pairs, with precisely the compatible module maps.
Source: Stacks 06WT, 0441 (blueprint: def-sfb-smooth-atlas-module-datum). -/
instance category : Category (SmoothAtlasModuleDatum a) where
  Hom M N := {b : M.module.obj ⟶ N.module.obj // Compatible M N b}
  id M := ⟨𝟙 _, by intro T f g q s; simp⟩
  comp b c := ⟨b.val ≫ c.val, by
    intro T f g q s
    simp only [Functor.map_comp, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    rw [c.property, b.property]⟩
  id_comp b := Subtype.ext (Category.id_comp _)
  comp_id b := Subtype.ext (Category.comp_id _)
  assoc b c d := Subtype.ext (Category.assoc _ _ _)

/-- Forget the relation isomorphism, retaining the actual etale module and every map.
Source: Stacks 06WT (blueprint: def-sfb-smooth-atlas-module-datum). -/
def forget : SmoothAtlasModuleDatum a ⥤
    SheafOfModules.{max (u + 1) v w} (atlasEtaleRings.{u, max v w} U.left) where
  obj M := M.module.obj
  map b := b.val

end SmoothAtlasModuleDatum

end CategoryTheory
