/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback

/-! # Quasi-coherent modules on an algebraic-space groupoid

Source: Stacks Project, spaces-groupoids.tex, definition-groupoid-module and
lemma-abelian, Tag 06VZ (blueprint: def-sfb-space-groupoid-module).

The composable-arrow space is any specified presheaf pullback. The groupoid laws
are the existing test-scheme laws, transported by its unique pullback isomorphism.
The descent comparisons use the existing tensor-normalized composition and identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A groupoid of algebraic spaces, retaining its composable-arrow pullback.
Source: Stacks, spaces-groupoids.tex, definition-groupoid
(blueprint: def-sfb-space-groupoid-module). -/
structure ModuleGroupoid (S : Scheme.{u}) where
  U : AlgebraicSpace S
  R : AlgebraicSpace S
  P : AlgebraicSpace S
  s : R ⟶ U
  t : R ⟶ U
  e : U ⟶ R
  i : R ⟶ R
  p₀ : P ⟶ R
  p₁ : P ⟶ R
  c : P ⟶ R
  square : IsPullback p₀.hom.hom p₁.hom.hom s.hom.hom t.hom.hom
  laws : IsPresheafGroupoid s.hom.hom t.hom.hom e.hom.hom i.hom.hom
    (square.isoPullback.inv ≫ c.hom.hom)


/-- The recorded tensor pullback behind an opaque descent-equation interface.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
@[irreducible] def spaceGroupoidPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Y.Modules ⥤ X.Modules := moduleTensorPullback f

/-- Comparison of iterated pullbacks with equal composite maps.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
@[irreducible] def spaceGroupoidCompComparison {S : Scheme.{u}}
    {P R U : AlgebraicSpace S} (a b : P ⟶ R) (f g : R ⟶ U)
    (h : a ≫ f = b ≫ g) (M : U.Modules) :
    (spaceGroupoidPullback a).obj ((spaceGroupoidPullback f).obj M) ≅
      (spaceGroupoidPullback b).obj ((spaceGroupoidPullback g).obj M) := by
  unfold spaceGroupoidPullback
  exact (moduleTensorComposition a f).app M ≪≫
    eqToIso (congrArg (fun k ↦ (moduleTensorPullback k).obj M) h) ≪≫
    ((moduleTensorComposition b g).app M).symm

/-- Comparison of pullback along a section with the original module.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
@[irreducible] def spaceGroupoidUnitComparison {S : Scheme.{u}}
    {U R : AlgebraicSpace S} (e : U ⟶ R) (f : R ⟶ U)
    (h : e ≫ f = 𝟙 U) (M : U.Modules) :
    (spaceGroupoidPullback e).obj ((spaceGroupoidPullback f).obj M) ≅ M := by
  unfold spaceGroupoidPullback
  exact (moduleTensorComposition e f).app M ≪≫
    eqToIso (congrArg (fun k ↦ (moduleTensorPullback k).obj M) h) ≪≫
    (moduleTensorPullbackId U).app M

/-- The unit law under the canonical tensor pullback identifications.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
def spaceGroupoidUnitLaw {S : Scheme.{u}} (G : ModuleGroupoid S) (M : G.U.Modules)
    (α : (spaceGroupoidPullback G.t).obj M ≅ (spaceGroupoidPullback G.s).obj M) : Prop :=
  (spaceGroupoidPullback G.e).map α.hom ≫
      (spaceGroupoidUnitComparison G.e G.s (by
        apply ObjectProperty.hom_ext
        apply Sheaf.hom_ext
        exact G.laws.source_id) M).hom =
    (spaceGroupoidUnitComparison G.e G.t (by
      apply ObjectProperty.hom_ext
      apply Sheaf.hom_ext
      exact G.laws.target_id) M).hom

/-- The cocycle law, first the second arrow and then the first.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
def spaceGroupoidCocycleLaw {S : Scheme.{u}} (G : ModuleGroupoid S) (M : G.U.Modules)
    (α : (spaceGroupoidPullback G.t).obj M ≅ (spaceGroupoidPullback G.s).obj M) : Prop :=
  (spaceGroupoidPullback G.c).map α.hom ≫
      (spaceGroupoidCompComparison G.c G.p₁ G.s G.s (by
        apply ObjectProperty.hom_ext
        apply Sheaf.hom_ext
        change G.c.hom.hom ≫ G.s.hom.hom = G.p₁.hom.hom ≫ G.s.hom.hom
        have h := congrArg (fun k ↦ G.square.isoPullback.hom ≫ k) G.laws.source_comp
        simpa only [Category.assoc, Iso.hom_inv_id_assoc,
          IsPullback.isoPullback_hom_snd_assoc] using h) M).hom =
    (spaceGroupoidCompComparison G.c G.p₀ G.t G.t (by
        apply ObjectProperty.hom_ext
        apply Sheaf.hom_ext
        change G.c.hom.hom ≫ G.t.hom.hom = G.p₀.hom.hom ≫ G.t.hom.hom
        have h := congrArg (fun k ↦ G.square.isoPullback.hom ≫ k) G.laws.target_comp
        simpa only [Category.assoc, Iso.hom_inv_id_assoc,
          IsPullback.isoPullback_hom_fst_assoc] using h) M).hom ≫
      (spaceGroupoidPullback G.p₀).map α.hom ≫
      (spaceGroupoidCompComparison G.p₀ G.p₁ G.s G.t (by
          apply ObjectProperty.hom_ext
          apply Sheaf.hom_ext
          exact G.square.w) M).hom ≫
      (spaceGroupoidPullback G.p₁).map α.hom

/-- Quasi-coherent modules with groupoid descent, on the ordinary small etale site.
Source: Stacks, definition-groupoid-module and lemma-abelian, Tag 06VZ
(blueprint: def-sfb-space-groupoid-module). -/
structure SpaceGroupoidModule {S : Scheme.{u}} (G : ModuleGroupoid S) where
  moduleObj : G.U.Modules
  quasiCoherent : moduleObj.IsQuasicoherent
  α : (spaceGroupoidPullback G.t).obj moduleObj ≅
    (spaceGroupoidPullback G.s).obj moduleObj
  unit : spaceGroupoidUnitLaw G moduleObj α
  cocycle : spaceGroupoidCocycleLaw G moduleObj α

namespace SpaceGroupoidModule

variable {S : Scheme.{u}} {G : ModuleGroupoid S}

/-- Equivariant morphisms are exactly the module maps intertwining descent.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
def Hom (M N : SpaceGroupoidModule G) :=
  {v : M.moduleObj ⟶ N.moduleObj //
    (spaceGroupoidPullback G.t).map v ≫ N.α.hom =
      M.α.hom ≫ (spaceGroupoidPullback G.s).map v}

/-- Identities and composition are those of underlying module maps.
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
instance category : Category (SpaceGroupoidModule G) where
  Hom := SpaceGroupoidModule.Hom
  id M := ⟨𝟙 M.moduleObj, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.property, ← Category.assoc, f.property]
    simp only [Category.assoc]⟩
  id_comp f := by apply Subtype.ext; simp
  comp_id f := by apply Subtype.ext; simp
  assoc f g h := by apply Subtype.ext; simp only [Category.assoc]

/-- The forgetful functor to the recorded full subcategory QCoh(U).
Source: Stacks, definition-groupoid-module (blueprint: def-sfb-space-groupoid-module). -/
def forgetToQuasiCoherent : SpaceGroupoidModule G ⥤ G.U.QCoh where
  obj M := ⟨M.moduleObj, M.quasiCoherent⟩
  map v := ObjectProperty.homMk v.val
  map_id _M := rfl
  map_comp _f _g := rfl

/-- The ordinary small-etale module-sheaf forgetful functor.
Source: Stacks, lemma-abelian, Tag 06VZ (blueprint: def-sfb-space-groupoid-module). -/
def forgetToModules : SpaceGroupoidModule G ⥤ G.U.Modules where
  obj M := M.moduleObj
  map v := v.val
  map_id _M := rfl
  map_comp _f _g := rfl

end SpaceGroupoidModule
end AlgebraicGeometry.AlgebraicSpace
