/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.OpenTensorNormalization
import WeilConjectures.Compactification.Refinement

/-! # Ambient proper/open pasting

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D, and the agent's clopen construction
on the ordinary unbounded pro-etale and ringed sequence sites
(blueprint: lem-sf-ambient-proper-open-pasting).

All arrows are the existing intrinsic clopen-projection maps and their adjunction mates.
The shared record below only packages their equations; its two realizations use the actual
finite-coefficient and simultaneous semilinear-system derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

/-- Finite-type schemes over the fixed algebraic closure, with all morphisms over it.
No separatedness of a structure map is imposed. Source: the ambient convention of
Stacks 0F7B--0F7D (blueprint: lem-sf-ambient-proper-open-pasting). -/
abbrev Spaces (F : WeilConjectures.FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (C := Over (Spec (.of F.k)))
    (fun X => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- The actual underlying scheme functor. Source: Stacks 0F7B--0F7D
(blueprint: lem-sf-ambient-proper-open-pasting). -/
abbrev geometry (F : WeilConjectures.FiniteFieldDatum.{u}) : Spaces F ⥤ Scheme.{u} :=
  ObjectProperty.ι _ ⋙ Over.forget _

set_option linter.checkUnivs false in
/-- A record of the operations already constructed by the dependencies. The pullback
compositor is oriented from the composite pullback to successive pullbacks; its inverse
is the d of the node. Source: Stacks 0F7B--0F7D
(blueprint: lem-sf-ambient-proper-open-pasting). -/
structure Calculus (G : Type g) [Category.{h} G] (geo : G ⥤ Scheme.{u}) where
  D : G → Type v
  [category : ∀ X, Category.{w} (D X)]
  P : ∀ {X Y}, (X ⟶ Y) → D Y ⥤ D X
  S : ∀ {X Y}, (X ⟶ Y) → D X ⥤ D Y
  J : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)], D X ⥤ D Y
  adj : ∀ {X Y} (f : X ⟶ Y), P f ⊣ S f
  openAdj : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)], J j ⊣ P j
  pComp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f
  pId : ∀ X, P (𝟙 X) ≅ 𝟭 (D X)
  alpha : ∀ {U V W Z} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] (_h : k ≫ p = r ≫ i),
    J i ⋙ P p ⟶ P r ⋙ J k

attribute [instance] Calculus.category

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

/-- Direct-image composition is the adjunction conjugate of pComp. In particular the
composite adjunction is identified with the specified adjunction for the composite.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.sComp (c : Calculus.{u, g, h, v, w} G geo)
    {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) : c.S f ⋙ c.S g ≅ c.S (f ≫ g) :=
  conjugateIsoEquiv ((c.adj g).comp (c.adj f)) (c.adj (f ≫ g)) (c.pComp f g)

/-- Open-extension composition is fixed by the open adjunction and pComp.
Source: Stacks 03DI (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.jComp (c : Calculus.{u, g, h, v, w} G geo)
    {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map (f ≫ g))] : c.J f ⋙ c.J g ≅ c.J (f ≫ g) :=
  Adjunction.leftAdjointCompIso (c.openAdj f) (c.openAdj g) (c.openAdj (f ≫ g))
    (c.pComp f g).symm

/-- The direct-image identity is the adjunction conjugate of pId.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.sId (c : Calculus.{u, g, h, v, w} G geo) (X : G) : c.S (𝟙 X) ≅ 𝟭 (c.D X) :=
  (conjugateIsoEquiv Adjunction.id (c.adj (𝟙 X)) (c.pId X)).symm

/-- The open-extension identity is fixed by the open adjunction and pId.
Source: Stacks 03DI (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.jId (c : Calculus.{u, g, h, v, w} G geo) (X : G)
    [IsOpenImmersion (geo.map (𝟙 X))] : c.J (𝟙 X) ≅ 𝟭 (c.D X) :=
  (c.openAdj (𝟙 X)).leftAdjointUniq (Adjunction.id.ofNatIsoRight (c.pId X).symm)

/-- Gamma is the prescribed proper-adjunction mate of the intrinsic clopen alpha.
Source: Stacks 0F7B and 07A7 (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.gamma (c : Calculus.{u, g, h, v, w} G geo)
    {U V W Z : G} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] (h : k ≫ p = r ≫ i) :
    c.S r ⋙ c.J i ⟶ c.J k ⋙ c.S p :=
  mateEquiv (c.adj r) (c.adj p) (c.alpha k r p i h)

/-- The canonical ordinary coefficient realization. Alpha is the dependency's explicit
beta/clopen-projection composite; no transformation is chosen from its values.
Source: Stacks 0F7B (blueprint: lem-sf-ambient-proper-open-pasting). -/
def ordinary (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Calculus (Spaces F) (geometry F) where
  D X := ProperOpenDerived Λ X.obj.left
  P f := ProperOpenPull Λ f.hom.left
  S f := ProperOpenPush Λ f.hom.left
  J j hJ := by
    letI : IsOpenImmersion j.hom.left := hJ
    exact ProperOpenShriek Λ j.hom.left
  adj f := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f.hom.left
  openAdj j hJ := by
    letI : IsOpenImmersion j.hom.left := hJ
    exact properOpenAdj Λ j.hom.left
  pComp f g := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f.hom.left g.hom.left
  pId X := leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X.obj.left
  alpha k r p i hk hi hqk hqi hpr hpp h := by
    letI : IsOpenImmersion k.hom.left := hk
    letI : IsOpenImmersion i.hom.left := hi
    letI : QuasiCompact k.hom.left := hqk
    letI : QuasiCompact i.hom.left := hqi
    letI : IsProper r.hom.left := hpr
    letI : IsProper p.hom.left := hpp
    exact properOpenAlpha Λ k.hom.left r.hom.left p.hom.left i.hom.left
      (congrArg (fun f => f.hom.left) h)

/-- The simultaneous ringed-diagram realization. These are actual unbounded derived
systems with semilinear transitions, before any evaluation or scalar restriction.
Source: Zheng 4.1, 4.10; Stacks 0F7B
(blueprint: lem-sf-ambient-proper-open-pasting). -/
def systems (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    Calculus (Spaces F) (geometry F) where
  D X := SemilinearProperOpen.Derived C τ X.obj.left
  P f := SemilinearProperOpen.P C τ f.hom.left
  S f := SemilinearProperOpen.R C τ f.hom.left
  J j hJ := by
    letI : IsOpenImmersion j.hom.left := hJ
    exact SemilinearProperOpen.J C τ j.hom.left
  adj f := SemilinearProperOpen.adj C τ f.hom.left
  openAdj j hJ := by
    letI : IsOpenImmersion j.hom.left := hJ
    exact SemilinearProperOpen.jAdj C τ j.hom.left
  pComp f g := SemilinearProperOpen.pComp C τ f.hom.left g.hom.left
  pId X := SemilinearProperOpen.pId C τ X.obj.left
  alpha k r p i hk hi hqk hqi hpr hpp h := by
    letI : IsOpenImmersion k.hom.left := hk
    letI : IsOpenImmersion i.hom.left := hi
    letI : QuasiCompact k.hom.left := hqk
    letI : QuasiCompact i.hom.left := hqi
    letI : IsProper r.hom.left := hpr
    letI : IsProper p.hom.left := hpp
    exact SemilinearProperOpen.alpha C τ k.hom.left r.hom.left p.hom.left i.hom.left
      (congrArg (fun f => f.hom.left) h)

/-- Properness of a mapped composite, by the existing composition instance.
Source: Stacks 01W6 (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedCompositeProper {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper (geo.map f)] [IsProper (geo.map g)] : IsProper (geo.map (f ≫ g)) := by
  rw [geo.map_comp]
  infer_instance

/-- Openness of a mapped composite, by the existing composition instance.
Source: Stacks 01IO (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedCompositeOpen {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)] :
    IsOpenImmersion (geo.map (f ≫ g)) := by
  rw [geo.map_comp]
  infer_instance

/-- Quasi-compactness of a mapped composite, by the existing composition instance.
Source: Stacks 01K3 (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedCompositeQuasiCompact {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact (geo.map f)] [QuasiCompact (geo.map g)] :
    QuasiCompact (geo.map (f ≫ g)) := by
  rw [geo.map_comp]
  infer_instance

/-- Properness of a mapped identity.
Source: Stacks 01W6 (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedIdentityProper (X : G) : IsProper (geo.map (𝟙 X)) := by
  rw [geo.map_id]
  infer_instance

/-- Openness of a mapped identity.
Source: Stacks 01IO (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedIdentityOpen (X : G) : IsOpenImmersion (geo.map (𝟙 X)) := by
  rw [geo.map_id]
  infer_instance

/-- Quasi-compactness of a mapped identity.
Source: Stacks 01K3 (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance mappedIdentityQuasiCompact (X : G) : QuasiCompact (geo.map (𝟙 X)) := by
  rw [geo.map_id]
  infer_instance

/-- Equality transport of pullback, used for associativity and identity arrows.
Source: Stacks 03CB (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.pCongr (c : Calculus.{u, g, h, v, w} G geo)
    {X Y : G} {f g : X ⟶ Y} (h : f = g) : c.P f ≅ c.P g :=
  eqToIso (congrArg c.P h)

/-- Equality transport of direct image.
Source: Stacks 03CB (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.sCongr (c : Calculus.{u, g, h, v, w} G geo)
    {X Y : G} {f g : X ⟶ Y} (h : f = g) : c.S f ≅ c.S g :=
  eqToIso (congrArg c.S h)

/-- Equality transport of open extension; the immersion proofs are proof irrelevant.
Source: Stacks 03DI (blueprint: lem-sf-ambient-proper-open-pasting). -/
def Calculus.jCongr (c : Calculus.{u, g, h, v, w} G geo)
    {X Y : G} {f g : X ⟶ Y}
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    (h : f = g) : c.J f ≅ c.J g := by
  cases h
  exact Iso.refl _

/-- The explicit equations of the node, with functor associators expressed at components.
This is only a package of equations, not an additional hypothesis on the realizations.
Source: Stacks 0F7B--0F7D (blueprint: lem-sf-ambient-proper-open-pasting). -/
structure Laws (c : Calculus.{u, g, h, v, w} G geo) : Prop where
  /-- Pullback compositors are associative. -/
  p_assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : c.D T),
    (c.pComp (f ≫ g) h).hom.app M ≫ (c.pComp f g).hom.app ((c.P h).obj M) =
      (c.pCongr (Category.assoc f g h)).hom.app M ≫ (c.pComp f (g ≫ h)).hom.app M ≫
        (c.P f).map ((c.pComp g h).hom.app M)
  /-- The two pullback unit equations. -/
  p_unit : ∀ {X Y : G} (f : X ⟶ Y) (M : c.D Y),
    ((c.pComp (𝟙 X) f).hom.app M ≫ (c.pId X).hom.app ((c.P f).obj M) =
      (c.pCongr (Category.id_comp f)).hom.app M) ∧
    ((c.pComp f (𝟙 Y)).hom.app M ≫ (c.P f).map ((c.pId Y).hom.app M) =
      (c.pCongr (Category.comp_id f)).hom.app M)
  /-- Direct-image compositors are associative. -/
  s_assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : c.D X),
    (c.S h).map ((c.sComp f g).hom.app M) ≫ (c.sComp (f ≫ g) h).hom.app M =
      (c.sComp g h).hom.app ((c.S f).obj M) ≫ (c.sComp f (g ≫ h)).hom.app M ≫
        (c.sCongr (Category.assoc f g h)).inv.app M
  /-- The two direct-image unit equations. -/
  s_unit : ∀ {X Y : G} (f : X ⟶ Y) (M : c.D X),
    ((c.sComp (𝟙 X) f).hom.app M ≫ (c.sCongr (Category.id_comp f)).hom.app M =
      (c.S f).map ((c.sId X).hom.app M)) ∧
    ((c.sComp f (𝟙 Y)).hom.app M ≫ (c.sCongr (Category.comp_id f)).hom.app M =
      (c.sId Y).hom.app ((c.S f).obj M))
  /-- Open-extension compositors are associative. -/
  j_assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map h)] (M : c.D X),
    (c.J h).map ((c.jComp f g).hom.app M) ≫ (c.jComp (f ≫ g) h).hom.app M =
      (c.jComp g h).hom.app ((c.J f).obj M) ≫ (c.jComp f (g ≫ h)).hom.app M ≫
        (c.jCongr (Category.assoc f g h)).inv.app M
  /-- The two open-extension unit equations. -/
  j_unit : ∀ {X Y : G} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)] (M : c.D X),
    ((c.jComp (𝟙 X) j).hom.app M ≫ (c.jCongr (Category.id_comp j)).hom.app M =
      (c.J j).map ((c.jId X).hom.app M)) ∧
    ((c.jComp j (𝟙 Y)).hom.app M ≫ (c.jCongr (Category.comp_id j)).hom.app M =
      (c.jId Y).hom.app ((c.J j).obj M))
  /-- Vertical pasting of the intrinsic clopen alpha, before taking mates. -/
  alpha_vertical : ∀ {A C₀ E B D F : G}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r₁)] [IsProper (geo.map r₂)]
    [IsProper (geo.map p₁)] [IsProper (geo.map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : c.D E),
    (c.pComp p₁ p₂).inv.app ((c.J j).obj M) ≫
        (c.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (c.J k).map ((c.pComp r₁ r₂).hom.app M) =
      (c.P p₁).map ((c.alpha i r₂ p₂ j h₂).app M) ≫
        (c.alpha k r₁ p₁ i h₁).app ((c.P r₂).obj M)
  /-- Horizontal pasting of the intrinsic clopen alpha. -/
  alpha_horizontal : ∀ {A B E C₀ D F : G}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map l)]
    [IsOpenImmersion (geo.map i)] [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map l)]
    [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] [IsProper (geo.map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : c.D C₀),
    (c.P q).map ((c.jComp i j).hom.app M) ≫
        (c.alpha (k ≫ l) r q (i ≫ j) h).app M ≫
        (c.jComp k l).inv.app ((c.P r).obj M) =
      (c.alpha l p q j h₂).app ((c.J i).obj M) ≫
        (c.J l).map ((c.alpha k r p i h₁).app M)
  /-- Proper-adjunction mates paste vertically. -/
  gamma_vertical : ∀ {A C₀ E B D F : G}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r₁)] [IsProper (geo.map r₂)]
    [IsProper (geo.map p₁)] [IsProper (geo.map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : c.D A),
    (c.J j).map ((c.sComp r₁ r₂).hom.app M) ≫
        (c.gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (c.sComp p₁ p₂).inv.app ((c.J k).obj M) =
      (c.gamma i r₂ p₂ j h₂).app ((c.S r₁).obj M) ≫
        (c.S p₂).map ((c.gamma k r₁ p₁ i h₁).app M)
  /-- Proper-adjunction mates paste horizontally. -/
  gamma_horizontal : ∀ {A B E C₀ D F : G}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map l)]
    [IsOpenImmersion (geo.map i)] [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map l)]
    [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] [IsProper (geo.map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : c.D A),
    (c.jComp i j).hom.app ((c.S r).obj M) ≫
        (c.gamma (k ≫ l) r q (i ≫ j) h).app M ≫
        (c.S q).map ((c.jComp k l).inv.app M) =
      (c.J j).map ((c.gamma k r p i h₁).app M) ≫
        (c.gamma l p q j h₂).app ((c.J k).obj M)
  /-- Identity proper edges give identity comparisons. -/
  gamma_vertical_id : ∀ {U X : G} (j : U ⟶ X)
    [IsOpenImmersion (geo.map j)] [QuasiCompact (geo.map j)]
    (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : c.D U),
    (c.gamma j (𝟙 U) (𝟙 X) j h).app M ≫ (c.sId X).hom.app ((c.J j).obj M) =
      (c.J j).map ((c.sId U).hom.app M)
  /-- Identity open edges give identity comparisons. -/
  gamma_horizontal_id : ∀ {U X : G} (p : U ⟶ X) [IsProper (geo.map p)]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : c.D U),
    (c.gamma (𝟙 U) p p (𝟙 X) h).app M ≫ (c.S p).map ((c.jId U).hom.app M) =
      (c.jId X).hom.app ((c.S p).obj M)

/-- The tensor/composition equation for the actual ordinary pro-etale functors.
The two tensor maps on the right are the tensor of the two pullback compositors.
Source: Stacks 03EL, 07A4 (blueprint: lem-sf-ambient-proper-open-pasting). -/
def OrdinaryTensorComposition (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  ∀ {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : ProperOpenDerived Λ Z.obj.left),
    ((ordinary F Λ).pComp f g).hom.app
        (((ProperOpenTensor Λ Z.obj.left).obj M).obj N) ≫
        (ProperOpenPull Λ f.hom.left).map
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g.hom.left M N).hom ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f.hom.left
          ((ProperOpenPull Λ g.hom.left).obj M)
          ((ProperOpenPull Λ g.hom.left).obj N)).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) (f ≫ g).hom.left M N).hom ≫
        ((ProperOpenTensor Λ X.obj.left).map
          (((ordinary F Λ).pComp f g).hom.app M)).app
            ((ProperOpenPull Λ (f ≫ g).hom.left).obj N) ≫
        ((ProperOpenTensor Λ X.obj.left).obj
          ((ProperOpenPull Λ f.hom.left).obj ((ProperOpenPull Λ g.hom.left).obj M))).map
            (((ordinary F Λ).pComp f g).hom.app N)

/-- Tensor/composition coherence on the simultaneous ringed sequence site. The tensor
comparison is the published comparison uniquely characterized on K-flat representatives,
not a map chosen after evaluation. The compositors carry their ordinary section formula
and localization certificate, so quantifying over their presentation adds no hypothesis.
Source: Stacks 03EL, 07A4; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-proper-open-pasting). -/
def SystemTensorComposition (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (o : WeilConjectures.IntegralSystemRealization.Operations l E)
    (c : WeilConjectures.IntegralSystemRealization.Compositors l E o) : Prop :=
  ∀ {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : WeilConjectures.coefficientSequenceDerived l E Z.obj.left),
    (c.pullComp f.hom.left g.hom.left).hom.app
        ((WeilConjectures.pullbackTensorCalculus l E Z.obj.left).systemClosed.tensor.obj
          (M, N)) ≫
        (WeilConjectures.pullbackTensorSequenceDerived l E f.hom.left).map
          ((WeilConjectures.pullbackTensorSystemComparison l E g.hom.left).hom.app (M, N)) ≫
        (WeilConjectures.pullbackTensorSystemComparison l E f.hom.left).hom.app
          ((WeilConjectures.pullbackTensorSequenceDerived l E g.hom.left).obj M,
            (WeilConjectures.pullbackTensorSequenceDerived l E g.hom.left).obj N) =
      (WeilConjectures.pullbackTensorSystemComparison l E (f ≫ g).hom.left).hom.app (M, N) ≫
        (WeilConjectures.pullbackTensorCalculus l E X.obj.left).systemClosed.tensor.map
          (Prod.mkHom ((c.pullComp f.hom.left g.hom.left).hom.app M)
            ((c.pullComp f.hom.left g.hom.left).hom.app N))

/-- The positive coefficient ring, in the module coefficient universe, is finite.
Source: Serre, Local Fields, II.2 (blueprint: lem-sf-ambient-proper-open-pasting). -/
instance positiveCoefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  infer_instance

/-- The canonical ambient proper/open calculus obeys all the composition and identity
laws, in both coefficient settings, together with the canonical tensor/composition law.
Positive levels are indexed by `n + 1`, and system indices also start at the first positive
level. There is no separatedness condition on a structure morphism, no Cartesian square
condition, and no restriction on derived objects.
Source: Stacks 0F7B--0F7D, 03CB, 03EL, 07A4 and 07A7; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-proper-open-pasting).

Proof:
1. At the module level use the unique iterated-fibre-product isomorphism and the local
   tensor formula `(m tensor a) tensor b` to `m tensor c(a)b`. The comparison preserves
   the composite adjunction unit by proEtale_tensor_composition_unit; constant-ring
   identifications compose by proEtaleConstantRingComposition. The same formula commutes
   with every coefficient transition on the sequence site. Exact localization gives d.
2. Conjugate d under the specified composite adjunctions to obtain c and e. The composite
   Hom equivalence is the successive Hom equivalence (Adjunction.comp). Its injectivity
   gives associativity, the two unit laws, and compatibility with units and counits, using
   the recorded CompositionAdjunctionNormalization and conjugate-iso unit equation.
3. For tensor coherence use the ordinary inverse-image tensor map on local pure tensors.
   Both routes multiply the same intermediate scalars. Pullback preserves K-flat flat-term
   resolutions; localization of this equality on signed total tensors gives the displayed
   tensor equation. For systems use pullbackTensorSystemComparison's unique K-flat square,
   before evaluation, as supplied by semilinearDerivedSections and the ringed tensor theorem.
4. In each square, b is open by base change; s is open because k factors through b. Since
   q is separated and qs is proper, s is proper, hence closed. Only p is separated over Z.
   The fibre product remains finite type, by finite-type base change and composition.
5. Decompose module sheaves over the two clopen pieces. The projector is `(1,0)`. Maps into
   its selected extension are determined by restriction to that piece. The product-of-sections
   inverse commutes with the coefficient transitions, so the same uniqueness holds for
   module systems. This is sheaf-level uniqueness, not faithfulness of derived evaluation.
6. The intrinsic alpha is beta followed by that projector and the canonical compositors.
   Its selected restriction is identity by the open unit normalization. Exact localization
   preserves the open adjunction and beta. Its proper-adjunction mate is Calculus.gamma.
7. In a vertical pasting, restrict the two successive alpha factors to the outer selected
   clopen piece. Both restrictions are identity, so clopen uniqueness identifies their
   composite with the outer alpha. Localize this module/system equality.
8. In a horizontal pasting make the same restriction along the composite top open. Again
   both factors restrict to identity. Clopen uniqueness gives the intrinsic outer alpha.
9. Apply mateEquiv_vcomp and mateEquiv_hcomp to those two equations, inserting the canonical
   c and e from step 2. This gives the two gamma pasting equations in the actual unbounded
   system category itself, as in semilinearProperOpenMatePasting.
10. In either identity square the selected clopen factor is identity. Its alpha is identity
    under the unit comparisons, and the triangle equations give the gamma identities.
    Refinement squares and intermediate compatible-tower squares have exactly these proper
    and quasi-compact-open hypotheses, so all equations apply to them. No constructibility,
    Tor, boundedness, etale-origin, normalization, evaluation or total-limit condition occurs.
-/
theorem ambientProperOpenPasting (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (Laws (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ∧
    OrdinaryTensorComposition F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Laws (systems F (WeilConjectures.IntegralSystemRealization.scalarRings l E)
      (WeilConjectures.IntegralSystemRealization.scalarTransitions l E)) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (c : WeilConjectures.IntegralSystemRealization.Compositors l E o),
      SystemTensorComposition F l E o c := by
  sorry

end AlgebraicGeometry.ProEtale.AmbientProperOpen
