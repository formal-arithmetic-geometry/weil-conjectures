/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Canonical arrows for Gabber's local projection comparison

Source: ILO, Exposé XI §2.2, (2.a)–(2.f)
(blueprint: def-trf-local-oriented-projection-arrows).

All arrows are defined using the existing sheaf, point, and adjunction constructions.
The module lift records its scalar action under the set adjunction, which determines
its direct image, and hence its adjoint inverse image, up to their canonical isomorphisms.
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.GabberLocalProjection

/-- Global sections on the small étale site. Source: ILO XI §2.1
(blueprint: def-trf-local-oriented-projection-arrows). -/
def sections (X : Scheme.{u}) : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1) :=
  (sheafSections X.smallEtaleTopology (Type (u + 1))).obj (op (⊤_ X.Etale))

/-- The geometric morphism of étale topoi induced by a scheme morphism.
Source: ILO XI §2.2 and Stacks 03Q1
(blueprint: def-trf-local-oriented-projection-arrows). -/
def etale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    GeometricMorphism (Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  inverse := Scheme.etaleSetPullback f
  direct := (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
    (Type (u + 1)) (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
  adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
  leftExact := by
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    unfold Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    infer_instance

/-- The canonical morphism to sets, with constant-sheaf inverse image.
Source: ILO XI §2.2 (blueprint: def-trf-local-oriented-projection-arrows). -/
def epsilon (X : Scheme.{u}) :
    GeometricMorphism (Sheaf X.smallEtaleTopology (Type (u + 1))) (Type (u + 1)) where
  inverse := constantSheaf X.smallEtaleTopology (Type (u + 1))
  direct := sections X
  adj := constantSheafAdj X.smallEtaleTopology (Type (u + 1)) terminalIsTerminal
  leftExact := by unfold constantSheaf; infer_instance

/-- The geometric point, using the existing stalk/skyscraper adjunction.
Source: ILO XI §2.1 (blueprint: def-trf-local-oriented-projection-arrows). -/
def point {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    GeometricMorphism (Type (u + 1)) (Sheaf X.smallEtaleTopology (Type (u + 1))) where
  inverse := (Scheme.pointSmallEtale x).sheafFiber
  direct := (Scheme.pointSmallEtale x).skyscraperSheafFunctor
  adj := (Scheme.pointSmallEtale x).skyscraperSheafAdjunction
  leftExact := by
    let : AB5OfSize.{u, u} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (Type (u + 1))
    infer_instance

/-- The actual germ map from global sections to the geometric stalk.
Source: ILO XI §2.1 (blueprint: def-trf-local-oriented-projection-arrows). -/
def germ {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) : sections X ⟶ (point x).inverse where
  app H := (Scheme.pointSmallEtale x).toPresheafFiber (⊤_ X.Etale)
    ((Scheme.pointSmallEtale x).fiber.map (terminal.from (Scheme.Etale.mk (𝟙 X)))
      (Over.homMk x (by simp))) H.obj
  naturality H K f :=
    ((Scheme.pointSmallEtale x).toPresheafFiber_naturality f.hom _ _).symm

/-- Direct image does not change global sections. The identification is induced
by the unique isomorphism between the two final étale objects.
Source: ILO XI §2.2 (blueprint: def-trf-local-oriented-projection-arrows). -/
def directSections {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etale f).direct ⋙ sections Y ≅ sections X :=
  NatIso.ofComponents (fun H ↦ H.obj.mapIso
    ((terminalIsTerminal.isTerminalObj (MorphismProperty.Over.pullback @Etale ⊤ f)
      (⊤_ Y.Etale)).uniqueUpToIso terminalIsTerminal).symm.op)
    (by intros; dsimp [etale, sections]; simp only [← NatTrans.naturality])

/-- Pullback of global sections followed by the germ at `x`. It is the canonical
map Γ(S,F) → (a⁻¹F)ₓ, whose invertibility expresses the local hypothesis.
Source: ILO XI §§2.1–2.2 (blueprint: def-trf-local-oriented-projection-arrows). -/
def imageGerm {A S : Scheme.{u}} (a : A ⟶ S) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A) :
    sections S ⟶ ((point x).comp (etale a)).inverse :=
  Functor.whiskerRight (etale a).adj.unit (sections S) ≫
    Functor.whiskerLeft (etale a).inverse (directSections a).hom ≫
    Functor.whiskerLeft (etale a).inverse (germ x)

/-- The canonical constant-sheaf pullback comparison, obtained from the two
adjunctions to global sections. Source: ILO XI §2.2(d)
(blueprint: def-trf-local-oriented-projection-arrows). -/
def constantPullback {B S : Scheme.{u}} (b : B ⟶ S) :
    (epsilon S).inverse ⋙ (etale b).inverse ≅ (epsilon B).inverse :=
  (((epsilon S).adj.comp (etale b).adj).ofNatIsoRight (directSections b)).leftAdjointUniq
    (epsilon B).adj

/-- The inverse-image mate of b ⇒ axε, using exactly the closed-point counit.
The isomorphism `d` will be normalized by `d.hom = imageGerm a x`.
Source: ILO XI §2.2(b)–(d) (blueprint: def-trf-local-oriented-projection-arrows). -/
def closedCounit {A B S : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A)
    (d : sections S ≅ ((point x).comp (etale a)).inverse) :
    (((epsilon B).comp (point x)).comp (etale a)).inverse ⟶ (etale b).inverse :=
  Functor.whiskerRight d.inv (epsilon B).inverse ≫
    Functor.whiskerLeft (sections S) (constantPullback b).inv ≫
    Functor.whiskerRight (epsilon S).adj.counit (etale b).inverse

/-- The direct-image convention for the canonical orientation of the section cone.
Source: ILO XI §2.2(d) (blueprint: def-trf-local-oriented-projection-arrows). -/
def closedOrientation {A B S : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A)
    (d : sections S ≅ ((point x).comp (etale a)).inverse) :
    (etale b).direct ⟶ (((epsilon B).comp (point x)).comp (etale a)).direct :=
  (conjugateEquiv (etale b).adj
    ((((epsilon B).comp (point x)).comp (etale a)).adj)) (closedCounit a b x d)

/-- The identity geometric morphism. Source: ILO XI §2.2(e)
(blueprint: def-trf-local-oriented-projection-arrows). -/
def identity (E : Type (u + 2)) [Category.{u + 1} E] : GeometricMorphism E E :=
  ⟨𝟭 E, 𝟭 E, Adjunction.id, inferInstance⟩

/-- Forget the module structure over the actual constant ring sheaf.
Source: Stacks 00YV (blueprint: def-trf-local-oriented-projection-arrows). -/
def underlying {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [CommRing Λ] :
    ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)) ⥤
      Sheaf J (Type (u + 1)) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat)

/-- Constant scalars act through the ring-sheafification unit.
Source: Stacks 00YV (blueprint: def-trf-local-oriented-projection-arrows). -/
def scale {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [CommRing Λ]
    (M : ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)))
    (r : Λ) (U : Cᵒᵖ) (m : M.val.obj U) : M.val.obj U :=
  ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app U r) • m

/-- A constant-coefficient lift of a geometric morphism, specified by its set
adjunction and its scalar operations on generalized sections. In `linear`, the
adjoints of z = r x + y satisfy that same identity. This determines the module
direct image rather than allowing an arbitrary underlying-set lift; its left
adjoint and the compatible units are then determined up to canonical isomorphism.
Source: Stacks 00YV; ILO XI §2.2(f)
(blueprint: def-trf-local-oriented-projection-arrows). -/
structure ModuleLift {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf J (Type (u + 1))) (Sheaf K (Type (u + 1))))
    (Λ : Type (u + 1)) [CommRing Λ] where
  inverse : ringedSiteModules.{u + 1} ((constantSheaf K RingCat.{u + 1}).obj (RingCat.of Λ)) ⥤
    ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ))
  direct : ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)) ⥤
    ringedSiteModules.{u + 1} ((constantSheaf K RingCat.{u + 1}).obj (RingCat.of Λ))
  adj : inverse ⊣ direct
  underlyingInverse : inverse ⋙ underlying J Λ ≅
    underlying K Λ ⋙ f.inverse
  underlyingDirect : direct ⋙ underlying K Λ ≅
    underlying J Λ ⋙ f.direct
  homEquiv : ∀
    (N : ringedSiteModules.{u + 1} ((constantSheaf K RingCat.{u + 1}).obj (RingCat.of Λ)))
    (M : ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)))
    (h : inverse.obj N ⟶ M),
    (underlying K Λ).map (adj.homEquiv N M h) ≫
      underlyingDirect.hom.app M =
    f.adj.homEquiv _ _ (underlyingInverse.inv.app N ≫
      (underlying J Λ).map h)
  linear : ∀ (M : ringedSiteModules.{u + 1} ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)))
    (T : Sheaf K (Type (u + 1)))
    (r : Λ) (x y z : T ⟶
      (underlying K Λ).obj (direct.obj M)),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U), z.hom.app U t =
      @Add.add ((direct.obj M).val.obj U) inferInstance
        (scale K Λ (direct.obj M) r U (x.hom.app U t))
        (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (f.inverse.obj T).obj.obj U),
      ((f.adj.homEquiv T _).symm (z ≫ underlyingDirect.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (scale J Λ M r U
            (((f.adj.homEquiv T _).symm (x ≫ underlyingDirect.hom.app M)).hom.app U t))
          (((f.adj.homEquiv T _).symm (y ≫ underlyingDirect.hom.app M)).hom.app U t)

/-- The specified comparison, obtained by applying p₂,* to the section adjunction
unit and then the section-composition isomorphism. Source: ILO XI (2.f)
(blueprint: def-trf-local-oriented-projection-arrows). -/
def unitComparison {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (p : GeometricMorphism (Sheaf J (Type (u + 1))) (Sheaf K (Type (u + 1))))
    (s : GeometricMorphism (Sheaf K (Type (u + 1))) (Sheaf J (Type (u + 1))))
    (Λ : Type (u + 1)) [CommRing Λ] (pL : ModuleLift J K p Λ)
    (sL : ModuleLift K J s Λ) (e : sL.direct ⋙ pL.direct ≅ 𝟭 _) :
    pL.direct ⟶ sL.inverse :=
  Functor.whiskerRight sL.adj.unit pL.direct ≫
    (Functor.associator sL.inverse sL.direct pL.direct).hom ≫
    Functor.whiskerLeft sL.inverse e.hom

end CategoryTheory.GabberLocalProjection
