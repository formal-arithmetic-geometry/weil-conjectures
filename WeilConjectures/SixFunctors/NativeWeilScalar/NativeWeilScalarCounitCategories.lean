/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization

/-! # Normalized scalar realization and the Frobenius invariant counit

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph; native expansion,
Steps 1--17 (blueprint: def-sf-native-weil-scalar-counit-categories).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeWeilScalar

open AdicQbarRealization

variable (l : ℕ) [Fact l.Prime]

/-- The ordinary constructible category with its full ambient morphisms.
Source: native expansion, opening paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev Constructible (X : Scheme.{u}) (R : LocallyFiniteAdicRealization.Realization l X) :=
  (boundedConstructible l X R).FullSubcategory

/-- The canonical restriction of the published realization to its stated essential image.
Source: native expansion, scalar-realization paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def rho (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D) :
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left ⥤
      Constructible l T.base.left (R.data T).realization :=
  (boundedConstructible l T.base.left (R.data T).realization).lift
    (ordinary l T.base.left (R.data T).realization)
    (fun K ↦ ((R.data T).image _).2 ⟨K, ⟨Iso.refl _⟩⟩)

/-- The actual ordinary module Frobenius pullback, before any constructible restriction.
Source: native expansion, Frobenius paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev pull (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left) :=
  modulePull l T.base.left g.hom (R.ring T T g)

/-- Complexes of the recorded abelian fixed-pair category, localized at quasi-isomorphisms.
Source: native expansion, opening paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev Pairs (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left) :=
  Endofunctor.IsoAlgebra (pull l D R T g)

/-- Termwise forgetting, followed by ordinary derived localization.
Source: native expansion, opening paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev forget (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left)
    [HasDerivedCategory.{u + 1} (Pairs l D R T g)] :=
  (Endofunctor.IsoAlgebra.forget (pull l D R T g)).mapDerivedCategory

/-- The actual native Weil category is the inverse image of bounded constructibility.
Source: native expansion, opening paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev Weil (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left)
    [HasDerivedCategory.{u + 1} (Pairs l D R T g)] :=
  ((boundedConstructible l T.base.left (R.data T).realization).inverseImage
    (forget l D R T g)).FullSubcategory

/-- The derived structure map is the localization of the actual termwise structure maps.
Source: native expansion, Step 17
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def theta (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left)
    [HasDerivedCategory.{u + 1} (Pairs l D R T g)] :
    forget l D R T g ⋙ (pull l D R T g).mapDerivedCategory ≅ forget l D R T g :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Endofunctor.IsoAlgebra.strNatIso (pull l D R T g))

/-- The actual module functor: exact open extension followed by the separately
right-derived proper image, for the native function-valued coefficient identifications.
Source: native expansion, Step 1
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def compact {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l) :
    DerivedCategory (modules l X R) ⥤ DerivedCategory (modules l Y S) := by
  letI := G
  exact PurCompactSupport.image (LocallyFiniteAdicCompactSupport.nativeCoefficients l) c

/-- The mate is the recorded mate equivalence, with the inverse left comparison.
Source: native expansion, Steps 15--16
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def mate {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (P : A ⥤ A) (Q : B ⥤ B) (a : F ⋙ Q ≅ P ⋙ F) :
    G ⋙ P ⟶ Q ⋙ G :=
  (mateEquiv adj adj a.inv).natTrans

/-- The explicit mate-counit equation, retaining the actual adjunction counit.
Source: native expansion, Step 16
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def MateCounit {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (P : A ⥤ A) (Q : B ⥤ B) (a : F ⋙ Q ≅ P ⋙ F) : Prop :=
  ∀ L : B, F.map ((mate adj P Q a).app L) ≫ adj.counit.app (Q.obj L) =
    a.inv.app (G.obj L) ≫ Q.map (adj.counit.app L)

/-- The induced Weil structure and invariant counit equation. The supplied theta is
always the localization of the termwise structure isomorphism, not a replacement object.
Source: native expansion, Step 17
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def InvariantCounit {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (P : A ⥤ A) (Q : B ⥤ B) (a : F ⋙ Q ≅ P ⋙ F)
    (L : B) (t : Q.obj L ≅ L) : Prop :=
  IsIso ((mate adj P Q a).app L ≫ G.map t.hom) ∧
    a.hom.app (G.obj L) ≫
        F.map ((mate adj P Q a).app L ≫ G.map t.hom) ≫ adj.counit.app L =
      Q.map (adj.counit.app L) ≫ t.hom

/-- Repackage the actual geometric fiber, with precisely its inherited hypotheses.
Source: finite-field convention and native expansion, opening paragraph
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
abbrev fiberSpace (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : GeometricSpace D where
  base := D.geometricFiber T₀
  separated := MorphismProperty.pullback_snd
    (P := @IsSeparated) T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) inferInstance
  finiteType := (FrobeniusExchange.fiber_finiteType D T₀).1
  quasiCompact := (FrobeniusExchange.fiber_finiteType D T₀).2

/-- The common-stage pullback with the prime-invertibility data supplied by the
normalized realization. Source: native expansion, Step 12
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def commonPull (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left) :=
  letI := (R.data T).units
  commonStageDerivedPullback l (PadicAlgCl l) g.hom

/-- Restriction of the actual normalized scalar realization to an ordinary full
subcategory is an equivalence, with the same forward functor rho.
Source: native expansion, Step 14
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
structure EquivalenceData (D : FiniteFieldDatum.{u}) (R : Family l D)
    (T : GeometricSpace D) where
  equivalence : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
    T.base.left ≌ Constructible l T.base.left (R.data T).realization
  forward : equivalence.functor = rho l D R T

/-- The realization bridge retains the specified forward functor, including its arrows.
Source: native expansion, Step 14
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def realizationBridge (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (e : EquivalenceData l D R T) :
    e.equivalence.functor ⋙ (boundedConstructible l T.base.left (R.data T).realization).ι ≅
      ordinary l T.base.left (R.data T).realization :=
  Functor.isoWhiskerRight (eqToIso e.forward) _ ≪≫
    (boundedConstructible l T.base.left (R.data T).realization).liftCompιIso _ _

/-- Restrict the exact ordinary Frobenius to the full constructible subcategory.
The preservation witness is a conclusion below, not an extra geometric hypothesis.
Source: native expansion, Step 13
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def restrictPull (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left)
    (h : ∀ K : Constructible l T.base.left (R.data T).realization,
      boundedConstructible l T.base.left (R.data T).realization
        (((pull l D R T g).mapDerivedCategory).obj K.obj)) :
    Constructible l T.base.left (R.data T).realization ⥤
      Constructible l T.base.left (R.data T).realization :=
  (boundedConstructible l T.base.left (R.data T).realization).lift
    ((boundedConstructible l T.base.left (R.data T).realization).ι ⋙
      (pull l D R T g).mapDerivedCategory) h

/-- Forget a native derived Weil object to the actual ordinary constructible category.
Source: native expansion, opening paragraph and Step 17
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def forgetConstructible (D : FiniteFieldDatum.{u}) (R : Family l D)
    (T : GeometricSpace D) (g : T.base.left ≅ T.base.left)
    [HasDerivedCategory.{u + 1} (Pairs l D R T g)] :
    Weil l D R T g ⥤ Constructible l T.base.left (R.data T).realization :=
  (boundedConstructible l T.base.left (R.data T).realization).lift
    (((boundedConstructible l T.base.left (R.data T).realization).inverseImage
      (forget l D R T g)).ι ⋙ forget l D R T g) (fun K ↦ K.property)

/-- The native structure map inside the full constructible category.
Its ambient arrow is exactly the localized termwise structure arrow.
Source: native expansion, Step 17
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def constructibleTheta (D : FiniteFieldDatum.{u}) (R : Family l D)
    (T : GeometricSpace D) (g : T.base.left ≅ T.base.left)
    [HasDerivedCategory.{u + 1} (Pairs l D R T g)]
    (h : ∀ K : Constructible l T.base.left (R.data T).realization,
      boundedConstructible l T.base.left (R.data T).realization
        (((pull l D R T g).mapDerivedCategory).obj K.obj))
    (L : Weil l D R T g) :
    (restrictPull l D R T g h).obj ((forgetConstructible l D R T g).obj L) ≅
      (forgetConstructible l D R T g).obj L :=
  ObjectProperty.isoMk _ ((theta l D R T g).app L.obj)

/-- Canonical cancellation for the actual inverse reindexing. All comparisons are
localizations of the function-normalized comparisons of the realization family.
Source: native expansion, Steps 12--13
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def pullCancel (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left) :
    (pull l D R T g).mapDerivedCategory ⋙
        (pull l D R T g.symm).mapDerivedCategory ≅ 𝟭 _ := by
  let e := eqToIso (congrArg
    (fun q : T.base.left ≅ T.base.left ↦ pull l D R T q) (Iso.symm_self_id g))
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((R.moduleComp T T T g.symm g).symm ≪≫ e ≪≫ R.moduleId T) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The same canonical cancellation inside the full constructible subcategory.
Source: native expansion, Steps 13--16
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def constructibleCancel (D : FiniteFieldDatum.{u}) (R : Family l D) (T : GeometricSpace D)
    (g : T.base.left ≅ T.base.left)
    (h : ∀ K : Constructible l T.base.left (R.data T).realization,
      boundedConstructible l T.base.left (R.data T).realization
        ((pull l D R T g).mapDerivedCategory.obj K.obj))
    (h' : ∀ K : Constructible l T.base.left (R.data T).realization,
      boundedConstructible l T.base.left (R.data T).realization
        ((pull l D R T g.symm).mapDerivedCategory.obj K.obj)) :
    restrictPull l D R T g h ⋙ restrictPull l D R T g.symm h' ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((pullCancel l D R T g).app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((pullCancel l D R T g).hom.naturality f.hom))

/-- Restrict actual module compact support after proving its constructibility.
Source: native expansion, Steps 13--14
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def restrictCompact {X Y : Scheme.{u}}
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (H : DerivedCategory (modules l X R) ⥤ DerivedCategory (modules l Y S))
    (h : ∀ K : Constructible l X R, boundedConstructible l Y S (H.obj K.obj)) :
    Constructible l X R ⥤ Constructible l Y S :=
  (boundedConstructible l Y S).lift ((boundedConstructible l X R).ι ⋙ H) h

/-- Transport the specified common-stage adjunction, including its unit and counit.
Source: native expansion, Step 14
(blueprint: def-sf-native-weil-scalar-counit-categories). -/
def transportAdjunction {A : Type u₁} {B : Type u₂} {C : Type u₃} {E : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} E]
    (eX : A ≌ C) (eY : B ≌ E) {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) :
    eX.inverse ⋙ F ⋙ eY.functor ⊣ eY.inverse ⋙ G ⋙ eX.functor :=
  eX.symm.toAdjunction.comp (adj.comp eY.toAdjunction)

end WeilConjectures.NativeWeilScalar
