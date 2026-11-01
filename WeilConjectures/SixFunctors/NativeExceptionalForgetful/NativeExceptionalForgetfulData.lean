/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport

/-! # Native exceptional forgetting interface

Source: current blueprint, cor-coef-verdier-weil-equivariance, exceptional adjunction
and equivariant units and counits (blueprint: def-sf-native-exceptional-forgetful-data).
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
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The coefficient characteristic condition follows directly from the finite-field cardinality.
Source: current blueprint, finite-field convention
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance coefficientCharacteristic : Fact (ringChar D.k₀ ≠ l) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  exact ⟨fun h ↦ (Fact.out : l ≠ D.p) (h.symm.trans (ringChar.eq D.k₀ D.p))⟩

/-- A separated finite-type model over the specified finite field.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
structure Space where
  base : Over (Spec (CommRingCat.of D.k₀))
  [separated : IsSeparated base.hom]
  [finiteType : LocallyOfFiniteType base.hom]
  [quasiCompact : QuasiCompact base.hom]

attribute [instance] Space.separated Space.finiteType Space.quasiCompact

/-- The chosen geometric fiber with its structure morphism.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def geometric (T : Space D) : GeometricSpace D where
  base := D.geometricFiber T.base
  separated := inferInstanceAs (IsSeparated (pullback.snd T.base.hom _))
  finiteType := inferInstanceAs (LocallyOfFiniteType (pullback.snd T.base.hom _))
  quasiCompact := inferInstanceAs (QuasiCompact (pullback.snd T.base.hom _))

/-- The model's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance nativeFiniteType (T : Space D) :
    LocallyOfFiniteType (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := T.finiteType

/-- The model's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance nativeQuasiCompact (T : Space D) :
    QuasiCompact (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := T.quasiCompact

/-- The model's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance nativeSeparated (T : Space D) :
    IsSeparated (T.base.left ↘ Spec (CommRingCat.of D.k₀)) := T.separated

/-- The geometric fiber's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricFiniteType (T : Space D) :
    LocallyOfFiniteType ((geometric D T).base.left ↘ Spec (CommRingCat.of D.k)) :=
  (geometric D T).finiteType

/-- The geometric fiber's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricQuasiCompact (T : Space D) :
    QuasiCompact ((geometric D T).base.left ↘ Spec (CommRingCat.of D.k)) :=
  (geometric D T).quasiCompact

/-- The geometric fiber's bundled morphism property in Scheme.Over form.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricSeparated (T : Space D) :
    IsSeparated ((geometric D T).base.left ↘ Spec (CommRingCat.of D.k)) :=
  (geometric D T).separated

/-- Change from the library's algebraic closure to the arbitrary closure in D.
The field equivalence is over the finite field, so this is a geometric-fiber
isomorphism, fixing the model coordinate.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def closureMap (T : Space D) : T.base.hom.geometricFiber ⟶ (geometric D T).base.left :=
  pullback.map T.base.hom (Scheme.specAlgebraicClosure D.k₀).hom
    T.base.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (𝟙 _) (Spec.map (CommRingCat.ofHom
      (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingHom)) (𝟙 _)
    (by simp) (by
      change Spec.map (CommRingCat.ofHom (algebraMap D.k₀ (AlgebraicClosure D.k₀))) ≫
        𝟙 _ = _
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact ((IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).commutes x).symm)

/-- Native bounded constructible Weil complexes with all their derived morphisms.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev W (T : Space D) := WeilComplex D.k₀ l T.base.left

/-- Ordinary module-derived forgetting, transported to the specified closure.
The transport is proper direct image along the displayed fiber isomorphism;
its right derivation is consequently its exact termwise derivation.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def U (R : Family l D) (T : Space D) :
    W D l T ⥤ DerivedCategory (modules l (geometric D T).base.left
      (R.data (geometric D T)).realization) :=
  WeilComplex.forget ⋙ (ProEtale.adicLowerStar l (closureMap D T)).rightDerivedFunctor ⋙
    sectionDerived l (geometric D T).base.left (R.data (geometric D T)).realization

/-- The actual geometric base change of a model morphism.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev geometricMap {X Y : Space D} (f₀ : X.base ⟶ Y.base) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Base change preserves the stated model-morphism property.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricMapSeparated {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] : IsSeparated (geometricMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance

/-- Base change preserves the stated model-morphism property.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricMapFiniteType {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [LocallyOfFiniteType f₀.left] : LocallyOfFiniteType (geometricMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance

/-- Base change preserves the stated model-morphism property.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricMapQuasiCompact {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [QuasiCompact f₀.left] : QuasiCompact (geometricMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance

/-- The native compact-support construction on the model morphism.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev nativeShriek {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    W D l X ⥤ W D l Y :=
  by
    letI : LocallyOfFiniteType (Y.base.left ↘ Spec (CommRingCat.of D.k₀)) := Y.finiteType
    letI : QuasiCompact (Y.base.left ↘ Spec (CommRingCat.of D.k₀)) := Y.quasiCompact
    letI : IsSeparated (Y.base.left ↘ Spec (CommRingCat.of D.k₀)) := Y.separated
    exact WeilComplex.derivedLowerShriek D.k₀ l f₀.left

/-- The finite-field point as a model space.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def point : Space D where
  base := Over.mk (𝟙 (Spec (CommRingCat.of D.k₀)))
  separated := inferInstanceAs (IsSeparated (𝟙 _))
  finiteType := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))

/-- The native constant Weil complex with its canonical Frobenius, in degree zero.
Source: Constant.lean, adicConstant; current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev constant (T : Space D) : W D l T :=
  WeilSheaf.toComplex.obj (WeilSheaf.adicConstant D.k₀ l T.base.left)

/-- The common-stage category on the geometric fiber.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev C (T : Space D) :=
  generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) (geometric D T).base.left

/-- The specified ordinary coefficient realization.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev rho (R : Family l D) (T : Space D) :=
  ordinary l (geometric D T).base.left (R.data (geometric D T)).realization

/-- The coefficient unit R_T[0], using the actual sectionwise regular module.
Source: current blueprint, cor-coef-verdier-weil-equivariance, point-unit clause
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev coefficientUnit (R : Family l D) (T : Space D) :=
  DerivedCategory.Q.obj (ringedTensorUnitComplex.{u + 1, u, u + 1}
    (ProEt.topology (geometric D T).base.left)
    (ring l (geometric D T).base.left (R.data (geometric D T)).realization))

/-- Omega in the common-stage constructible category.
Source: current blueprint, cor-coef-verdier-weil-equivariance, point-unit clause
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def omega (R : Family l D) (T : Space D) : C D l T := by
  letI := (R.data (geometric D T)).units
  exact pullbackTensorCommonUnit l (PadicAlgCl l) (geometric D T).base.left

/-- The prescribed scalar-unit-normalized realization R_T[0] ≅ rho_T(Omega).
Source: BS 6.8.14--6.8.15; current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def unitRealization (R : Family l D) (T : Space D) :
    coefficientUnit D l R T ≅ (rho D l R T).obj (omega D l R T) :=
  by
    letI := (R.data (geometric D T)).units
    exact (R.data (geometric D T)).tensor.coherence.unitIso.symm ≪≫
      (R.data (geometric D T)).tensor.unit

/-- The normalized common-stage exceptional system of the dependency node.
All scalar and compactification normalization is retained in System.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev CoefficientSystem {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] : Type (u + 2) := by
  letI : LocallyOfFiniteType ((geometric D X).base.left ↘ Spec (.of D.k)) :=
    (geometric D X).finiteType
  letI : QuasiCompact ((geometric D X).base.left ↘ Spec (.of D.k)) :=
    (geometric D X).quasiCompact
  letI : LocallyOfFiniteType ((geometric D Y).base.left ↘ Spec (.of D.k)) :=
    (geometric D Y).finiteType
  letI : QuasiCompact ((geometric D Y).base.left ↘ Spec (.of D.k)) :=
    (geometric D Y).quasiCompact
  letI : IsSeparated (geometricMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance
  letI : LocallyOfFiniteType (geometricMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance
  letI : QuasiCompact (geometricMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance
  exact ConstructibleExceptionalCoefficients.System.{u, 0} l (PadicAlgCl l) D
    (Fact.out : l ≠ D.p) (X := (geometric D X).base.left)
    (Y := (geometric D Y).base.left) (f := geometricMap D f₀)

/-- A common-stage model of the actual derived forgetful functor. The natural
isomorphism is defined on every derived morphism, including extension morphisms.
Source: current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
structure ForgetModel (R : Family l D) (T : Space D) where
  functor : W D l T ⥤ C D l T
  realization : functor ⋙ rho D l R T ≅ U D l R T

/-- The two natural comparisons with their specified adjunction units and counits.
These are comparisons after the equivalence rho: whiskering with rho and using
ForgetModel.realization gives exactly the two ordinary module-derived comparisons.
Source: current blueprint, cor-coef-verdier-weil-equivariance, final sentence
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
structure Comparison (R : Family l D) {X Y : Space D}
    (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (G : W D l Y ⥤ W D l X) (adj : nativeShriek D l f₀ ⊣ G) where
  left : nativeShriek D l f₀ ⋙ VY.functor ≅ VX.functor ⋙ (S.ring.operation c .closed).F
  right : G ⋙ VX.functor ≅ VY.functor ⋙ (S.ring.operation c .closed).G
  unit (K : W D l X) :
    VX.functor.map (adj.unit.app K) ≫ right.hom.app ((nativeShriek D l f₀).obj K) ≫
        (S.ring.operation c .closed).G.map (left.hom.app K) =
      (S.ring.operation c .closed).adjunction.unit.app (VX.functor.obj K)
  counit (L : W D l Y) :
    (S.ring.operation c .closed).F.map (right.hom.app L) ≫
        (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L) =
      left.inv.app (G.obj L) ≫ VY.functor.map (adj.counit.app L)

/-- The geometric point literally Spec k, with its identity structure morphism.
Source: current blueprint, cor-coef-verdier-weil-equivariance, point specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def geometricPoint : GeometricSpace D where
  base := Over.mk (𝟙 (Spec (CommRingCat.of D.k)))
  separated := inferInstanceAs (IsSeparated (𝟙 _))
  finiteType := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))

/-- The canonical identification of the geometric fiber of Spec k0 with Spec k.
Its hom is the second pullback projection, so composing the geometric structural
map with it is the structure morphism of geometric D X itself.
Source: current blueprint, cor-coef-verdier-weil-equivariance, point specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def pointGeometricIso : (geometric D (point D)).base.left ≅ Spec (CommRingCat.of D.k) :=
  asIso (pullback.snd (𝟙 (Spec (CommRingCat.of D.k₀)))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- The geometric structural morphism is a morphism over the geometric point.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricStructureIsOver (X : Space D) :
    ((geometric D X).base.hom).IsOver (Spec (CommRingCat.of D.k)) := by
  constructor
  dsimp only [autoParam]
  change (geometric D X).base.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k D.k)) = (geometric D X).base.hom
  simp

/-- Separatedness of the literal geometric structure map.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricStructureSeparated (X : Space D) :
    IsSeparated (geometric D X).base.hom := (geometric D X).separated

/-- Finite type of the literal geometric structure map.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricStructureFiniteType (X : Space D) :
    LocallyOfFiniteType (geometric D X).base.hom := (geometric D X).finiteType

/-- Quasi-compactness of the literal geometric structure map.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
instance geometricStructureQuasiCompact (X : Space D) :
    QuasiCompact (geometric D X).base.hom := (geometric D X).quasiCompact

/-- The normalized exceptional system for the literal geometric structure map a_X.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
abbrev StructuralSystem (X : Space D) : Type (u + 2) :=
  ConstructibleExceptionalCoefficients.System.{u, 0} l (PadicAlgCl l) D (Fact.out : l ≠ D.p)
    (X := (geometric D X).base.left) (Y := Spec (CommRingCat.of D.k))
    (f := (geometric D X).base.hom)

/-- Omega at literal Spec k, for the last assertion of the node.
Source: current blueprint, cor-coef-verdier-weil-equivariance, structural specialization
(blueprint: lem-sf-weil-native-exceptional-forgetful). -/
def geometricPointOmega (R : Family l D) :
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Spec (CommRingCat.of D.k)) := by
  letI : ∀ x : Spec (CommRingCat.of D.k),
      Invertible (l : (Spec (CommRingCat.of D.k)).residueField x) :=
    (R.data (geometricPoint D)).units
  exact pullbackTensorCommonUnit l (PadicAlgCl l) (Spec (CommRingCat.of D.k))

/-- The complete comparison, with one forgetful model at each scheme and the
same comparisons in the structural-morphism specialization. Right adjoints and
adjunctions are quantified only when they exist, precisely as in the assertion.
Source: current blueprint, cor-coef-verdier-weil-equivariance, exceptional-adjunction
and point-unit assertions (blueprint: lem-sf-weil-native-exceptional-forgetful). -/
structure Package (R : Family l D) where
  model : ∀ T : Space D, ForgetModel D l R T
  comparison : ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
      [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
      (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
      (G : W D l Y ⥤ W D l X) (adj : nativeShriek D l f₀ ⊣ G),
    Comparison D l R (model X) (model Y) f₀ S c G adj
  nativeUnit : (U D l R (point D)).obj (constant D l (point D)) ≅
    coefficientUnit D l R (point D)
  commonUnit : (model (point D)).functor.obj (constant D l (point D)) ≅
    omega D l R (point D)
  unit_normalization :
    (model (point D)).realization.hom.app (constant D l (point D)) ≫
        nativeUnit.hom ≫ (unitRealization D l R (point D)).hom =
      (rho D l R (point D)).map commonUnit.hom
  specialization : ∀ (X : Space D) (a₀ : X.base ⟶ (point D).base)
      [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
      (S : CoefficientSystem D l a₀) (c : Compactification (geometricMap D a₀))
      (G : W D l (point D) ⥤ W D l X) (_adj : nativeShriek D l a₀ ⊣ G),
    (U D l R X).obj (G.obj (constant D l (point D))) ≅
      (rho D l R X).obj ((S.ring.operation c .closed).G.obj (omega D l R (point D)))
  specialization_eq : ∀ (X : Space D) (a₀ : X.base ⟶ (point D).base)
      [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
      (S : CoefficientSystem D l a₀) (c : Compactification (geometricMap D a₀))
      (G : W D l (point D) ⥤ W D l X) (adj : nativeShriek D l a₀ ⊣ G),
    (specialization X a₀ S c G adj).hom =
      (model X).realization.inv.app (G.obj (constant D l (point D))) ≫
        (rho D l R X).map
          ((comparison X (point D) a₀ S c G adj).right.hom.app (constant D l (point D)) ≫
            (S.ring.operation c .closed).G.map commonUnit.hom)

  actualSpecialization : ∀ (X : Space D) (a₀ : X.base ⟶ (point D).base)
      [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
      (S : StructuralSystem D l X) (c : Compactification (geometric D X).base.hom)
      (G : W D l (point D) ⥤ W D l X) (_adj : nativeShriek D l a₀ ⊣ G),
    (U D l R X).obj (G.obj (constant D l (point D))) ≅
      (rho D l R X).obj ((S.ring.operation c .closed).G.obj (geometricPointOmega D l R))

end WeilConjectures.NativeExceptionalForgetful
