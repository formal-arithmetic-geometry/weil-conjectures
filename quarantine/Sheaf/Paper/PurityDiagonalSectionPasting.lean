/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q21, N8
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
/-!
# Pasting the orientation-free diagonal section comparison

Source: blueprint main-20261015, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-diagonal-section-pasting).

Every map below is in the canonical etale presentation of the finite pro-etale
constructible category. The comparison-site pullback is fully faithful on these objects;
comparedSectionPresentation identifies the actual section object, and
finiteComparedDualizing is the unit-normalized exceptional image. Thus the equalities specify
the pro-etale maps, including their units, counits, tensors and pullback reassociations.
No orientation or Tate-twist identification occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The finite coefficient exponent is invertible on every scheme over the fixed field.
Source: blueprint def-pur-conventions, the finite coefficient paragraph
(blueprint: def-pur-conventions).
Proof: ell to the positive level annihilates the coefficient quotient, since the
valuation of ell in O_E is positive. The same integer is nonzero in k, hence a unit;
its image along the structure morphism is a unit in global sections. -/
theorem comparedExponent (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of P.field.k)) : HasInvertibleExponent P.Coefficient T := by
  sorry

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

section GenericUnit

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- Evaluate the exceptional compositor at the coefficient unit before specializing
its coefficient category. This preserves the upstream generic derived-unit term.
Source: blueprint sigma, exceptional compositor at the unit
(blueprint: lem-pur-diagonal-section-pasting). -/
def exceptionalUnit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [(Etale.rightDerivedLowerShriek C f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C g).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C (f ≫ g)).IsLeftAdjoint]
    (c : Etale.rightDerivedUpperShriek C (f ≫ g) ≅
      Etale.rightDerivedUpperShriek C g ⋙ Etale.rightDerivedUpperShriek C f) :
    Etale.dualizingComplex C (f ≫ g) ≅
      (Etale.rightDerivedUpperShriek C f).obj (Etale.dualizingComplex C g) :=
  c.app (𝟙_ _)

/-- Evaluate normalized etale localization at the same generic coefficient unit.
Source: blueprint E_(v,h) at the unit
(blueprint: lem-pur-diagonal-section-pasting). -/
def restrictionUnit {U X B : Scheme.{u}} (v' : U ⟶ X) (h : X ⟶ B)
    [HasCompactification h] [HasCompactification (v' ≫ h)]
    [(Etale.rightDerivedLowerShriek C h).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek C (v' ≫ h)).IsLeftAdjoint]
    (c : Etale.rightDerivedUpperShriek C h ⋙ (Etale.upperStar C v').mapDerivedCategory ≅
      Etale.rightDerivedUpperShriek C (v' ≫ h)) :
    Etale.dualizingComplex C (v' ≫ h) ≅
      (Etale.upperStar C v').mapDerivedCategory.obj (Etale.dualizingComplex C h) :=
  (c.app (𝟙_ _)).symm

section TensorMate

variable [Etale.UpperStarPreservesFlat C]
  {FC : C → C → Type w} {CC : C → Type (u + 1)}
  [∀ (M N : C), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} C FC]
  [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget C)]
  [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget C)]

/-- Package the specified tensor mate before specializing its coefficient category.
This uses the generic source term of the published mate, avoiding comparison of
concrete monoidal instances when applying asIso.
Source: blueprint sigma, theta at omega_v (blueprint: lem-pur-diagonal-section-pasting). -/
def tensorMateIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(Etale.rightDerivedLowerShriek C f).IsLeftAdjoint]
    [IsIso (Etale.projectionMap C f)]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (h : IsIso (Etale.dualizingComplexTensorMapOfIsIso f K)) :
    ((Etale.derivedTensor C X).obj (Etale.dualizingComplex C f)).obj
      ((Etale.upperStar C f).leftDerivedFunctor.obj K) ≅
        (Etale.rightDerivedUpperShriek C f).obj K :=
  @asIso _ _ _ _ (Etale.dualizingComplexTensorMapOfIsIso f K) h

end TensorMate

/-- Package the specified finite-coefficient tensor mate before specializing the ring.
Source: blueprint sigma, theta at omega_v (blueprint: lem-pur-diagonal-section-pasting). -/
def finiteThetaIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso (Etale.dualizingComplexTensorMap Λ f K)) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K) ≅
          (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  tensorMateIso (ModuleCat.{u + 1} Λ) f K h

end GenericUnit

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The finite etale presentation of the derived category used in the comparisons.
Source: blueprint finite coefficient conventions
(blueprint: lem-pur-diagonal-section-pasting). -/
abbrev D (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] (X : Scheme.{u}) :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The existing derived tensor bifunctor in finite etale coordinates. Writing
this bifunctor explicitly avoids comparing the two equal concrete monoidal
instance terms, as required by the upstream TensorStructure interface.
Source: blueprint derived-operation conventions
(blueprint: lem-pur-diagonal-section-pasting). -/
abbrev tensor (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X : Scheme.{u}} (K M : D Λ P X) : D Λ P X :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M

/-- Apply the existing tensor bifunctor to a pair of isomorphisms.
Source: blueprint monoidal reassociation in kappa and nu
(blueprint: lem-pur-diagonal-section-pasting). -/
def tensorComparison (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X : Scheme.{u}}
    {K K' M M' : D Λ P X} (a' : K ≅ K') (b' : M ≅ M') :
    tensor Λ P K M ≅ tensor Λ P K' M' :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso a').app M ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K').mapIso b'

/-- Equality of the actual small pro-etale arrows in canonical etale-origin
coordinates. Every arrow is carried by the dependency's comparison inverse image.
Source: blueprint finite pro-etale operations and comparison convention
(blueprint: lem-pur-diagonal-section-pasting). -/
def SameProEtaleMap (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X : Scheme.{u}}
    {K L : D Λ P X} (r t : K ⟶ L) : Prop :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map r =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map t

/-- The self-product section object, using the dependency's section invariant.
Source: blueprint lem-pur-diagonal-section-pasting, C_h
(blueprint: lem-pur-diagonal-section-pasting). -/
def diagonalSection (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] : D Λ P X :=
  Etale.sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f)

/-- The specified smooth tensor mate is invertible in the fixed finite setting.
Source: blueprint thm-pur-cohomological-smoothness, clause 2
(blueprint: lem-pur-diagonal-section-pasting).
Proof: pull the coefficient exponent from the fixed field to X along aX. Apply
the orientation-free smooth tensor theorem to f and K; its canonical form states
invertibility of this exact projection-counit mate, without a Tate-twist datum. -/
theorem thetaIsIso (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [SmoothOfRelativeDimension d f]
    (K : D Λ P Y) (aX : X ⟶ Spec (.of P.field.k)) :
    IsIso (Etale.dualizingComplexTensorMap Λ f K) := by
  sorry

/-- The specified smooth base-change mate is invertible in the fixed finite setting.
Source: blueprint thm-pur-cohomological-smoothness, clause 3
(blueprint: lem-pur-diagonal-section-pasting).
Proof: pull the coefficient exponent from the fixed field to X along aX. Smooth base change
makes the canonical exceptional mate an isomorphism for the Cartesian square.
Its unit component, followed by the canonical pullback-unit isomorphism, is
exactly dualizingComplexBaseChangeMap, hence is invertible. -/
theorem betaIsIso (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v' : Y' ⟶ Y} {u' : X' ⟶ X}
    (d : ℕ) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f] (sq : IsPullback u' f' f v')
    (aX : X ⟶ Spec (.of P.field.k)) :
    IsIso (Etale.dualizingComplexBaseChangeMap Λ sq) := by
  sorry

/-- The specified smooth tensor mate, as an isomorphism on its actual source.
Source: blueprint sigma and def-pur-co-smoothness, clause 2
(blueprint: lem-pur-diagonal-section-pasting). -/
def thetaIso (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [SmoothOfRelativeDimension d f]
    (K : D Λ P Y) (aX : X ⟶ Spec (.of P.field.k)) :=
  finiteThetaIso Λ f K (thetaIsIso Λ P d f K aX)

/-- The exceptional compositor at the unit, in the dualizing-object interface.
Source: blueprint sigma, c at the unit
(blueprint: lem-pur-diagonal-section-pasting). -/
def compositionUnit (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g) :=
  exceptionalUnit (ModuleCat.{u + 1} Λ) f g (finiteExceptionalComposition Λ f g)

/-- Sigma is exactly theta, with its source symmetry already inserted, followed by
inverse exceptional composition. The published theta here orders omega first.
Source: blueprint lem-pur-diagonal-section-pasting, definition of sigma
(blueprint: lem-pur-diagonal-section-pasting). -/
def sigma (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] [SmoothOfRelativeDimension d f]
    (aX : X ⟶ Spec (.of P.field.k)) :=
  thetaIso Λ P d f (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g) aX ≪≫
    (compositionUnit Λ P f g).symm

/-- The canonical self-product base-change map and pullback along its diagonal.
Source: blueprint lem-pur-diagonal-section-pasting, alpha_h
(blueprint: lem-pur-diagonal-section-pasting). -/
def alpha (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (aX : X ⟶ Spec (.of P.field.k)) :
    diagonalSection Λ P f ≅ Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f :=
  letI := betaIsIso Λ P d (IsPullback.of_hasPullback f f).flip aX
  finiteDiagonalRestriction Λ f
    (asIso (Etale.dualizingComplexBaseChangeMap Λ
      (IsPullback.of_hasPullback f f).flip))



/-- The universal-product map a(x1,x2)=(x1,f(x2)).
Source: blueprint lem-pur-diagonal-section-pasting, Q and W
(blueprint: lem-pur-diagonal-section-pasting). -/
def a {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) (f ≫ g) ⟶ pullback (f ≫ g) g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f)
    ((pullback.condition (f := f ≫ g) (g := f ≫ g)).trans (Category.assoc _ f g).symm)

/-- The graph section s=(id,f).
Source: blueprint lem-pur-diagonal-section-pasting, s
(blueprint: lem-pur-diagonal-section-pasting). -/
def s {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ pullback (f ≫ g) g :=
  pullback.lift (𝟙 X) f (Category.id_comp (f ≫ g))

/-- The natural inclusion W_f into W_gf.
Source: blueprint lem-pur-diagonal-section-pasting, proof Step 4
(blueprint: lem-pur-diagonal-section-pasting). -/
def i {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback f f ⟶ pullback (f ≫ g) (f ≫ g) :=
  pullback.map f f (f ≫ g) (f ≫ g) (𝟙 X) (𝟙 X) g
    (Category.id_comp (f ≫ g)).symm (Category.id_comp (f ≫ g)).symm

/-- The natural map j(x,y)=(f(x),y) to W_g.
Source: blueprint lem-pur-diagonal-section-pasting, proof Step 4
(blueprint: lem-pur-diagonal-section-pasting). -/
def j {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) g ⟶ pullback g g :=
  pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 Z)
    (Category.comp_id (f ≫ g))
    ((Category.comp_id g).trans (Category.id_comp g).symm)

/-- The actual two Cartesian squares and their section identities.
Source: blueprint lem-pur-diagonal-section-pasting, proof Steps 1 and 4
(blueprint: lem-pur-diagonal-section-pasting).
Proof: apply the pullback universal property to the displayed pair coordinates.
Both cones represent the same pairs satisfying respectively f(x)=y and g(y)=gf(x).
Projection identities prove the section equations, including the empty case. -/
theorem geometry {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (i f g) (pullback.fst f f) (a f g) (s f g) ∧
    IsPullback (j f g) (pullback.fst (f ≫ g) g) (pullback.fst g g) f ∧
    a f g ≫ pullback.fst (f ≫ g) g = pullback.fst (f ≫ g) (f ≫ g) ∧
    pullback.diagonal (f ≫ g) ≫ a f g = s f g ∧
    pullback.diagonal f ≫ i f g = pullback.diagonal (f ≫ g) ∧
    s f g ≫ j f g = f ≫ pullback.diagonal g := by
  sorry

/-- The smooth dimensions and separated finite-type properties of the pasted tower.
Source: blueprint lem-pur-diagonal-section-pasting, proof Step 1
(blueprint: lem-pur-diagonal-section-pasting).
Proof: a is the base change of f along the second projection Q to Y, and b is the
base change of g along gf. Base-change permanence gives their dimensions d,e and
their separated finite-type properties. Composition gives dimension d+e. -/
theorem geometryProperties {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    SmoothOfRelativeDimension d (a f g) ∧ IsSeparated (a f g) ∧
    LocallyOfFiniteType (a f g) ∧ QuasiCompact (a f g) ∧
    SmoothOfRelativeDimension (d + e) (f ≫ g) := by
  sorry

/-- Equality transport of the dualizing object, with no choice of comparison.
Source: blueprint canonical Cartesian product identifications
(blueprint: lem-pur-diagonal-section-pasting). -/
def dualizingCongr (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g] (h : f = g) :
    Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) g :=
  h ▸ Iso.refl _

/-- The specified smooth base-change counit mate.
Source: blueprint theta and beta conventions, proof Steps 2--4
(blueprint: lem-pur-diagonal-section-pasting). -/
def beta (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {u' : X' ⟶ X}
    (d : ℕ) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f] (sq : IsPullback u' f' f v)
    (aX : X ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
        Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f' :=
  letI := betaIsIso Λ P d sq aX
  asIso (Etale.dualizingComplexBaseChangeMap Λ sq)

/-- The first input comparison gamma_f is pullback of beta_(a,s) inverse.
Source: blueprint lem-pur-diagonal-section-pasting, proof Step 4
(blueprint: lem-pur-diagonal-section-pasting). -/
def gammaF (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification (f ≫ g)] [HasCompactification (a f g)]
    [QuasiCompact f] [SmoothOfRelativeDimension d (a f g)]
    (aZ : Z ⟶ Spec (.of P.field.k)) :
    diagonalSection Λ P f ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ)
        (pullback.diagonal (f ≫ g))).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (a f g)) :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f)).leftDerivedFunctor.mapIso
        (beta Λ P d (geometry f g).1
          (pullback.fst (f ≫ g) (f ≫ g) ≫ (f ≫ g) ≫ aZ)).symm ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f) (i f g) (pullback.diagonal (f ≫ g))
        (geometry f g).2.2.2.2.1.symm).app _).symm

/-- The second input comparison gamma_g is pullback of beta_(p_g,f).
Source: blueprint lem-pur-diagonal-section-pasting, proof Step 4
(blueprint: lem-pur-diagonal-section-pasting). -/
def gammaG (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact g]
    [SmoothOfRelativeDimension e (pullback.fst g g)]
    (aZ : Z ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
      (diagonalSection Λ P g) ≅
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (s f g)).leftDerivedFunctor.obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ)
        (pullback.fst (f ≫ g) g)) :=
  ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      f (pullback.diagonal g)).app _).symm ≪≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (s f g) (j f g) (f ≫ pullback.diagonal g)
        (geometry f g).2.2.2.2.2.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) (s f g)).leftDerivedFunctor.mapIso
      (beta Λ P e (geometry f g).2.1 (pullback.fst g g ≫ g ≫ aZ))

/-- The section-pasting arrow is the two canonical input comparisons, monoidal
pullback reassociation, pullback of sigma_(a,b), and equality ba=p_gf.
Source: blueprint lem-pur-diagonal-section-pasting, definition of kappa
(blueprint: lem-pur-diagonal-section-pasting). -/
def kappa (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification (a f g)]
    [HasCompactification (a f g ≫ pullback.fst (f ≫ g) g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (a f g)]
    [SmoothOfRelativeDimension d (a f g)]
    [SmoothOfRelativeDimension e (pullback.fst g g)]
    (aZ : Z ⟶ Spec (.of P.field.k)) :
    tensor Λ P (diagonalSection Λ P f)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
        (diagonalSection Λ P g)) ≅ diagonalSection Λ P (f ≫ g) :=
  tensorComparison Λ P (gammaF Λ P d f g aZ)
      (gammaG Λ P e f g aZ ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
          (pullback.diagonal (f ≫ g)) (a f g) (s f g)
            (geometry f g).2.2.2.1.symm).app _) ≪≫
    -- Keep the scheme arguments and both factors explicit: inferring them compares
    -- concrete monoidal instance terms in this canonical pullback comparison.
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ)
      (Y := pullback (f ≫ g) (f ≫ g)) (Z := X)
      (pullback.diagonal (f ≫ g))
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (a f g))
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a f g)).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ)
          (pullback.fst (f ≫ g) g)))).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.diagonal (f ≫ g))).leftDerivedFunctor.mapIso
        (sigma Λ P d (a f g) (pullback.fst (f ≫ g) g)
            (pullback.fst (f ≫ g) (f ≫ g) ≫ (f ≫ g) ≫ aZ) ≪≫
          dualizingCongr Λ P (geometry f g).2.2.1)



/-- The diagonal pasting equation with every auxiliary compactification supplied
by Nagata and every auxiliary dimension supplied by base change.
Source: blueprint lem-pur-diagonal-section-pasting, first asserted equality
(blueprint: lem-pur-diagonal-section-pasting). -/
def Equation (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian aZ
  letI := QuasiCompact.compactSpace_of_compactSpace aZ
  letI : IsNoetherian Z := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian g
  letI := QuasiCompact.compactSpace_of_compactSpace g
  letI : IsNoetherian Y := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian f
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := ⟨⟩
  let hgeom := geometryProperties d e f g
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2
  SameProEtaleMap Λ P
    ((kappa Λ P d e f g aZ).hom ≫ (alpha Λ P (d + e) (f ≫ g) ((f ≫ g) ≫ aZ)).hom)
    ((tensorComparison Λ P (alpha Λ P d f (f ≫ g ≫ aZ))
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.mapIso
        (alpha Λ P e g (g ≫ aZ)))).hom ≫ (sigma Λ P d f g (f ≫ g ≫ aZ)).hom)

/-- Finite-type base change over a Noetherian source stays Noetherian.
Source: blueprint proof Steps 1 and 9 (blueprint: lem-pur-diagonal-section-pasting).
Proof: the first projection is finite type by base change. Its source is locally
Noetherian over the locally Noetherian first factor and quasi-compact over its
quasi-compact first factor, hence is Noetherian. -/
theorem noetherianPullback {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsNoetherian X] [LocallyOfFiniteType g] [QuasiCompact g] :
    IsNoetherian (pullback f g) := by
  sorry

attribute [instance] noetherianPullback

/-- The normalized etale localization comparison, selected from the dependency's
unique counit-normalized isomorphism, not from a mere existence of an isomorphism.
Source: blueprint proof Steps 7 and 9--12, E_(u,h)
(blueprint: lem-pur-diagonal-section-pasting). -/
def etaleRestriction (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {U X S : Scheme.{u}}
    (v : U ⟶ X) (h : X ⟶ S)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [HasCompactification h] [HasCompactification (v ≫ h)] :
    Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (v ≫ h) ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h) :=
  let E := Classical.choose
    (Etale.existsUnique_etaleAmbientAdjointLocalityIso Λ v h
      (HasCompactification.compactification h)
      (HasCompactification.compactification (v ≫ h))
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h)
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (v ≫ h))
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) h)
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (v ≫ h))).exists
  restrictionUnit (ModuleCat.{u + 1} Λ) v h E ≪≫
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} Λ) v).app _).symm

/-- Canonical comparison of section invariants along an etale map over the base.
The only identifications are equality transport, normalized etale localization,
and the recorded derived pullback compositor.
Source: blueprint proof Steps 9--12 (blueprint: lem-pur-diagonal-section-pasting). -/
def etaleSection (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {U X B : Scheme.{u}}
    (v : U ⟶ X) (h : X ⟶ B) (h' : U ⟶ B) (r : B ⟶ U) (z : B ⟶ X)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [HasCompactification h] [HasCompactification h'] [HasCompactification (v ≫ h)]
    (hv : h' = v ≫ h) (hz : z = r ≫ v) :
    Etale.sectionInvariant Λ h' r ≅
      Etale.sectionInvariant Λ h z :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ) r).leftDerivedFunctor.mapIso
    (dualizingCongr Λ P hv ≪≫ etaleRestriction Λ P v h) ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      r v z hz).app _).symm

/-- Affine r-space, with the explicit size lift of its finite coordinate set.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
abbrev A (r : ℕ) (B : Scheme.{u}) := AffineSpace (ULift.{u} (Fin r)) B

/-- The affine-space projection.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
abbrev pr (r : ℕ) (B : Scheme.{u}) : A r B ⟶ B := A r B ↘ B

/-- The zero section; its coordinates are literally zero.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
abbrev zero (r : ℕ) (B : Scheme.{u}) : B ⟶ A r B := AffineSpace.zeroSection _ _

/-- The ordered block projection forgetting the first d coordinates.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
def q (d e : ℕ) (B : Scheme.{u}) : A (d + e) B ⟶ A e B :=
  AffineSpace.reindex (fun i : ULift.{u} (Fin e) => ULift.up (Fin.natAdd d i.down)) B

/-- The first coordinate block.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
def first (d e : ℕ) (B : Scheme.{u}) : A (d + e) B ⟶ A d B :=
  AffineSpace.reindex (fun i : ULift.{u} (Fin d) => ULift.up (Fin.castAdd e i.down)) B

/-- The actual Cartesian affine-space square and its zero-section identities.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting).
Proof: the polynomial-algebra universal property splits a (d+e)-tuple into its two
ordered blocks. The inverse concatenates the tuples. Both compositions are identity
on every coordinate, also for an empty block. Applying this to the zero tuple proves
the section identities. Smoothness of q is base change of the d-space projection. -/
theorem affineGeometry (d e : ℕ) (B : Scheme.{u}) :
    IsPullback (first d e B) (q d e B) (pr d B) (pr e B) ∧
    zero (d + e) B ≫ first d e B = zero d B ∧
    zero (d + e) B ≫ q d e B = zero e B ∧
    q d e B ≫ pr e B = pr (d + e) B ∧
    SmoothOfRelativeDimension d (q d e B) ∧ IsSeparated (q d e B) ∧
    LocallyOfFiniteType (q d e B) ∧ QuasiCompact (q d e B) ∧
    SmoothOfRelativeDimension d (pr d B) := by
  sorry

/-- The projection of r-space has pure relative dimension r.
Source: blueprint sbc-lem-affine-space-smooth
(blueprint: lem-pur-diagonal-section-pasting).
Proof: the published affine-space smoothness instance has dimension the cardinality
of the coordinate set ULift (Fin r), which is r. -/
theorem affineDimension (r : ℕ) (B : Scheme.{u}) :
    SmoothOfRelativeDimension r (pr r B) := by
  sorry

/-- D_r is the zero-section invariant, without a Tate-twist identification.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
def zeroInvariant (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] (r : ℕ) (B : Scheme.{u})
    [HasCompactification (pr r B)] : D Λ P B :=
  Etale.sectionInvariant Λ (pr r B) (zero r B)

/-- Affine space over a Noetherian base is Noetherian.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting).
Proof: the affine projection is finite type, giving locally Noetherian source;
its quasi-compactness and compactness of B give compactness of the source. -/
theorem affineNoetherian (r : ℕ) (B : Scheme.{u}) [IsNoetherian B] :
    IsNoetherian (A r B) := by
  sorry

attribute [instance] affineNoetherian

/-- The specified affine-space comparison nu. First apply beta inverse and pullback
composition on the two factors; then monoidal pullback and pullback of sigma.
Source: blueprint proof Step 8 (blueprint: lem-pur-diagonal-section-pasting). -/
def nu (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] (d e : ℕ) (B : Scheme.{u})
    [IsNoetherian B] (aB : B ⟶ Spec (.of P.field.k)) :
    tensor Λ P (zeroInvariant Λ P d B) (zeroInvariant Λ P e B) ≅ zeroInvariant Λ P (d + e) B :=
  letI := (affineGeometry d e B).2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.2
  letI := affineDimension e B
  let b := beta Λ P d (affineGeometry d e B).1 (pr d B ≫ aB)
  let c₁ := ((Etale.upperStar (ModuleCat.{u + 1} Λ)
      (zero (d + e) B)).leftDerivedFunctor.mapIso b.symm ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (zero (d + e) B) (first d e B) (zero d B)
      (affineGeometry d e B).2.1.symm).app _).symm).symm
  let c₂ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    (zero (d + e) B) (q d e B) (zero e B)
    (affineGeometry d e B).2.2.1.symm).app
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (pr e B))
  tensorComparison Λ P c₁ c₂ ≪≫
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ)
      (zero (d + e) B) _ _).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (zero (d + e) B)).leftDerivedFunctor.mapIso
        (sigma Λ P d (q d e B) (pr e B) (pr (d + e) B ≫ aB) ≪≫
          dualizingCongr Λ P (affineGeometry d e B).2.2.2.1)




/-- The source-open factorization through the target-open Cartesian base change.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def openFactor {X Y X' Y' : Scheme.{u}} (h : X ⟶ Y) (h' : X' ⟶ Y')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : u' ≫ h = h' ≫ v) :
    X' ⟶ pullback h v := pullback.lift u' h' w

/-- The residual factor is an open immersion; this does not assert that the
original compatible open square was Cartesian.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting).
Proof: target base change restricts X to h inverse image of Y'. Since u maps into
this inverse image, its factor is the same open immersion into that open subset.
The two projection equations are the universal-property equations. -/
theorem openFactorProperties {X Y X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (h' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion u'] [IsOpenImmersion v] (w : u' ≫ h = h' ≫ v) :
    IsOpenImmersion (openFactor h h' u' v w) ∧
    openFactor h h' u' v w ≫ pullback.fst h v = u' ∧
    openFactor h h' u' v w ≫ pullback.snd h v = h' := by
  sorry

/-- Restriction of the dualizing object for arbitrary compatible source and target
opens: target base change first, then normalized source etale localization.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def openDualizing (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    (d : ℕ) (h : X ⟶ Y) (h' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    [IsOpenImmersion u'] [IsOpenImmersion v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension d h]
    (w : u' ≫ h = h' ≫ v) (aX : X ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h' :=
  let j := openFactor h h' u' v w
  letI := (openFactorProperties h h' u' v w).1
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    j (pullback.fst h v) u'
    (openFactorProperties h h' u' v w).2.1.symm).app _ ≪≫
  (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.mapIso
    (beta Λ P d (IsPullback.of_hasPullback h v) aX) ≪≫
  (etaleRestriction Λ P j (pullback.snd h v)).symm ≪≫
  dualizingCongr Λ P (openFactorProperties h h' u' v w).2.2

/-- Restrict both factors of the diagonal self-product.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def openPair {X Y X' Y' : Scheme.{u}} (h : X ⟶ Y) (h' : X' ⟶ Y')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : u' ≫ h = h' ≫ v) :
    pullback h' h' ⟶ pullback h h :=
  pullback.map h' h' h h u' u' v w.symm w.symm

/-- Simultaneous restriction of the two factors is open, and the diagonal factors
through that restriction.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting).
Proof: the map is the restriction of the open product u times u to the locus where
the images in Y' agree. Because v is a monomorphism this is exactly the inverse
image of W_h. Projection and diagonal equations follow from the pullback property. -/
theorem openPairProperties {X Y X' Y' : Scheme.{u}}
    (h : X ⟶ Y) (h' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion u'] [IsOpenImmersion v] (w : u' ≫ h = h' ≫ v) :
    IsOpenImmersion (openPair h h' u' v w) ∧
    openPair h h' u' v w ≫ pullback.fst h h = pullback.fst h' h' ≫ u' ∧
    pullback.diagonal h' ≫ openPair h h' u' v w = u' ≫ pullback.diagonal h := by
  sorry

/-- Restriction of C_h by restricting both factors and using the normalized
exceptional comparison on their first projections.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def openSection (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    (d : ℕ) (h : X ⟶ Y) (h' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    [IsOpenImmersion u'] [IsOpenImmersion v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension d h]
    (w : u' ≫ h = h' ≫ v) (aX : X ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
      (diagonalSection Λ P h) ≅ diagonalSection Λ P h' :=
  letI := (openPairProperties h h' u' v w).1
  ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    u' (pullback.diagonal h)).app _).symm ≪≫
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    (pullback.diagonal h') (openPair h h' u' v w)
    (u' ≫ pullback.diagonal h)
    (openPairProperties h h' u' v w).2.2.symm).app _ ≪≫
  (Etale.upperStar (ModuleCat.{u + 1} Λ)
    (pullback.diagonal h')).leftDerivedFunctor.mapIso
      (openDualizing Λ P d (pullback.fst h h) (pullback.fst h' h')
        (openPair h h' u' v w) u'
        (openPairProperties h h' u' v w).2.1 (pullback.fst h h ≫ aX))

/-- Difference coordinates for the self-product of the first chart.
Source: blueprint proof Step 11 (blueprint: lem-pur-diagonal-section-pasting). -/
def differenceFirst {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (x : X ⟶ A d Y) : pullback f f ⟶ A d X :=
  AffineSpace.homOfVector (pullback.fst f f) fun k =>
    (pullback.snd f f).appTop (x.appTop (AffineSpace.coord Y k)) -
      (pullback.fst f f).appTop (x.appTop (AffineSpace.coord Y k))

/-- Difference coordinates G(x,y)=y(y)-y(f(x)) on Q.
Source: blueprint proof Step 9 (blueprint: lem-pur-diagonal-section-pasting). -/
def differenceSecond {X Y Z : Scheme.{u}} (e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (y : Y ⟶ A e Z) : pullback (f ≫ g) g ⟶ A e X :=
  AffineSpace.homOfVector (pullback.fst (f ≫ g) g) fun k =>
    (pullback.snd (f ≫ g) g).appTop (y.appTop (AffineSpace.coord Z k)) -
      (pullback.fst (f ≫ g) g ≫ f).appTop (y.appTop (AffineSpace.coord Z k))

/-- The ordered total difference map F, with the x-block before the y-block.
Source: blueprint proof Step 9 (blueprint: lem-pur-diagonal-section-pasting). -/
def differenceTotal {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X ⟶ A d Y) (y : Y ⟶ A e Z) :
    pullback (f ≫ g) (f ≫ g) ⟶ A (d + e) X :=
  AffineSpace.homOfVector (pullback.fst (f ≫ g) (f ≫ g)) fun k =>
    Fin.addCases
      (fun l => (pullback.snd (f ≫ g) (f ≫ g)).appTop
          (x.appTop (AffineSpace.coord Y (ULift.up l))) -
        (pullback.fst (f ≫ g) (f ≫ g)).appTop
          (x.appTop (AffineSpace.coord Y (ULift.up l))))
      (fun l => (pullback.snd (f ≫ g) (f ≫ g) ≫ f).appTop
          (y.appTop (AffineSpace.coord Z (ULift.up l))) -
        (pullback.fst (f ≫ g) (f ≫ g) ≫ f).appTop
          (y.appTop (AffineSpace.coord Z (ULift.up l)))) k.down

/-- The chart difference maps are etale, separated and finite type, and carry the
specified sections to the zero sections. No non-Cartesian square is called Cartesian.
Source: blueprint proof Steps 9 and 11 (blueprint: lem-pur-diagonal-section-pasting).
Proof: G is the base change of y followed by translation. Factor F through
R=Q times_(A^e_X) A^(d+e)_X. Its first factor is the base change of x followed
by translation, and its second factor is the base change of G. Thus all three
maps are etale. The schemes are affine and Noetherian, so their maps are separated
and finite type. Projection equations follow from homOfVector; diagonal difference
coordinates are zero. This includes empty schemes and either empty coordinate block. -/
theorem chartGeometry {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffine X] [IsAffine Y] [IsAffine Z]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (x : X ⟶ A d Y) (y : Y ⟶ A e Z) [Etale x] [Etale y]
    (hx : x ≫ pr d Y = f) (hy : y ≫ pr e Z = g) :
    (Etale (differenceFirst d f x) ∧ IsSeparated (differenceFirst d f x) ∧
      LocallyOfFiniteType (differenceFirst d f x) ∧ QuasiCompact (differenceFirst d f x)) ∧
    (Etale (differenceSecond e f g y) ∧ IsSeparated (differenceSecond e f g y) ∧
      LocallyOfFiniteType (differenceSecond e f g y) ∧ QuasiCompact (differenceSecond e f g y)) ∧
    (Etale (differenceTotal d e f g x y) ∧ IsSeparated (differenceTotal d e f g x y) ∧
      LocallyOfFiniteType (differenceTotal d e f g x y) ∧
      QuasiCompact (differenceTotal d e f g x y)) ∧
    differenceFirst d f x ≫ pr d X = pullback.fst f f ∧
    pullback.diagonal f ≫ differenceFirst d f x = zero d X ∧
    differenceSecond e f g y ≫ pr e X = pullback.fst (f ≫ g) g ∧
    s f g ≫ differenceSecond e f g y = zero e X ∧
    differenceTotal d e f g x y ≫ pr (d + e) X = pullback.fst (f ≫ g) (f ≫ g) ∧
    pullback.diagonal (f ≫ g) ≫ differenceTotal d e f g x y = zero (d + e) X := by
  sorry

/-- The coordinate assertion, in the actual difference-coordinate identifications.
On an affine restricted chart triple the common base is X (the U of the statement).
Source: blueprint proof Steps 8--12 (blueprint: lem-pur-diagonal-section-pasting). -/
def ChartEquation (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffine X] [IsAffine Y] [IsAffine Z]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k))
    (x : X ⟶ A d Y) (y : Y ⟶ A e Z) [Etale x] [Etale y]
    (hx : x ≫ pr d Y = f) (hy : y ≫ pr e Z = g) : Prop :=
  let h := chartGeometry d e f g x y hx hy
  letI := h.1.1
  letI := h.1.2.1
  letI := h.1.2.2.1
  letI := h.1.2.2.2
  letI := h.2.1.1
  letI := h.2.1.2.1
  letI := h.2.1.2.2.1
  letI := h.2.1.2.2.2
  letI := h.2.2.1.1
  letI := h.2.2.1.2.1
  letI := h.2.2.1.2.2.1
  letI := h.2.2.1.2.2.2
  let hgeom := geometryProperties d e f g
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2
  let c₁ := etaleSection Λ P (differenceFirst d f x) (pr d X)
    (pullback.fst f f) (pullback.diagonal f) (zero d X)
    h.2.2.2.1.symm h.2.2.2.2.1.symm
  let c₂ := gammaG Λ P e f g aZ ≪≫
    etaleSection Λ P (differenceSecond e f g y) (pr e X)
      (pullback.fst (f ≫ g) g) (s f g) (zero e X)
      h.2.2.2.2.2.1.symm h.2.2.2.2.2.2.1.symm
  let c₃ := etaleSection Λ P (differenceTotal d e f g x y) (pr (d + e) X)
    (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)) (zero (d + e) X)
    h.2.2.2.2.2.2.2.1.symm h.2.2.2.2.2.2.2.2.symm
  SameProEtaleMap Λ P ((kappa Λ P d e f g aZ).hom ≫ c₃.hom)
    ((tensorComparison Λ P c₁ c₂).hom ≫ (nu Λ P d e X (f ≫ g ≫ aZ)).hom)

/-- The canonical restriction comparison for a tensor with a pulled-back second
factor. It is built only from the monoidal pullback and composition comparisons.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def tensorRestriction (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    (w : u' ≫ f = f' ≫ v) (K : D Λ P X) (M : D Λ P Y) (K' : D Λ P X') (M' : D Λ P Y')
    (e₁ : (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj K ≅ K')
    (e₂ : (Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj M ≅ M') :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
      (tensor Λ P K
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj M)) ≅
      tensor Λ P K'
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f').leftDerivedFunctor.obj M') :=
  Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) u' _ _ ≪≫
    tensorComparison Λ P e₁
      (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u' f).app M).symm ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
          f' v (u' ≫ f) w).app M ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) f').leftDerivedFunctor.mapIso e₂)

/-- Composing compatible restriction squares gives the restriction square for gf.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting).
Proof: reassociate u f g, substitute u f=f' v and v g=g' w, and reassociate back. -/
theorem compositeSquare {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w) :
    u' ≫ (f ≫ g) = (f' ≫ g') ≫ w := by
  sorry

/-- Restriction of the middle product Q by the compatible source/target opens.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def openMiddle {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w) :
    pullback (f' ≫ g') g' ⟶ pullback (f ≫ g) g :=
  pullback.map (f' ≫ g') g' (f ≫ g) g u' v w
    (compositeSquare f g f' g' u' v w hf hg).symm hg.symm

/-- The open middle product respects a, b and the graph section.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting).
Proof: openMiddle restricts both factors to opens, as for openPair. For a and b
compare the two projections; they agree by the compatible restriction equations.
For the graph compare its first projection, the identity, and second projection f.
The pullback universal property then proves each equality. -/
theorem openMiddleProperties {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w) :
    IsOpenImmersion (openMiddle f g f' g' u' v w hf hg) ∧
    openPair (f ≫ g) (f' ≫ g') u' w
      (compositeSquare f g f' g' u' v w hf hg) ≫ a f g =
        a f' g' ≫ openMiddle f g f' g' u' v w hf hg ∧
    openMiddle f g f' g' u' v w hf hg ≫ pullback.fst (f ≫ g) g =
      pullback.fst (f' ≫ g') g' ≫ u' ∧
    u' ≫ s f g = s f' g' ≫ openMiddle f g f' g' u' v w hf hg := by
  sorry

/-- Restriction comparison for the pullback of an object along a section or graph.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def pullbackRestriction (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y X' Y' : Scheme.{u}}
    (r : X ⟶ Y) (r' : X' ⟶ Y') (u' : X' ⟶ X) (v : Y' ⟶ Y)
    (h : u' ≫ r = r' ≫ v) (K : D Λ P Y) (K' : D Λ P Y')
    (c : (Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj K ≅ K') :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).leftDerivedFunctor.obj K) ≅
    (Etale.upperStar (ModuleCat.{u + 1} Λ) r').leftDerivedFunctor.obj K' :=
  ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u' r).app K).symm ≪≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      r' v (u' ≫ r) h).app K ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) r').leftDerivedFunctor.mapIso c

/-- Naturality under arbitrary compatible source and target open restrictions.
The first three equations concern alpha_f, alpha_g, alpha_gf, the fourth sigma,
the fifth kappa, and the last two gamma_f and gamma_g. In particular source
opens are not treated as Cartesian.
Source: blueprint proof Step 7 (blueprint: lem-pur-diagonal-section-pasting). -/
def OpenEquation (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z X' Y' Z' : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aZ : Z ⟶ Spec (.of P.field.k)) : Prop :=
  let hgeom := geometryProperties d e f g
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2
  let hgeom' := geometryProperties d e f' g'
  letI := hgeom'.1
  letI := hgeom'.2.1
  letI := hgeom'.2.2.1
  letI := hgeom'.2.2.2.1
  letI := hgeom'.2.2.2.2
  let hfg := compositeSquare f g f' g' u' v w hf hg
  let S₁ := openSection Λ P d f f' u' v hf (f ≫ g ≫ aZ)
  let S₂ := openSection Λ P e g g' v w hg (g ≫ aZ)
  let S₃ := openSection Λ P (d + e) (f ≫ g) (f' ≫ g') u' w hfg (f ≫ g ≫ aZ)
  let O₁ := openDualizing Λ P d f f' u' v hf (f ≫ g ≫ aZ)
  let O₂ := openDualizing Λ P e g g' v w hg (g ≫ aZ)
  let O₃ := openDualizing Λ P (d + e) (f ≫ g) (f' ≫ g') u' w hfg (f ≫ g ≫ aZ)
  let R := openMiddle f g f' g' u' v w hf hg
  let T := openPair (f ≫ g) (f' ≫ g') u' w hfg
  let hR := openMiddleProperties f g f' g' u' v w hf hg
  letI := hR.1
  let hT := openPairProperties (f ≫ g) (f' ≫ g') u' w hfg
  letI := hT.1
  let Oa := openDualizing Λ P d (a f g) (a f' g') T R hR.2.1
    (pullback.fst (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ)
  let Ob := openDualizing Λ P e (pullback.fst (f ≫ g) g)
    (pullback.fst (f' ≫ g') g') R u' hR.2.2.1
    (pullback.fst (f ≫ g) g ≫ f ≫ g ≫ aZ)
  let Ta := pullbackRestriction Λ P (pullback.diagonal (f ≫ g))
    (pullback.diagonal (f' ≫ g')) u' T hT.2.2.symm _ _ Oa
  let Tb := pullbackRestriction Λ P (s f g) (s f' g') u' R hR.2.2.2 _ _ Ob
  let Sg := pullbackRestriction Λ P f f' u' v hf _ _ S₂
  let U := (Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor
  let V := (Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor
  SameProEtaleMap Λ P (U.map (alpha Λ P d f (f ≫ g ≫ aZ)).hom ≫ O₁.hom)
      (S₁.hom ≫ (alpha Λ P d f' (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (V.map (alpha Λ P e g (g ≫ aZ)).hom ≫ O₂.hom)
      (S₂.hom ≫ (alpha Λ P e g' (v ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (U.map (alpha Λ P (d + e) (f ≫ g) (f ≫ g ≫ aZ)).hom ≫ O₃.hom)
      (S₃.hom ≫ (alpha Λ P (d + e) (f' ≫ g') (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (U.map (sigma Λ P d f g (f ≫ g ≫ aZ)).hom ≫ O₃.hom)
      ((tensorRestriction Λ P f f' u' v hf _ _ _ _ O₁ O₂).hom ≫
        (sigma Λ P d f' g' (u' ≫ f ≫ g ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (U.map (kappa Λ P d e f g aZ).hom ≫ S₃.hom)
      ((tensorRestriction Λ P f f' u' v hf _ _ _ _ S₁ S₂).hom ≫
        (kappa Λ P d e f' g' (w ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (U.map (gammaF Λ P d f g aZ).hom ≫ Ta.hom)
      (S₁.hom ≫ (gammaF Λ P d f' g' (w ≫ aZ)).hom) ∧
  SameProEtaleMap Λ P (U.map (gammaG Λ P e f g aZ).hom ≫ Tb.hom)
      (Sg.hom ≫ (gammaG Λ P e f' g' (w ≫ aZ)).hom)



/-- All clauses of orientation-free diagonal section pasting, including restriction
and the conditional coordinate comparison on each compatible affine open chart.
The repeated finiteness, smoothness and Noetherian instances for restrictions are
consequences of the compatible open squares, recorded explicitly to bind every object.
Source: blueprint lem-pur-diagonal-section-pasting
(blueprint: lem-pur-diagonal-section-pasting). -/
def ModelStatement (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := LocallyOfFiniteType.isLocallyNoetherian aZ
  letI := QuasiCompact.compactSpace_of_compactSpace aZ
  letI : IsNoetherian Z := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian g
  letI := QuasiCompact.compactSpace_of_compactSpace g
  letI : IsNoetherian Y := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian f
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := ⟨⟩
  Equation Λ P d e f g aZ ∧
    ∀ {X' Y' Z' : Scheme.{u}} (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
      (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
      [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
      [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w),
      OpenEquation Λ P d e f g f' g' u' v w hf hg aZ ∧
      (∀ [IsAffine X'] [IsAffine Y'] [IsAffine Z']
        (x : X' ⟶ A d Y') (y : Y' ⟶ A e Z') [Etale x] [Etale y]
        (hx : x ≫ pr d Y' = f') (hy : y ≫ pr e Z' = g'),
        ChartEquation Λ P d e f' g' (w ≫ aZ) x y hx hy)

/-- The statement in the prescribed coefficient setting. Internal formulas use a
coefficient ring variable; this definition specializes their proposition to the actual
coefficient quotient and the source-implied invertible exponent on the fixed field.
Source: blueprint all clauses of diagonal section pasting
(blueprint: lem-pur-diagonal-section-pasting). -/
def Statement (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  ModelStatement P.Coefficient P d e f g aZ

/-- Pasting of the orientation-free diagonal section comparison, with its open
restriction and precise ordered difference-coordinate clauses.
Source: blueprint main-20261015, thm-pur-composition-coherence proof Step 1
(blueprint: lem-pur-diagonal-section-pasting).

The following is the complete twelve-step proof recorded on the DAG node. The
formal definitions above use exactly its mates, coordinate differences and
pullback comparisons, in the canonical finite pro-etale presentation.

Proof step 1. Write $r:Q\to Y$ and $l:W\to X$ for the second projections. The universal property
[def-pc-fibre-product] gives the commutative diagram with rows $W\xrightarrow aQ\xrightarrow bX$
and $X\xrightarrow fY\xrightarrow gZ$, and vertical arrows $l,r,gf$. Its two squares are
Cartesian: $W=Q\times_YX$ and $Q=X\times_ZY$. Its outer rectangle is the base-change square for
$gf$, with $ba=p_{gf}$. Evaluation on pairs gives $at=s$, $lt=1_X$, and $rs=f$. Base-change and
composition permanence [lem-sbc-smooth-relative-dimension-permanence,
lem-pod-separated-finite-type-base-change] give the smooth separated finite-type maps $a,b,ba$ of
dimensions $d,e,d+e$. These are the actual two squares used below; no square involving a
composition isomorphism is regarded as a square of schemes.

Proof step 2. Use $B_{h,v,N}:Lu^*Rh^!N\to Rh'^!Lv^*N$ for the transpose of
$Lv^*\varepsilon_{h,N}\circ\operatorname{Ex}_!^{-1}$ for a Cartesian square $(h,h',v,u)$; its unit
specialization is exactly $\beta_{h,v}$ of [def-pur-co-smoothness]. The horizontal law of
[fix-lem-exchanges](2), inverted and followed by the pulled-back counit, gives transitivity of $B$
for successive base changes. The vertical law in the same clause, with compact-support composition
[thm-sf-comp-composition], gives
$$c_{b,a,L(gf)^*N}\circ B_{gf,gf,N}=Ra^!(B_{g,gf,N})\circ
B_{f,r,Rg^!N}\circ Ll^*c_{g,f,N}.$$ This follows by taking the mates of the two sides of that
vertical exchange equation, using [lem-weil-pbc-mate-pasting](2) and the composite counit
[def-weil-pbc-composite-adjunction]; conjugation reverses composition as in
[def-weil-pbc-adjunction-conjugate]. Thus the geometric exchange equations, as well as the formal
mate law, are used.

Proof step 3. The tensor and base-change clauses (1),(3) of [thm-pur-cohomological-smoothness]
make every displayed $\theta$ and smooth $B$ invertible, and identify
$B_{f,r,N}\,Ll^*\theta_{f,N}$ with $\theta_{a,Lr^*N}(1\otimes\beta_{f,r})$. Set
$$A=\beta_{f,r}:Ll^*\omega_f\to\omega_a,\quad B=\beta_{g,gf}:Lr^*\omega_g\to\omega_b,\quad
D=\beta_{gf,gf}:Ll^*\omega_{gf}\to\omega_{ba}.$$
Apply the vertical identity of Step 2 at
$N=\Lambda$, substitute this tensor compatibility at $N=\omega_g$, and invert $c_{b,a}$.
Naturality of $\theta_a$ in $B$ gives exactly
$$D\,Ll^*\sigma_{f,g}=\sigma_{a,b}(A\otimes
La^*B).\tag{*}$$
All pullback composition in this formula is supplied by
[lem-weil-pbc-proetale-derived-pullback-composition];
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies its tensor comparison. Their
reassociations agree termwise on K-flat flat-term models: both orders send a pure tensor to the
same pulled-back tensor, and both composite pullbacks are the termwise canonical module
comparison. This also fixes all suppressed associators.

Proof step 4. Let $i:W_f\to W$ send $(x,x')$ with $f(x)=f(x')$ to the same pair. Then
$(W_f\xrightarrow iW, X\xrightarrow sQ)$ is the base-change square of $a$, and $i\Delta_f=t$. Let
$j:Q\to W_g$ send $(x,y)$ to $(f(x),y)$; then $(Q\xrightarrow jW_g,X\xrightarrow fY)$ is the
base-change square of $p_g$, and $js=\Delta_gf$. Put $F=\beta_{a,s}:Li^*\omega_a\to\omega_{p_f}$
and $G=\beta_{p_g,f}:Lj^*\omega_{p_g}\to\omega_b$. The comparisons in the statement are
$$\gamma_f=L\Delta_f^*F^{-1}:C_f\to Lt^*\omega_a,\qquad\gamma_g=Ls^*G:Lf^*C_g\to Ls^*\omega_b.$$
Horizontal transitivity from Step 2, applied respectively to the squares for $(f,r)$ then $(a,s)$
and for $(g,g)$ then $(p_g,f)$, gives
$$\alpha_f=(Lt^*A)^{-1}\gamma_f,\quad
Lf^*\alpha_g=(Ls^*B)^{-1}\gamma_g,\quad\alpha_{gf}=(Lt^*D)^{-1}.$$
The last formula is precisely
[lem-pur-diagonal-base-change] for $gf$ since $lt=1$. The same lemma identifies the first two with
the specified $\alpha$, rather than unspecified isomorphisms. Use
[lem-weil-pbc-proetale-derived-pullback-composition] throughout to identify the composed
pullbacks.

Proof step 5. The invertibility in [thm-pur-cohomological-smoothness] and adjunction conjugation
[def-weil-pbc-adjunction-conjugate] of [thm-sf-comp-composition] show that each $\sigma$ is an
isomorphism. The tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback],
$at=s$, and derived pullback composition [lem-weil-pbc-proetale-derived-pullback-composition] make
$\kappa$ exactly $Lt^*\sigma_{a,b}\circ(\gamma_f\otimes\gamma_g)$. Pull (*) back along $t$,
precompose with $\gamma_f\otimes\gamma_g$, and multiply by $(Lt^*D)^{-1}$. The three substitutions
of Step 4 give
$$\alpha_{gf}\kappa=\sigma_{f,g}(\alpha_f\otimes Lf^*\alpha_g).$$
This is a
calculation with the specified maps, requiring both exchange pasting and base-change compatibility
of the tensor map.

Proof step 6. We will also use the cocycle equation
$$\sigma_{vu,w}(\sigma_{u,v}\otimes1)=\sigma_{u,wv}(1\otimes Lu^*\sigma_{v,w}).\tag{**}$$
This is
the tensor-formula composition clause (4) of [thm-pur-cohomological-smoothness] evaluated at
$\omega_w$, followed by the inverse exceptional composition comparison: substitute
$\sigma_{u,v}=c_{v,u}^{-1}\theta_{u,\omega_v}\mathrm{sym}$ on both sides. Naturality moves
$c_{w,v}^{-1}$ through $\theta_u$; clause (4) replaces $\theta_u\circ Lu^*\theta_v$ with the
composite tensor map; the two remaining $c$ composites agree because [thm-sf-comp-composition] is
associative and conjugation [def-weil-pbc-adjunction-conjugate] reverses the same associative
equation. Thus (**) uses the specified $\theta$, not the unspecified isomorphism of the
co-smooth-composition lemma. For an etale $u$,
[lem-pur-finite-etale-dualizing-normalization](1),(3) say $\sigma_{u,v}^{-1}=E_{u,v}$ after
removing $\omega_u$ with $\eta_u$. In particular (**) gives
$$E_{u,wv}\sigma_{vu,w}=Lu^*\sigma_{v,w}(E_{u,v}\otimes1).\tag{***}$$

Proof step 7. Target-open restrictions are Cartesian base changes, so Steps 2-3 and
[fix-lem-exchanges](1),(2) identify every restricted $\beta$ and $\sigma$ with the corresponding
map on the target open. A further source-open immersion $u$ uses the normalized etale comparison
$E_{u,h}$ of [lem-pur-finite-etale-dualizing-normalization], rather than a falsely asserted
Cartesian square. Its compatibility with $\sigma$ is (***); its compatibility with the Cartesian
base-change maps is Step 2 with the etale normalization of that lemma. Restricting the diagonal
pair amounts to restricting both factors, and its diagonal factors through that restriction. Hence
applying the derived pullback comparison [lem-weil-pbc-proetale-derived-pullback-composition] and
the tensor comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the formulas for
$\gamma_f,\gamma_g,\kappa$ proves precisely their asserted compatibility with arbitrary compatible
source and target open restrictions.

Proof step 8. For the base $B$ of the statement, [def-sbc-affine-space] and
[sbc-lem-affine-space-smooth] give the smooth tower $\mathbf A_B^{d+e}\xrightarrow q\mathbf
A_B^e\xrightarrow{P_e}B$. The square with top $\mathbf A_B^{d+e}\to\mathbf A_B^d$ and bottom $P_e$
is Cartesian and $q$ is the pullback of $P_d$. Its $\beta$ gives $Lz_{d+e}^*\omega_q\cong
Lz_d^*\omega_{P_d}=D_d$, while $qz_{d+e}=z_e$ gives $Lz_{d+e}^*Lq^*\omega_{P_e}=D_e$ by
[lem-weil-pbc-proetale-derived-pullback-composition]. Thus the tensor comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and $Lz_{d+e}^*\sigma_{q,P_e}$ give the stated
$\nu_{d,e}$. Its definition uses no trivialization of any dualizing object.

Proof step 9. By Step 7 work on the stated charts and replace $(X,Y,Z)$ by $(U,V,T)$, putting
$B=U$. Write $x=(x_1,\ldots,x_d)$ for the chart coordinates of $U\to\mathbf A^d_V$ and
$y=(y_1,\ldots,y_e)$ for those of $V\to\mathbf A^e_T$. With $Q=U\times_TV$ and $W=U\times_TU$,
define
$$G:Q\to\mathbf A_B^e,\quad(u,v)\mapsto y(v)-y(fu).$$
Put $R=Q\times_{\mathbf A_B^e}\mathbf
A_B^{d+e}=\mathbf A_Q^d$ with projections $q_Q:R\to Q$, $J:R\to\mathbf A_B^{d+e}$. Define
$$H:W\to
R,\quad(u,u')\mapsto((u,fu'),x(u')-x(u)).$$
Then $a=q_QH$, $b=P_eG$, $qJ=Gq_Q$, and $F=JH$ has the
ordered difference coordinates $(x(u')-x(u),y(fu')-y(fu))$. These formulas follow from
[def-pc-fibre-product, def-sbc-affine-space]. $G$ is the base change of the chart of $g$, followed
by translation by $-y(fu)$; $H$ is the base change of the chart of $f$, followed by translation by
$-x(u)$. They are etale by [lem-weil-pbc-etale-ring-base-change]; translation is an isomorphism
with inverse addition of the same coordinates. Likewise $J$ is etale as a base change of $G$. All
these schemes are affine, so that cited affine ring-base-change statement applies, and all maps
are separated finite type. Crucially the square $(W\xrightarrow F\mathbf A_B^{d+e},Q\xrightarrow
G\mathbf A_B^e)$ need not be Cartesian; the square defining $R$ is Cartesian. The sections satisfy
$Gs=z_e$ and $Ft=z_{d+e}$.

Proof step 10. Write $E$ for the normalized comparisons of
[lem-pur-finite-etale-dualizing-normalization]. For the Cartesian square defining $R$, its clause
(3) gives
$$E_{J,q}\sigma_{q_Q,G}=\beta_{q,G}^{-1},\tag{a}$$
after identifying $\omega_G$ with the
unit. Apply (**) to $(q_Q,G,P_e)$ and (***) to $(J,q,P_e)$. Substitute (a) and
$\sigma_{G,P_e}^{-1}=E_{G,P_e}$. Cancellation of the invertible $\sigma_{q_Q,G}$ gives the typed
identity
$$E_{J,P_eq}\sigma_{q_Q,b}=LJ^*\sigma_{q,P_e}\bigl(\beta_{q,G}^{-1}\otimes
Lq_Q^*E_{G,P_e}\bigr).\tag{b}$$
Both sides have domain $\omega_{q_Q}\otimes Lq_Q^*\omega_b$ and
target $LJ^*\omega_{P_eq}$. Now apply (***) with $(H,q_Q,b)$, then pull (b) along $H$.
Associativity of $c$ and the etale-composition normalization in that lemma identify
$E_{F,P_eq}=LH^*E_{J,P_eq}\circ E_{H,bq_Q}$. Hence
$$E_{F,P_eq}\sigma_{a,b}=LF^*\sigma_{q,P_e}\bigl((LH^*\beta_{q,G}^{-1})E_{H,q_Q}\otimes
La^*E_{G,P_e}\bigr).\tag{c}$$
This proves the comparison of the two towers using the Cartesian
square and normalized etale factors separately.

Proof step 11. Check the input identifications in (c) against those defining $\kappa$. Pull the
Cartesian square $(p_f,a,s,i)$ of Step 4 back through $H$. The result is the Cartesian square of
etale maps $H:W\to\mathbf A_Q^d$ and $H_f:W_f\to\mathbf A_B^d$, with base $s:B\to Q$; explicitly
$H_f(u,u')=(u,x(u')-x(u))$. Its zero section is the image of $\Delta_f$. The base-change
compatibility of $\rho$ and $\eta$ in [lem-pur-finite-etale-dualizing-normalization], and vertical
exchange pasting [fix-lem-exchanges](2) for $a=q_QH$, identify $L\Delta_f^*E_{H_f,P_d}$ with
$Lt^*E_{H,q_Q}\gamma_f$, followed by the base-change comparison for $q_Q$ along $s$. Horizontal
exchange pasting identifies that comparison with $Lt^*LH^*\beta_{q,G}^{-1}$ followed by the $D_d$
comparison in Step 8: both are the inverse base-change comparison for $P_d$ along the composite
$B\xrightarrow sQ\xrightarrow G\mathbf A_B^e$, with $Gs=z_e$. Thus the first input of $Lt^*$(c) is
the actual difference-coordinate identification $C_f\to D_d$, using the route through $\gamma_f$,
not an arbitrary isomorphism. For the second input define $G_g:W_g=V\times_TV\to\mathbf A_V^e$ by
$(v,v')\mapsto(v,y(v')-y(v))$. The square with top $j:Q\to W_g$ and bottom $f:B\to V$ is
Cartesian, as is the square of $G_g$ and $G:Q\to\mathbf A_B^e$ over the affine-space pullback
$\mathbf A_B^e\to\mathbf A_V^e$. Vertical exchange pasting for $p_g=P_e^VG_g$, followed by etale
beta normalization, identifies the pullback of the section comparison $L\Delta_g^*E_{G_g,P_e^V}$
with $Ls^*E_{G,P_e}\gamma_g:Lf^*C_g\to D_e$. All composed pullbacks here use
[lem-weil-pbc-proetale-derived-pullback-composition].

Proof step 12. For the output, $Ft=z_{d+e}$ identifies $Lt^*E_{F,P_eq}:C_{gf}\to D_{d+e}$ with the
canonical total difference-coordinate comparison; here $E_F$ is obtained by composing the etale
comparisons for $H,J$, and [lem-pur-finite-etale-dualizing-normalization](2) makes this the
canonical comparison for their composite. Pull (c) back along $t$ and insert
$\gamma_f\otimes\gamma_g$. Step 11 identifies its two inputs with $D_d\otimes D_e$ exactly as in
Step 8; its middle arrow is $Lz_{d+e}^*\sigma_{q,P_e}$. Its left side is the coordinate image of
$\kappa$. This is precisely $\kappa|_U=\nu_{d,e}$. The tensor and pullback comparisons
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-proetale-derived-pullback-composition] give all the displayed source/target
identifications. The statement is conditional on compatible charts; their local availability
follows by applying [sbc-thm-etale-local-normal-form] first to $g$ and then to $f$. Empty charts
cause no assertion; when either block has length zero the translation, zero section and cocycle
calculations have the same formulas with the empty block, including the normalized etale unit. No
orientation or Tate-twist comparison has entered.
-/
theorem diagonalSectionPasting (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    Statement P d e f g aZ := by
  sorry



end WeilConjectures.PurityFiniteSetting.DiagonalPasting
