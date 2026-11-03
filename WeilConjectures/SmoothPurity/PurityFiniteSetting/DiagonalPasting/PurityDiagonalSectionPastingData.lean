/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat
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
The shared constructions are attached to def-pur-diagonal-section-pasting-data.
(blueprint: def-pur-diagonal-section-pasting-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

section GenericUnit

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The finite coefficient exponent is invertible on every scheme over the fixed field.
Source: blueprint def-pur-conventions, the finite coefficient paragraph
(blueprint: def-pur-conventions).
Proof: ell to the positive level annihilates the coefficient quotient, since the
valuation of ell in O_E is positive. The same integer is nonzero in k, hence a unit;
its image along the structure morphism is a unit in global sections. -/
theorem comparedExponent (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of P.field.k)) : HasInvertibleExponent P.Coefficient T := by
  exact P.finiteComparedInvertibleExponent aT

/-- Evaluate the exceptional compositor at the coefficient unit before specializing
its coefficient category. This preserves the upstream generic derived-unit term.
Source: blueprint sigma, exceptional compositor at the unit
(blueprint: lem-pur-diagonal-section-pasting). -/
def exceptionalUnit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (c : Etale.rightDerivedUpperShriek Λ (f ≫ g) ≅
      Etale.rightDerivedUpperShriek Λ g ⋙ Etale.rightDerivedUpperShriek Λ f) :
    Etale.dualizingComplex Λ (f ≫ g) ≅
      (Etale.rightDerivedUpperShriek Λ f).obj (Etale.dualizingComplex Λ g) :=
  c.app (𝟙_ _)

/-- Evaluate normalized etale localization at the same generic coefficient unit.
Source: blueprint E_(v,h) at the unit
(blueprint: lem-pur-diagonal-section-pasting). -/
def restrictionUnit {U X B : Scheme.{u}} (v' : U ⟶ X) (h : X ⟶ B)
    [HasCompactification h] [HasCompactification (v' ≫ h)]
    (c : Etale.rightDerivedUpperShriek Λ h ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) v').mapDerivedCategory ≅
      Etale.rightDerivedUpperShriek Λ (v' ≫ h)) :
    Etale.dualizingComplex Λ (v' ≫ h) ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) v').mapDerivedCategory.obj
        (Etale.dualizingComplex Λ h) :=
  (c.app (𝟙_ _)).symm

/-- Package the specified finite-coefficient tensor mate before specializing the ring.
Source: blueprint sigma, theta at omega_v (blueprint: lem-pur-diagonal-section-pasting). -/
def finiteThetaIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso (Etale.dualizingComplexTensorMap Λ f K)) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex Λ f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K) ≅
          (Etale.rightDerivedUpperShriek Λ f).obj K :=
  @asIso _ _ _ _ (Etale.dualizingComplexTensorMap Λ f K) h

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
  have := HasInvertibleExponent.of_hom (Λ := Λ) aX
  exact Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ f (d := d) K

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
  have := HasInvertibleExponent.of_hom (Λ := Λ) aX
  have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    Λ f d sq
  exact (Etale.isIso_dualizingComplexBaseChangeMap_iff Λ sq).2 inferInstance

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
    Etale.dualizingComplex Λ (f ≫ g) ≅
      (Etale.rightDerivedUpperShriek Λ f).obj
        (Etale.dualizingComplex Λ g) :=
  exceptionalUnit Λ f g (finiteExceptionalComposition Λ f g)

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
  thetaIso Λ P d f (Etale.dualizingComplex Λ g) aX ≪≫
    (compositionUnit Λ P f g).symm

/-- The canonical self-product base-change map and pullback along its diagonal.
Source: blueprint lem-pur-diagonal-section-pasting, alpha_h
(blueprint: lem-pur-diagonal-section-pasting). -/
def alpha (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] (aX : X ⟶ Spec (.of P.field.k)) :
    diagonalSection Λ P f ≅ Etale.dualizingComplex Λ f :=
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
  have ha : a f g ≫ pullback.fst (f ≫ g) g = pullback.fst (f ≫ g) (f ≫ g) := by
    simp [a]
  refine ⟨?_, ?_, ha, ?_, ?_, ?_⟩
  · apply IsPullback.mk'
    · apply pullback.hom_ext <;> simp [pullback.map, i, a, s, pullback.condition]
    · intro T x y h _
      apply pullback.hom_ext
      · simpa [pullback.map, i] using h =≫ pullback.fst (f ≫ g) (f ≫ g)
      · simpa [pullback.map, i] using h =≫ pullback.snd (f ≫ g) (f ≫ g)
    · intro T x y h
      have h₁ : x ≫ pullback.fst (f ≫ g) (f ≫ g) = y := by
        simpa [a, s] using h =≫ pullback.fst (f ≫ g) g
      have h₂ : x ≫ pullback.snd (f ≫ g) (f ≫ g) ≫ f = y ≫ f := by
        simpa [a, s] using h =≫ pullback.snd (f ≫ g) g
      refine ⟨pullback.lift (f := f) (g := f) y
        (x ≫ pullback.snd (f ≫ g) (f ≫ g)) (by simpa using h₂.symm), ?_, ?_⟩
      · apply pullback.hom_ext
        · simpa only [Category.assoc, i, pullback.map, pullback.lift_fst,
            Category.comp_id] using h₁.symm
        · simp only [Category.assoc, i, pullback.map, pullback.lift_snd,
            Category.comp_id]
      · exact pullback.lift_fst _ _ _
  · apply IsPullback.mk'
    · simp [pullback.map, j]
    · intro T x y h₁ h₂
      apply pullback.hom_ext
      · exact h₂
      · simpa [pullback.map, j] using h₁ =≫ pullback.snd g g
    · intro T x y h
      have h₁ : x ≫ pullback.fst g g = y ≫ f := h
      refine ⟨pullback.lift y (x ≫ pullback.snd g g) ?_, ?_, pullback.lift_fst _ _ _⟩
      · calc
          y ≫ (f ≫ g) = (y ≫ f) ≫ g := (Category.assoc _ _ _).symm
          _ = (x ≫ pullback.fst g g) ≫ g :=
            congrArg (fun k ↦ k ≫ g) h₁.symm
          _ = (x ≫ pullback.snd g g) ≫ g := by
            simp only [Category.assoc, pullback.condition]
      · apply pullback.hom_ext <;> simp [pullback.map, j, h₁]
  · apply pullback.hom_ext <;> simp [a, s]
  · apply pullback.hom_ext <;> simp [pullback.map, i]
  · apply pullback.hom_ext <;> simp [s, j]

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
  have hp : IsPullback (pullback.snd (f ≫ g) (f ≫ g)) (a f g) f
      (pullback.snd (f ≫ g) g) := by
    apply IsPullback.of_bot ?_ (by simp [a]) (IsPullback.of_hasPullback (f ≫ g) g).flip
    simpa [a] using (IsPullback.of_hasPullback (f ≫ g) (f ≫ g)).flip
  have : SmoothOfRelativeDimension d (a f g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback hp inferInstance
  exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @IsSeparated) hp inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp inferInstance,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance, inferInstance⟩

/-- Equality transport of the dualizing object, with no choice of comparison.
Source: blueprint canonical Cartesian product identifications
(blueprint: lem-pur-diagonal-section-pasting). -/
def dualizingCongr (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent Λ (Spec (.of P.field.k))] {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g] (h : f = g) :
    Etale.dualizingComplex Λ f ≅
      Etale.dualizingComplex Λ g :=
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
      (Etale.dualizingComplex Λ f) ≅
        Etale.dualizingComplex Λ f' :=
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
          (Etale.dualizingComplex Λ (a f g)) :=
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
      (Etale.dualizingComplex Λ
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
      (Etale.dualizingComplex Λ (a f g))
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a f g)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ
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
    Etale.dualizingComplex Λ (v ≫ h) ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ h) :=
  let E := Classical.choose
    (Etale.existsUnique_etaleAmbientAdjointLocalityIso Λ v h
      (HasCompactification.compactification h)
      (HasCompactification.compactification (v ≫ h))
      (Etale.rightDerivedUpperShriek Λ h)
      (Etale.rightDerivedUpperShriek Λ (v ≫ h))
      (Etale.rightDerivedUpperShriekAdjunction Λ h)
      (Etale.rightDerivedUpperShriekAdjunction Λ (v ≫ h))).exists
  restrictionUnit Λ v h E ≪≫
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

attribute [instance] noetherianPullback

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
  have hd : SmoothOfRelativeDimension d (pr d B) := by
    simpa only [Nat.card_ulift, Nat.card_fin] using
      (inferInstance : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin d))) (pr d B))
  have hp : IsPullback (first d e B) (q d e B) (pr d B) (pr e B) := by
    apply IsPullback.mk'
    · simp [first, q]
    · intro T x y h₁ h₂
      apply AffineSpace.hom_ext
      · simpa [first, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
              AffineSpace.reindex_appTop_coord] using h₁ =≫ pr d B
      · rintro ⟨j⟩
        refine Fin.addCases ?_ ?_ j
        · intro k
          simpa only [first, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
              AffineSpace.reindex_appTop_coord] using
            congrArg (fun z ↦ z.appTop (AffineSpace.coord B (ULift.up k))) h₁
        · intro k
          simpa only [q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
              AffineSpace.reindex_appTop_coord] using
            congrArg (fun z ↦ z.appTop (AffineSpace.coord B (ULift.up k))) h₂
    · intro T x y h
      let z : T ⟶ A (d + e) B := AffineSpace.homOfVector (x ≫ pr d B)
        (fun j ↦ Fin.addCases (fun k ↦ x.appTop (AffineSpace.coord B (ULift.up k)))
          (fun k ↦ y.appTop (AffineSpace.coord B (ULift.up k))) j.down)
      refine ⟨z, ?_, ?_⟩
      · apply AffineSpace.hom_ext
        · simp [z, first]
        · rintro ⟨k⟩
          simp only [first, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            AffineSpace.reindex_appTop_coord, z, AffineSpace.homOfVector_appTop_coord,
            Fin.addCases_left]
      · apply AffineSpace.hom_ext
        · simpa [z, q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
              AffineSpace.reindex_appTop_coord] using h
        · rintro ⟨k⟩
          simp only [q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            AffineSpace.reindex_appTop_coord, z, AffineSpace.homOfVector_appTop_coord,
            Fin.addCases_right]
  have := hd
  have : SmoothOfRelativeDimension d (q d e B) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback hp inferInstance
  refine ⟨hp, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_, hd⟩
  · simp [zero, first]
  · simp [zero, q]
  · simp [q]
  · exact MorphismProperty.of_isPullback (P := @IsSeparated) hp inferInstance
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp inferInstance
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance

/-- The projection of r-space has pure relative dimension r.
Source: blueprint sbc-lem-affine-space-smooth
(blueprint: lem-pur-diagonal-section-pasting).
Proof: the published affine-space smoothness instance has dimension the cardinality
of the coordinate set ULift (Fin r), which is r. -/
theorem affineDimension (r : ℕ) (B : Scheme.{u}) :
    SmoothOfRelativeDimension r (pr r B) := by
  simpa only [Nat.card_ulift, Nat.card_fin] using
    (inferInstance : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin r))) (pr r B))

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
  have := LocallyOfFiniteType.isLocallyNoetherian (pr r B)
  have := QuasiCompact.compactSpace_of_compactSpace (pr r B)
  exact ⟨⟩

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
      (Etale.dualizingComplex Λ (pr e B))
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
  have hfst : openFactor h h' u' v w ≫ pullback.fst h v = u' := by
    simp [openFactor]
  refine ⟨?_, hfst, by simp [openFactor]⟩
  have : IsOpenImmersion (openFactor h h' u' v w ≫ pullback.fst h v) :=
    hfst.symm ▸ inferInstance
  exact IsOpenImmersion.of_comp _ (pullback.fst h v)

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
      (Etale.dualizingComplex Λ h) ≅
      Etale.dualizingComplex Λ h' :=
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
  refine ⟨?_, ?_, ?_⟩
  · exact Scheme.pullback_map_isOpenImmersion h' h' h h u' u' v w.symm w.symm
  · simp [pullback.map, openPair]
  · apply pullback.hom_ext <;> simp [pullback.map, openPair]

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

private lemma appTop_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : Γ(Z, ⊤)) : f.appTop (g.appTop r) = (f ≫ g).appTop r := rfl

private lemma comp_translation_coord {n : Type u} {X B : Scheme.{u}}
    (f : X ⟶ AffineSpace n B) (v : n → Γ(B, ⊤)) (i : n) :
    (f ≫ AffineSpace.translation v).appTop (AffineSpace.coord B i) =
      f.appTop (AffineSpace.coord B i) + (f ≫ (AffineSpace n B ↘ B)).appTop (v i) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.translation_appTop_coord, map_add]
  rfl

private lemma translation_isIso {n : Type u} {B : Scheme.{u}} (v : n → Γ(B, ⊤)) :
    IsIso (AffineSpace.translation v) := by
  let E : AffineSpace n B ≅ AffineSpace n B :=
    { hom := AffineSpace.translation v
      inv := AffineSpace.translation (-v)
      hom_inv_id := by rw [← AffineSpace.translation_add, add_neg_cancel,
        AffineSpace.translation_zero]
      inv_hom_id := by rw [← AffineSpace.translation_add, neg_add_cancel,
        AffineSpace.translation_zero] }
  exact E.isIso_hom

private lemma chart_pullback {n : Type u} {L B X S : Scheme.{u}}
    (p : L ⟶ B) (r : L ⟶ X) (b : B ⟶ S) (f : X ⟶ S)
    (hp : IsPullback p r b f) (c : X ⟶ AffineSpace n S)
    (hc : c ≫ (AffineSpace n S ↘ S) = f) :
    IsPullback (AffineSpace.homOfVector p
      (fun i ↦ (r ≫ c).appTop (AffineSpace.coord S i))) r
      (AffineSpace.map n b) c := by
  let h := AffineSpace.homOfVector p
    (fun i ↦ (r ≫ c).appTop (AffineSpace.coord S i))
  have hcomm : h ≫ AffineSpace.map n b = r ≫ c := by
    apply AffineSpace.hom_ext
    · dsimp only [h]
      rw [Category.assoc, AffineSpace.map_over, AffineSpace.homOfVector_over_assoc,
        Category.assoc, hc]
      exact hp.w
    · intro i
      simp only [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord]
  have hout : IsPullback (h ≫ (AffineSpace n B ↘ B)) r b
      (c ≫ (AffineSpace n S ↘ S)) := by
    simpa only [h, AffineSpace.homOfVector_over, hc] using hp
  exact hout.of_right hcomm (AffineSpace.isPullback_map (n := n) b).flip

private lemma differenceFirst_diagonal {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (c : X ⟶ A d Y) :
    pullback.diagonal f ≫ differenceFirst d f c = zero d X := by
  apply AffineSpace.hom_ext
  · simp [differenceFirst]
  · intro i
    simp only [differenceFirst, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, map_sub]
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Category.assoc, pullback.diagonal_snd, pullback.diagonal_fst, Category.id_comp,
      sub_self, AffineSpace.zeroSection_appTop_coord]

private lemma differenceFirst_etale {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (c : X ⟶ A d Y) [Etale c] (hc : c ≫ (A d Y ↘ Y) = f) :
    Etale (differenceFirst d f c) := by
  let raw := AffineSpace.homOfVector (pullback.fst f f)
    (fun i ↦ (pullback.snd f f ≫ c).appTop (AffineSpace.coord Y i))
  have hp : IsPullback raw (pullback.snd f f) (AffineSpace.map (ULift.{u} (Fin d)) f) c :=
    chart_pullback _ _ _ _ (IsPullback.of_hasPullback f f) c hc
  have : Etale raw := MorphismProperty.of_isPullback hp.flip inferInstance
  let v : ULift.{u} (Fin d) → Γ(X, ⊤) := fun i ↦ -c.appTop (AffineSpace.coord Y i)
  have : IsIso (AffineSpace.translation v) := translation_isIso v
  have heq : differenceFirst d f c = raw ≫ AffineSpace.translation v := by
    apply AffineSpace.hom_ext
    · simp [raw, differenceFirst]
    · intro i
      rw [comp_translation_coord]
      simp only [differenceFirst, raw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, v, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply]
  rw [heq]
  infer_instance

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
  have hf : LocallyOfFiniteType f := hx ▸ inferInstance
  have hg : LocallyOfFiniteType g := hy ▸ inferInstance
  have ha₁ : a f g ≫ pullback.fst (f ≫ g) g =
      pullback.fst (f ≫ g) (f ≫ g) := by simp [a]
  have ha₂ : a f g ≫ pullback.snd (f ≫ g) g =
      pullback.snd (f ≫ g) (f ≫ g) ≫ f := by simp [a]
  let Graw := AffineSpace.homOfVector (pullback.fst (f ≫ g) g)
    (fun k : ULift.{u} (Fin e) ↦
      (pullback.snd (f ≫ g) g ≫ y).appTop (AffineSpace.coord Z k))
  let Hraw := AffineSpace.homOfVector (a f g)
    (fun k : ULift.{u} (Fin d) ↦
      (pullback.snd (f ≫ g) (f ≫ g) ≫ x).appTop (AffineSpace.coord Y k))
  let H := AffineSpace.homOfVector (a f g)
    (fun k : ULift.{u} (Fin d) ↦
      (pullback.snd (f ≫ g) (f ≫ g) ≫ x).appTop (AffineSpace.coord Y k) -
      (pullback.fst (f ≫ g) (f ≫ g) ≫ x).appTop (AffineSpace.coord Y k))
  let J : A d (pullback (f ≫ g) g) ⟶ A (d + e) X :=
    AffineSpace.homOfVector (pr d _ ≫ pullback.fst (f ≫ g) g)
      (fun k ↦ Fin.addCases
        (fun l ↦ AffineSpace.coord (pullback (f ≫ g) g) (ULift.up l))
        (fun l ↦ (pr d _ ≫ differenceSecond e f g y).appTop
          (AffineSpace.coord X (ULift.up l))) k.down)
  have hpG : IsPullback Graw (pullback.snd (f ≫ g) g)
      (AffineSpace.map (ULift.{u} (Fin e)) (f ≫ g)) y :=
    chart_pullback _ _ _ _ (IsPullback.of_hasPullback (f ≫ g) g) y hy
  have hpA : IsPullback (a f g) (pullback.snd (f ≫ g) (f ≫ g))
      (pullback.snd (f ≫ g) g) f := by
    have hout : IsPullback (a f g ≫ pullback.fst (f ≫ g) g)
        (pullback.snd (f ≫ g) (f ≫ g)) (f ≫ g) (f ≫ g) := by
      simpa only [ha₁] using IsPullback.of_hasPullback (f ≫ g) (f ≫ g)
    exact hout.of_right ha₂ (IsPullback.of_hasPullback (f ≫ g) g)
  have hpH : IsPullback Hraw (pullback.snd (f ≫ g) (f ≫ g))
      (AffineSpace.map (ULift.{u} (Fin d)) (pullback.snd (f ≫ g) g)) x :=
    chart_pullback _ _ _ _ hpA x hx
  have htG : differenceSecond e f g y = Graw ≫ AffineSpace.translation
      (fun k ↦ -((f ≫ y).appTop (AffineSpace.coord Z k))) := by
    apply AffineSpace.hom_ext
    · simp [differenceSecond, Graw]
    · intro k
      rw [comp_translation_coord]
      simp only [differenceSecond, Graw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply, Category.assoc]
  have htH : H = Hraw ≫ AffineSpace.translation
      (fun k ↦ -((pullback.fst (f ≫ g) g ≫ x).appTop (AffineSpace.coord Y k))) := by
    apply AffineSpace.hom_ext
    · simp [H, Hraw]
    · intro k
      rw [comp_translation_coord]
      simp only [H, Hraw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply, ← Category.assoc, ha₁]
  have hJ : J ≫ q d e X = pr d _ ≫ differenceSecond e f g y := by
    apply AffineSpace.hom_ext
    · simp [J, q, differenceSecond]
    · rintro ⟨k⟩
      simp only [J, q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_right]
  have hJfirst : J ≫ first d e X =
      AffineSpace.map (ULift.{u} (Fin d)) (pullback.fst (f ≫ g) g) := by
    apply AffineSpace.hom_ext
    · simp [J, first]
    · rintro ⟨k⟩
      simp only [J, first, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.reindex_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        Fin.addCases_left, AffineSpace.map_appTop_coord]
  have hpJ : IsPullback J (pr d _) (q d e X) (differenceSecond e f g y) := by
    have hout : IsPullback (J ≫ first d e X) (pr d _)
        (pr d X) (differenceSecond e f g y ≫ pr e X) := by
      simpa only [hJfirst, differenceSecond, AffineSpace.homOfVector_over] using
        AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (pullback.fst (f ≫ g) g)
    exact hout.of_right hJ (affineGeometry d e X).1
  have hF : H ≫ J = differenceTotal d e f g x y := by
    apply AffineSpace.hom_ext
    · simp [J, H, differenceTotal, ha₁]
    · rintro ⟨k⟩
      refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k
      · simp only [J, H, differenceTotal, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord,
          Fin.addCases_left]
      · simp only [J, differenceTotal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_right]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          AffineSpace.homOfVector_over]
        simp only [differenceSecond, AffineSpace.homOfVector_appTop_coord, map_sub]
        simp only [appTop_comp_apply, ← Category.assoc, ha₁, ha₂]
  have : Etale Graw := MorphismProperty.of_isPullback hpG.flip inferInstance
  have : Etale Hraw := MorphismProperty.of_isPullback hpH.flip inferInstance
  have : Etale (differenceSecond e f g y) := by
    rw [htG]
    have := translation_isIso (fun k ↦ -((f ≫ y).appTop (AffineSpace.coord Z k)))
    infer_instance
  have : Etale H := by
    rw [htH]
    have := translation_isIso
      (fun k ↦ -((pullback.fst (f ≫ g) g ≫ x).appTop (AffineSpace.coord Y k)))
    infer_instance
  have : Etale J := MorphismProperty.of_isPullback hpJ.flip inferInstance
  have : Etale (differenceTotal d e f g x y) := by rw [← hF]; infer_instance
  have := differenceFirst_etale d f x hx
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    AffineSpace.homOfVector_over _ _, differenceFirst_diagonal d f x,
    AffineSpace.homOfVector_over _ _, ?_, AffineSpace.homOfVector_over _ _, ?_⟩
  · apply AffineSpace.hom_ext
    · simp [differenceSecond, s]
    · intro k
      simp only [differenceSecond, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, map_sub]
      simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, s, pullback.lift_snd, pullback.lift_fst, Category.id_comp,
        sub_self, AffineSpace.zeroSection_appTop_coord]
  · apply AffineSpace.hom_ext
    · simp [differenceTotal]
    · rintro ⟨k⟩
      refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k <;>
        simp only [differenceTotal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_left, Fin.addCases_right, map_sub]
      all_goals simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        pullback.diagonal_snd_assoc, pullback.diagonal_fst_assoc, sub_self,
        AffineSpace.zeroSection_appTop_coord]

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
  calc
    u' ≫ (f ≫ g) = (u' ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (f' ≫ v) ≫ g := congrArg (fun k ↦ k ≫ g) hf
    _ = f' ≫ (g' ≫ w) := by rw [Category.assoc, hg]
    _ = (f' ≫ g') ≫ w := (Category.assoc _ _ _).symm

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Scheme.pullback_map_isOpenImmersion (f' ≫ g') g' (f ≫ g) g u' v w
      (compositeSquare f g f' g' u' v w hf hg).symm hg.symm
  · apply pullback.hom_ext <;> simp [pullback.map, openPair, openMiddle, a, Category.assoc, hf]
  · simp [pullback.map, openMiddle]
  · apply pullback.hom_ext <;> simp [s, openMiddle, hf]

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
(blueprint: def-pur-diagonal-section-pasting-data). -/
def Statement (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  ModelStatement P.Coefficient P d e f g aZ

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
