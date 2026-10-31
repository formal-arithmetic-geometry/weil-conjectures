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

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
