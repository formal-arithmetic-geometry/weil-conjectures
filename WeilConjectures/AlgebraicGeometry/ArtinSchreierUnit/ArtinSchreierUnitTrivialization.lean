/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.AffineSpace.FiniteFieldArtinSchreierMap
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierRootGeometry
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierRootNegation
public import WeilConjectures.CategoryTheory.ModuleObjects.TensorInverseEqualizerDual
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedProjectorCoverIso
import WeilConjectures.Mathlib.AlgebraicGeometry.ColimitsOver
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-! # Normalized multiplication and duality of the Artin–Schreier sheaf

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lem-wft-as-unit-trivialization and its proof (blueprint: lem-wft-as-unit-trivialization).

The function-indexed formulation writes the pullbacks of the universal maps on affine
spaces. Root evaluations specify the maps, including their normalization on disconnected
schemes. Tensor products are relative tensor products of internal coefficient modules;
the dual is the recorded equalizer internal hom, with its actual evaluation map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierUnit

open ArtinSchreierTrace

variable (k : Type u) [Field k] [Fintype k]
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The universal degree-q cover, with the existing translations.
Source: blueprint lem-wft-as-unit-trivialization, coefficient preamble
(blueprint: lem-wft-as-unit-trivialization). -/
abbrev universalCover : Over 𝔸(PUnit; Spec (.of k)) :=
  Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))

/-- The already defined averaging projector on the universal degree-q cover.
Source: blueprint lem-wft-as-unit-trivialization, coefficient preamble
(blueprint: lem-wft-as-unit-trivialization). -/
abbrev universalProjector (χ : AddChar k (MonObj.Γ Λ)) :=
  condensedProjector Λ k (universalCover k)
    (fun c ↦ Over.homMk (Etale.artinSchreierTranslation k c)
      (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)) χ

/-- Evaluation at an actual root on a splitting chart of the universal cover.
The source is exactly the recorded condensedSheafOf, not a scalar fibre.
Source: blueprint lem-wft-as-unit-trivialization, proof steps 1–2
(blueprint: lem-wft-as-unit-trivialization). -/
@[irreducible]
def rootEvaluation (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u})
    [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    (s : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ f)) ⟶ universalCover k) :
    condensedSheafOf Λ k χ X f ⟶ condensedUnit Λ X :=
  by
    unfold condensedSheafOf
    exact condensedEvaluation Λ _ s (image.ι (universalProjector k Λ χ))

/-- The canonical pullback comparison for the existing function sheaf. It is the
composition comparison of module pullbacks, followed by the equality of function maps.
Source: blueprint lem-wft-as-unit-trivialization, pullback to arbitrary X and f
(blueprint: lem-wft-as-unit-trivialization). -/
@[irreducible]
def pullFunctionIso (χ : AddChar k (MonObj.Γ Λ))
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] (f : Γ(Y, ⊤)) :
    (ProEtale.CondensedRing.upperStar Λ g).obj (condensedSheafOf Λ k χ Y f) ≅
      condensedSheafOf Λ k χ X (g.appTop f) := by
  unfold condensedSheafOf
  exact (ProEtale.CondensedRing.upperStarComp Λ g
    (AffineSpace.homOfVector (Y ↘ Spec (.of k)) (fun _ : PUnit ↦ f))).symm.app _ ≪≫
      (ProEtale.CondensedRing.upperStarCongr Λ
        ((AffineSpace.comp_homOfVector (fun _ : PUnit ↦ f) g (Y ↘ Spec (.of k))).trans
          (congrArg (fun π : X ⟶ Spec (.of k) ↦
            AffineSpace.homOfVector π (fun _ : PUnit ↦ g.appTop f))
              (CategoryTheory.comp_over g (Spec (.of k)))))).app _

/-- The specified equalizer dual, specialized to the pulled-back coefficient ring.
Source: blueprint lem-wft-as-unit-trivialization, the definition of L^vee
(blueprint: lem-wft-as-unit-trivialization). -/
abbrev functionDual (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u})
    [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :=
  (Mod.ihom' (ProEtale.condensedRingObj Λ X) (condensedSheafOf Λ k χ X f)).obj
    (condensedUnit Λ X)

/-- The inclusion of the equalizer of linear maps into the ambient internal hom.
Source: blueprint lem-wft-as-unit-trivialization, duality and evaluation
(blueprint: lem-wft-as-unit-trivialization). -/
@[irreducible]
def dualInclusion (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u})
    [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    (functionDual k Λ χ X f).X ⟶
      (ihom (condensedSheafOf Λ k χ X f).X).obj (ProEtale.condensedRingObj Λ X) :=
  (equalizer.ι
    (Mod.homModPre (ModObj.smul (M := ProEtale.condensedRingObj Λ X)
      (X := (condensedSheafOf Λ k χ X f).X)) (condensedUnit Λ X))
    (Mod.homModB (ProEtale.condensedRingObj Λ X)
      (condensedSheafOf Λ k χ X f) (condensedUnit Λ X))).hom

/-- The functional corresponding to a dual section, evaluated at epsilon^{-1}(1).
This is the underlying map of (epsilon^vee)^{-1}; no arbitrary duality isomorphism
is used. Source: blueprint lem-wft-as-unit-trivialization, zero normalization of delta
(blueprint: lem-wft-as-unit-trivialization). -/
@[irreducible]
def dualZeroEvaluation (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    (ε : condensedSheafOf Λ k χ X 0 ≅ condensedUnit Λ X) :
    (functionDual k Λ χ X 0).X ⟶ ProEtale.condensedRingObj Λ X :=
  (λ_ (functionDual k Λ χ X 0).X).inv ≫
    (MonObj.one (X := ProEtale.condensedRingObj Λ X) ≫ ε.inv.hom) ▷ (functionDual k Λ χ X 0).X ≫
      (condensedSheafOf Λ k χ X 0).X ◁ dualInclusion k Λ χ X 0 ≫
        (ihom.ev (condensedSheafOf Λ k χ X 0).X).app (ProEtale.condensedRingObj Λ X)

/-- The normalized maps and their coherence equations, written for functions.
At the two universal coordinates mu is the map on A^2; its associativity equation
at three universal coordinates is the equation on A^3. The root equations identify
these function maps with the pullbacks of those universal maps.
Source: blueprint lem-wft-as-unit-trivialization, all three paragraphs
(blueprint: lem-wft-as-unit-trivialization). -/
structure NormalizedData (χ : AddChar k (MonObj.Γ Λ)) where
  /-- Evaluation trivialization of the zero function. -/
  ε : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))],
    condensedSheafOf Λ k χ X 0 ≅ condensedUnit Λ X
  /-- The same evaluation trivialization for the inverse character. -/
  εinv : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))],
    condensedSheafOf Λ k χ⁻¹ X 0 ≅ condensedUnit Λ X
  /-- Both trivializations are evaluation at the distinguished root zero. -/
  ε_root : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (s : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ (0 : Γ(X, ⊤)))) ⟶ universalCover k),
    s.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = 0 →
      (ε X).hom = rootEvaluation k Λ χ X 0 s ∧
      (εinv X).hom = rootEvaluation k Λ χ⁻¹ X 0 s
  /-- Multiplication, with the direction in the blueprint. -/
  μ : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)),
    condensedSheafOf Λ k χ X (f + g) ≅
      condensedSheafOf Λ k χ X f ⊗ condensedSheafOf Λ k χ X g
  /-- Multiplication uses the sum of roots, fixing its canonical normalization. -/
  μ_root : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤))
    (s : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ f)) ⟶ universalCover k)
    (t : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ g)) ⟶ universalCover k)
    (v : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ f + g)) ⟶ universalCover k),
    v.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      @HAdd.hAdd Γ(X, ⊤) Γ(X, ⊤) Γ(X, ⊤) inferInstance
        (s.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
        (t.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) →
    (μ X f g).hom ≫ (rootEvaluation k Λ χ X f s ⊗ₘ rootEvaluation k Λ χ X g t) ≫
      (λ_ (condensedUnit Λ X)).hom = rootEvaluation k Λ χ X (f + g) v
  /-- The normalized multiplication is associative. -/
  associative : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g h : Γ(X, ⊤)),
    (μ X (f + g) h).hom ≫ (μ X f g).hom ▷ condensedSheafOf Λ k χ X h ≫
        (α_ (condensedSheafOf Λ k χ X f) (condensedSheafOf Λ k χ X g)
          (condensedSheafOf Λ k χ X h)).hom =
      eqToHom (congrArg (condensedSheafOf Λ k χ X) (add_assoc f g h)) ≫
        (μ X f (g + h)).hom ≫ condensedSheafOf Λ k χ X f ◁ (μ X g h).hom
  /-- Restriction along {0} times A^1 is the identity after the unit trivialization. -/
  left_unit : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)),
    eqToHom (congrArg (condensedSheafOf Λ k χ X) (zero_add f).symm) ≫
      (μ X 0 f).hom ≫ (ε X).hom ▷ condensedSheafOf Λ k χ X f ≫
        (λ_ (condensedSheafOf Λ k χ X f)).hom = 𝟙 _
  /-- At the origin multiplication is compatible with epsilon tensor epsilon. -/
  zero_normalization : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))],
    eqToHom (congrArg (condensedSheafOf Λ k χ X) (zero_add (0 : Γ(X, ⊤))).symm) ≫
      (μ X 0 0).hom ≫ ((ε X).hom ⊗ₘ (ε X).hom) ≫
        (λ_ (condensedUnit Λ X)).hom = (ε X).hom
  /-- The function multiplications are the pullbacks of the universal one. -/
  μ_pullback : ∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))] (f h : Γ(Y, ⊤)),
    (ProEtale.CondensedRing.upperStar Λ g).map (μ Y f h).hom ≫
      (Functor.Monoidal.μIso (ProEtale.CondensedRing.upperStar Λ g)
        (condensedSheafOf Λ k χ Y f) (condensedSheafOf Λ k χ Y h)).inv ≫
      (tensorIso (pullFunctionIso k Λ χ X Y g f) (pullFunctionIso k Λ χ X Y g h)).hom =
    (pullFunctionIso k Λ χ X Y g (f + h)).hom ≫
      eqToHom (congrArg (condensedSheafOf Λ k χ X) (map_add g.appTop.hom f h)) ≫
        (μ X (g.appTop f) (g.appTop h)).hom
  /-- The zero-function trivialization is pulled back from the origin. -/
  ε_pullback : ∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))],
    (ProEtale.CondensedRing.upperStar Λ g).map (ε Y).hom ≫
      (Functor.Monoidal.εIso (ProEtale.CondensedRing.upperStar Λ g)).inv =
    (pullFunctionIso k Λ χ X Y g 0).hom ≫
      eqToHom (congrArg (condensedSheafOf Λ k χ X) (map_zero g.appTop.hom)) ≫ (ε X).hom
  /-- The inverse character is identified with negation of the function. -/
  θ : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)),
    condensedSheafOf Λ k χ⁻¹ X f ≅ condensedSheafOf Λ k χ X (-f)
  /-- Negating the root specifies this identification, including characteristic two. -/
  θ_root : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    (s : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ f)) ⟶ universalCover k)
    (t : Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
      (fun _ : PUnit ↦ -f)) ⟶ universalCover k),
    t.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      -s.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) →
    (θ X f).hom ≫ rootEvaluation k Λ χ X (-f) t = rootEvaluation k Λ χ⁻¹ X f s
  /-- Negation comparison commutes with the same canonical module pullbacks. -/
  θ_pullback : ∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))] (f : Γ(Y, ⊤)),
    (ProEtale.CondensedRing.upperStar Λ g).map (θ Y f).hom ≫
      (pullFunctionIso k Λ χ X Y g (-f)).hom ≫
        eqToHom (congrArg (condensedSheafOf Λ k χ X) (map_neg g.appTop.hom f)) =
    (pullFunctionIso k Λ χ⁻¹ X Y g f).hom ≫ (θ X (g.appTop f)).hom
  /-- The dual is the specified internal hom into the coefficient module. -/
  δ : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)),
    functionDual k Λ χ X f ≅ condensedSheafOf Λ k χ⁻¹ X f
  /-- The displayed pairing in the blueprint is evaluation for delta, checked before
  the relative tensor quotient. This also states its perfection via delta being an iso. -/
  pairing : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)),
    Mod.tensorObjπ (condensedSheafOf Λ k χ X f) (condensedSheafOf Λ k χ⁻¹ X f) ≫
      ((condensedSheafOf Λ k χ X f ◁ (θ X f).hom) ≫ (μ X f (-f)).inv ≫
        eqToHom (congrArg (condensedSheafOf Λ k χ X) (add_neg_cancel f)) ≫
          (ε X).hom).hom =
      (condensedSheafOf Λ k χ X f).X ◁
        ((δ X f).inv.hom ≫ dualInclusion k Λ χ X f) ≫
          (ihom.ev (condensedSheafOf Λ k χ X f).X).app (ProEtale.condensedRingObj Λ X)
  /-- epsilon_inv composed with delta_0 equals the inverse dual of epsilon. -/
  dual_zero : ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))],
    (δ X 0).hom.hom ≫ (εinv X).hom.hom = dualZeroEvaluation k Λ χ X (ε X)

end AlgebraicGeometry.ArtinSchreierUnit

private theorem normalization_of_unit
    (h : m ≫ e.hom ▷ L ≫ (λ_ L).hom = 𝟙 L) :
    m ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ C)).hom = e.hom := by
  calc
    m ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ C)).hom =
        m ≫ e.hom ▷ L ≫ (λ_ L).hom ≫ e.hom := by
          simp only [MonoidalCategory.tensorHom_def, Category.assoc,
            leftUnitor_naturality]
    _ = e.hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun v ↦ v ≫ e.hom) h

private theorem inverse_pairing_zero
    (hunit : ∀ f, eqToHom (congrArg F (zero_add f).symm) ≫
      (μ 0 f).hom ≫ ε.hom ▷ F f ≫ (λ_ (F f)).hom = 𝟙 _)
    (hθ : (θ 0).hom ≫ eqToHom (congrArg F (neg_zero : -(0 : A) = 0)) ≫ ε.hom =
      εinv.hom) :
    F 0 ◁ (θ 0).hom ≫ (μ 0 (-0)).inv ≫
        eqToHom (congrArg F (add_neg_cancel (0 : A))) ≫ ε.hom =
      ε.hom ▷ G 0 ≫ (λ_ (G 0)).hom ≫ εinv.hom := by
  have hμ : (μ 0 (-0)).inv ≫ eqToHom (congrArg F (add_neg_cancel (0 : A))) =
      ε.hom ▷ F (-0) ≫ (λ_ (F (-0))).hom ≫
        eqToHom (congrArg F (neg_zero : -(0 : A) = 0)) := by
    rw [← cancel_epi (eqToHom (congrArg F (zero_add (-(0 : A))).symm) ≫
      (μ 0 (-0)).hom)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% (hunit (-(0 : A)))]
    simp
  rw [reassoc_of% hμ]
  rw [MonoidalCategory.whisker_exchange_assoc, leftUnitor_naturality_assoc, hθ]

private theorem zeroSectionEvaluation_heq (B : Scheme.{u})
    {Y : Over 𝔸(PUnit; B)} (s : Over.mk (AffineSpace.zeroSection PUnit B) ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology 𝔸(PUnit; B)) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ 𝔸(PUnit; B))}
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    HEq (condensedEvaluation Λ (AffineSpace.homOfVector (B ↘ B)
        (fun _ : PUnit ↦ (0 : Γ(B, ⊤)))) s ι)
      (condensedEvaluation Λ (AffineSpace.zeroSection PUnit B) s ι) := by
  exact condensedEvaluation_heq Λ
    (x := AffineSpace.homOfVector (B ↘ B) (fun _ : PUnit ↦ (0 : Γ(B, ⊤))))
    (y := AffineSpace.zeroSection PUnit B) rfl s s (HEq.refl s) ι

private theorem condensedEvaluation_heq {X T : Scheme.{u}} {x y : T ⟶ X}
    (h : x = y) {Y : Over X} (s : Over.mk x ⟶ Y) (t : Over.mk y ⟶ Y)
    (ht : HEq s t)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    HEq (condensedEvaluation Λ x s ι) (condensedEvaluation Λ y t ι) := by
  subst y
  have hst : s = t := eq_of_heq ht
  subst t
  rfl

private theorem coefficient_conditions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ))) :
    ProEtale.CondensedRing.IsAdmissibleCoefficient Λ ∧
      IsUnit (Fintype.card k : MonObj.Γ Λ) := by
  constructor
  · refine ⟨ℓ, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    rcases hΛ with hE | hB
    · exact Or.inl ⟨E, hE⟩
    · exact Or.inr hB
  · rcases hΛ with hE | hB
    · obtain ⟨e⟩ := hE
      have hq : IsUnit (Fintype.card k : E) :=
        isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      have h := hq.map ((MonObj.Γ.map e.inv.hom).comp
        (Profinite.continuousMapConstRingHom.{u} E))
      simpa only [RingHom.comp_apply, map_natCast] using h
    · obtain ⟨e⟩ := hB
      have hq : IsUnit (Fintype.card k : PadicAlgCl ℓ) :=
        isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      have h := hq.map ((MonObj.Γ.map e.inv.hom).comp
        (Profinite.PadicAlgCl.constRingHom.{u} ℓ))
      simpa only [RingHom.comp_apply, map_natCast] using h
