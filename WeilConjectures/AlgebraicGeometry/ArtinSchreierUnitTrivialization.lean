/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTraceComparison
public import WeilConjectures.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.FiniteFieldArtinSchreierMap
import WeilConjectures.DeligneLaumon.FiniteEtaleCondensedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

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

/-- The distinguished zero root in the universal degree-q covering.
Source: blueprint lem-wft-as-unit-trivialization, evaluation at y=0
(blueprint: lem-wft-as-unit-trivialization). -/
def originRoot : Over.mk (AffineSpace.zeroSection PUnit (Spec (.of k))) ⟶ universalCover k :=
  Over.homMk (AffineSpace.zeroSection PUnit (Spec (.of k)))
    Etale.zeroSection_comp_artinSchreierMap

/-- Compatibility with the trace comparison to the prime-field cover. The comparison
is the pullback of functions along the trace-polynomial morphism, not a chosen iso.
Its evaluation equation uses the same epsilon as the multiplication and duality data.
Source: blueprint lem-wft-as-unit-trivialization, last sentence and comparison (3)
(blueprint: lem-wft-as-unit-trivialization). -/
@[irreducible]
def PrimeCompatibility (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
    (χ : AddChar k (MonObj.Γ Λ)) (S : NormalizedData k Λ χ) : Prop :=
  HEq (S.ε (Spec (.of k))).hom
    (condensedEvaluation Λ (AffineSpace.zeroSection PUnit (Spec (.of k)))
      (originRoot k) (image.ι (universalProjector k Λ χ))) ∧
  ∀ (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)), Ψ ≠ 1 → ∀ a : kˣ,
    χ = (Ψ.compTrace k).mulShift (a : k) →
    ∃ (σp : ZMod p → (originPCover p k (a : k) ⟶ originPCover p k (a : k)))
      (h : universalCover k ⟶ originPCover p k (a : k))
      (e : image (condensedProjector Λ (ZMod p) (originPCover p k (a : k)) σp Ψ) ≅
        image (universalProjector k Λ χ)),
      (∀ b : ZMod p, (σp b).left.appTop
          (artinSchreierCoverCoordinate p _
            (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
        artinSchreierCoverCoordinate p _
          (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit) +
            (b.val : Γ((originPCover p k (a : k)).left, ⊤))) ∧
      h.left.appTop (artinSchreierCoverCoordinate p _
        (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
        ∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
          (@HMul.hMul Γ(𝔸(PUnit; Spec (.of k)), ⊤) Γ(𝔸(PUnit; Spec (.of k)), ⊤)
            Γ(𝔸(PUnit; Spec (.of k)), ⊤) inferInstance
            ((universalCover k).hom.appTop (scalar k _ (a : k)))
            (AffineSpace.coord (Spec (.of k)) PUnit.unit)) ^ (p ^ i) ∧
      e.hom ≫ image.ι (universalProjector k Λ χ) =
        image.ι (condensedProjector Λ (ZMod p) (originPCover p k (a : k)) σp Ψ) ≫
          condensedPull Λ h ∧
      (originRoot k ≫ h).left.appTop (artinSchreierCoverCoordinate p _
        (scalar k _ (a : k) * AffineSpace.coord (Spec (.of k)) PUnit.unit)) = 0 ∧
      (ProEtale.CondensedRing.upperStar Λ
        (AffineSpace.zeroSection PUnit (Spec (.of k)))).map e.hom ≫
          (condensedEvaluation Λ (AffineSpace.zeroSection PUnit (Spec (.of k)))
            (originRoot k) (image.ι (universalProjector k Λ χ))) =
        condensedEvaluation Λ (AffineSpace.zeroSection PUnit (Spec (.of k)))
          (originRoot k ≫ h)
          (image.ι (condensedProjector Λ (ZMod p) (originPCover p k (a : k)) σp Ψ))

/-- Evaluation at the zero root rigidifies the Artin–Schreier sheaf, with associative
multiplication, its unit law, the normalized inverse-character duality, and the
specified trace comparison. Coefficients are exactly E or Qbar_l, as condensed rings.
Source: latest blueprint sec-fourier-transform/sk-lem-as-properties,
lem-wft-as-unit-trivialization (blueprint: lem-wft-as-unit-trivialization).

Proof (the nine steps of the node):
1. The finite etale degree-q torsor and its translation-indexed self-pullback are
   lem-wft-finite-field-as-map. Apply lem-a1-finite-etale-condensed-base-change to
   identify the pulled-back direct image with a finite product of coefficient rings.
   An additive pullback preserves the retract given by the averaging idempotent.
2. Its image consists of functions v(t+c)=chi(c)v(t). Evaluation at a chosen root t
   has inverse b mapped to the function t+c mapped to chi(c)b. These module maps
   commute with restriction. At zero use the distinguished root zero, for chi and
   chi inverse, giving epsilon and epsilon_inv.
3. On the common chart with roots t1,t2, define mu by evaluation at t1+t2 and the
   inverse of coefficient multiplication. Translation changes the two sides by
   chi(c1+c2)=chi(c1)chi(c2); lem-pur-sheaf-hom-cover-gluing descends the map and its
   inverse. The recorded relative tensor and strong monoidal module pullback give
   the tensor comparison. Finite-etale exchange gives its pullback compatibility.
4. At zero this is epsilon tensor epsilon; on three-root charts both iterates
   evaluate at t1+t2+t3. With first root zero the map is the identity. Gluing detects
   these equations, yielding associativity and the left unit law.
5. Pull epsilon back through the zero section to every scheme, using the canonical
   composition and coefficient-unit comparisons. This gives the zero-function
   trivialization even for empty and disconnected schemes.
6. Negating roots sends f to -f and chi inverse to chi, also in characteristic two.
   The map h(z) mapped to h(-z) is its own inverse and fixes the zero root. Its
   evaluation formula and naturality give theta and its pullback equation.
7. Compose 1 tensor theta, mu inverse, and epsilon to form the displayed pairing.
   On a root chart it is (a,b) mapped to ab. Its adjoint into the equalizer internal
   hom is an isomorphism, with inverse lambda mapped to lambda(1) in coordinates.
   The local inverses glue; delta is the inverse adjoint, giving the pairing equation.
8. At zero this pairing is epsilon(a)epsilon_inv(b), so epsilon_inv composed with
   delta_0 evaluates a functional at epsilon inverse of 1. The same calculation
   after any pullback gives precisely the evaluation pairing for every f.
9. By lem-wft-as-comparison write chi=Psi composed with Tr(a times -). The trace
   polynomial sends zero to zero, and its comparison pulls back functions. Thus
   evaluation after comparison at y=0 is evaluation at u=0, for this same epsilon.
The symmetric monoidal abelian pullback is lem-sfb-finite-upper-star-braided;
def-sfb-mapmod-strong-monoidal and def-sfb-comap-iso-strong-monoidal transport it
and change coefficients. No unspecified isomorphism replaces any canonical map. -/
theorem artinSchreier_unit_trivialization
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    [Algebra (ZMod p) k] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hroots : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)))
    (ψ : AddChar k (MonObj.Γ Λ)) (hψ : ψ ≠ 1) :
    ∃ S : NormalizedData k Λ ψ, PrimeCompatibility k Λ p ψ S := by
  sorry

end AlgebraicGeometry.ArtinSchreierUnit
