/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.OrderedAffineTraceNormalForm
public import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.FiniteTateScalarSourceNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleCompactScalarCoherence
public import WeilConjectures.SecSmoothPurity.FiniteP1CoefficientSplitting
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.CategoryTheory.CounitTensorTower
import WeilConjectures.SecSmoothPurity.OrdinaryChartP1CounitScalar

/-!
# Finite coefficient change of the actual ordered affine counit

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, ordered projective-line integration
(blueprint: lem-sp-finite-affine-coefficient-counit).

The right functor is the specified direct Tate normal form. Its scalar exchange is
assembled from the normalized scalar tensor, pullback, Tate and shift maps. The
adjunction is transported from the ordered coordinate tower through the existing
left compactification comparison and the specified right normal form.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale

/-- Move the accumulated even shift from the whole tensor onto its Tate factor.
This is the inverse of the existing derived-tensor shift comparison.
Source: Charts, canonical tensor and shift reassociation
(blueprint: lem-sp-finite-affine-coefficient-counit). -/
def finiteAffineShiftPlacement (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (d : ℕ)
    (K : DerivedCategoryModule A S) :
    (orderedAffineRight A N hA S (d + 1)).obj K ≅
      ((ordinaryFiniteTensor A (affineTraceTower S (d + 1))).obj
        ((ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj K)).obj
        (finiteTateScalarObject A N hA (affineTraceTower S (d + 1)) (d + 1)) :=
  (derivedTensorRightShiftIso (ModuleCat.{u + 1} A)
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateTwist (affineTraceTower S (d + 1)) N A hA (d + 1)))
    (2 * ((d + 1 : ℕ) : ℤ))).symm.app
      ((ordinaryFinitePullback A (affineTraceProjection S (d + 1))).obj K)

/-- The single canonical scalar exchange on the direct affine right normal form.
The Tate balancing family is selected from its uniquely generator-normalized theorem;
its value on roots is `(z tensor a) tensor b` sent to `z tensor phi(a)b`.
At zero the right functor and its exchange are literal identities.
Source: Charts, canonical scalar/tensor/pullback/Tate/shift reassociation
(blueprint: lem-sp-finite-affine-coefficient-counit). -/
def finiteAffineRightScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → (K : DerivedCategoryModule A S) →
      (scalarExtension φ (affineTraceTower S d)).obj
          ((orderedAffineRight A N hA S d).obj K) ≅
        (orderedAffineRight B N hB S d).obj ((scalarExtension φ S).obj K)
  | 0, _ => Iso.refl _
  | d + 1, K =>
    let X := affineTraceTower S (d + 1)
    let hX := affineTraceInvertible N S hS (d + 1)
    let hx := fun x : X ↦ hX.map (X.presheaf.germ ⊤ x trivial).hom
    let hs := fun s : S ↦ hS.map (S.presheaf.germ ⊤ s trivial).hom
    let e := (finite_tate_scalar_source_normalization φ N hN hA hB X
      (fun x ↦ by simpa only [map_natCast] using hx x)).2
    let β := e.choose
    let i := e.choose_spec.1.2.2.1 S
      (fun s ↦ by simpa only [map_natCast] using hs s)
      (affineTraceProjection S (d + 1)) K (d + 1)
    (scalarExtension φ X).mapIso (finiteAffineShiftPlacement A N hA S d K) ≪≫
      @asIso _ _ _ _
        (finiteTateScalarSourceMap φ N hA hB
          (affineTraceProjection S (d + 1)) (d + 1) (β (d + 1)) K) i ≪≫
      (finiteAffineShiftPlacement B N hB S d ((scalarExtension φ S).obj K)).symm

/-- The actual ordered adjunction on the specified compactification, transported
through the canonical left comparison and the recursively specified right normal form.
No counit or orientation is chosen separately. Dimension zero starts from Adjunction.id
and still uses the comparison to the supplied, possibly nonidentity, compactification.
Source: Charts, fixed-compactification ordered integration
(blueprint: lem-sp-finite-affine-coefficient-counit). -/
def finiteAffineCompactAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      orderedAffineRight A N hA S d :=
  ((affineTraceAdjunction A N hA t D S hS d).ofNatIsoLeft
    (ProEtale.reductionEtaleAffineLeftIso A S d c)).ofNatIsoRight
      (orderedAffineRightIso A N hN hA S hS d)

/-- Finite coefficient change commutes with the actual specified affine integration
counit, and proper refinements identify these actual counits for both coefficient rings.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-sp-finite-affine-coefficient-counit).

Proof:
1. Apply lem-pur-ordinary-chart-p1-counit-scalar to each coordinate projective line.
   The unit/Kummer splitting and trace are exactly those of
   lem-sp-finite-p1-coefficient-splitting, so this is the actual projective counit square.
2. The open balancing inverse is the open-unit transpose. Its triangle identities give
   the open counit square. Paste with the projective square using mate pasting and the
   composite-adjunction counit formula. Its left map is the proper/open compact scalar map.
3. Apply lem-pur-counit-tensor-tower in coordinate order, starting with the identity
   square. The specified right normal-form equation of
   lem-sp-finite-affine-right-scalar-normal-form identifies the recursively pasted right
   exchange with finiteAffineRightScalarIso. No tensor factors are permuted.
4. Finite Tor amplitude applied to the degree-zero coefficient sheaf B bounds T K.
   Exact pullback, flat Tate tensor and finite shifts bound both right inputs. Every
   intermediate compact-support image is bounded below; its scalar image is identified
   with the B image by lem-pur-etale-compact-scalar-coherence.
5. Induct on the left compact-support comparison. At zero the identity normalization
   and the scalar refinement square include every compactification of the identity.
   At a successor, substitute the scalar composition square, the induction hypothesis
   at the last line image, and naturality of the B comparison. This identifies the left
   tower exchange with the actual compactScalarMap for c. The ambient comparison
   restricts to the bounded-below comparison of lem-amb-etale-compact-comparisons.
6. Substitute that comparison into step 3 and cancel scalar extension of the left
   comparison. Transport on the right through orderedAffineRightIso; the counit becomes
   precisely finiteAffineCompactAdjunction.counit. This proves the first equation.
   The common-refinement cocycle and scalar refinement equation identify the transported
   counits for every proper refinement, giving the final two equations. All bounds come
   from step 4. Neither a field base nor flatness of B over A is used.
-/
theorem finiteAffineCoefficientCounit
    (N : ℕ) (hN : 0 < N)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A S)
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
    (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K))
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) a b K) :
    ((compactScalarMap φ c).app ((orderedAffineRight A N hA S d).obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (finiteAffineRightScalarIso φ N hN hA hB S hS d K).hom ≫
        (finiteAffineCompactAdjunction B N hN hB tB DB S hS d c).counit.app
          ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map
        ((finiteAffineCompactAdjunction A N hN hA tA DA S hS d c).counit.app K)) ∧
    ∀ (c' : Compactification (affineTraceProjection S d)) (_r : c.Refinement c'),
      ((rightDerivedLowerShriekOfCompactificationIso A c c').hom.app
          ((orderedAffineRight A N hA S d).obj K) ≫
          (finiteAffineCompactAdjunction A N hN hA tA DA S hS d c').counit.app K =
        (finiteAffineCompactAdjunction A N hN hA tA DA S hS d c).counit.app K) ∧
      ((rightDerivedLowerShriekOfCompactificationIso B c c').hom.app
          ((orderedAffineRight B N hB S d).obj ((scalarExtension φ S).obj K)) ≫
          (finiteAffineCompactAdjunction B N hN hB tB DB S hS d c').counit.app
            ((scalarExtension φ S).obj K) =
        (finiteAffineCompactAdjunction B N hN hB tB DB S hS d c).counit.app
          ((scalarExtension φ S).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
