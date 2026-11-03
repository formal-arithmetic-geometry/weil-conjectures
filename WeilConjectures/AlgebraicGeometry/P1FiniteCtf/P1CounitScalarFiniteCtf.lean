/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-! # Finite-ctf projective-line counits and coefficient extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--35.
(blueprint: lem-sp-p1-counit-scalar).

The pro-etale right functor uses comparison inverse image of the shifted Tate line.
Exact comparison commutes canonically with the shift, so this is q^*(-)(1)[2].
The right scalar arrow is written in etale coordinates using only the normalized
pullback, tensor, shift and balanced Tate comparisons. Its descent is required on
all etale origins, making its value independent of the origin.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.P1FiniteCtf
open AdjunctionTransfer OrdinaryScalarSite

-- Fix the standard small-site instance before elaborating ambient object binders.
local instance proEtaleEssentiallySmall (S : Scheme.{u}) :
    EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _

/-- The intrinsic ordinary pro-etale finite-ctf domain: constructible cohomology,
boundedness, and a single finite Tor interval against every module sheaf. In
particular, an etale origin is a theorem about this domain, not part of its definition.
Source: def-weil-proetale-constructible-sheaf and
 def-weil-proetale-tor-amplitude; Charts (blueprint: lem-sp-p1-counit-scalar). -/
def proCtf (R : Type (u + 1)) [CommRing R] [Finite R] (S : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R))) :=
  fun K ↦
    (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf S R
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) i).obj K)) ∧
    (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) i).obj K)) ∧
    _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} R)) K

/-- Restrict an actual ambient functor to two specified full subcategories.
Source: Charts, finite-ctf domains (blueprint: lem-sp-p1-counit-scalar). -/
def restrict {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : ∀ K, P K → Q (F.obj K)) : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun K ↦ h K.obj K.property)

/-- The recorded exact comparison inverse image on derived categories.
Source: Charts, finite-site comparison (blueprint: lem-sp-p1-counit-scalar). -/
abbrev sitePull (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) S).mapDerivedCategory

/-- The ordinary pro-etale projective-line direct image. For this proper map it is
compact support at the trivial compactification, under its canonical identity-open
identification. Source: Charts (blueprint: lem-sp-p1-counit-scalar). -/
abbrev direct (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :=
  (lowerStar (ModuleCat.{u + 1} R) (ProjectiveLine S ↘ S)).rightDerivedFunctor

/-- The displayed pro-etale right functor: inverse image followed by right tensor
with comparison inverse image of the shifted finite Tate line. Source: Charts,
canonical pullback/Tate/shift comparisons (blueprint: lem-sp-p1-counit-scalar). -/
def right (R : Type (u + 1)) [CommRing R] (N : ℕ) (hR : (N : R) = 0)
    (S : Scheme.{u}) :=
  EtaleChartComparison.proPull R (ProjectiveLine S ↘ S) ⋙
    (derivedTensor (ModuleCat.{u + 1} R) (ProjectiveLine S)).flip.obj
      ((sitePull R (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteLine R N hR (ProjectiveLine S))⟦(2 : ℤ)⟧))

/-- The actual pullback and tensor comparison on one right-adjoint input. The two
outer comparisons identify termwise exact comparison with its left-derived model.
Source: Charts, canonical right-object comparison
(blueprint: lem-sp-p1-counit-scalar). -/
def rightSite (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0) (S : Scheme.{u})
    (K : Etale.DerivedCategoryModule R S) :
    (sitePull R (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteP1Right R N hR S).obj K) ≅
      (right R N hR S).obj ((sitePull R S).obj K) :=
  let C := comparisonUpperStar (ModuleCat.{u + 1} R) (ProjectiveLine S)
  let L := (Etale.ordinaryFiniteLine R N hR (ProjectiveLine S))⟦(2 : ℤ)⟧
  (C.leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
    asIso (EtaleChartComparison.nuTensor R (ProjectiveLine S)
      ((Etale.ordinaryFinitePullback R (ProjectiveLine S ↘ S)).obj K) L) ≪≫
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} R)
      (ProjectiveLine S))).mapIso
        (Iso.prod ((EtaleChartComparison.schemeIso R (ProjectiveLine S ↘ S)).app K)
          (C.leftDerivedFunctorIsoMapDerivedCategory.app L)) ≪≫
    (right R N hR S).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} R) S).leftDerivedFunctorIsoMapDerivedCategory.app K)

/-- The canonical ordinary right scalar arrow. Its line factor is the published
shifted balanced Tate map, specified on root/scalar generators by
`(z tensor a) tensor b ↦ z tensor phi(a)b`.
Source: Charts, integral Kummer classes and free summands
(blueprint: lem-sp-p1-counit-scalar). -/
def etaleArrow {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : Etale.DerivedCategoryModule A S) :
    (scalar.{u} (ProjectiveLine S).smallEtaleTopology φ).obj
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ⟶
      (Etale.ordinaryFiniteP1Right B N hB S).obj
        ((scalar S.smallEtaleTopology φ).obj K) :=
  (Etale.ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).hom.app
      ((Etale.ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    ((Etale.ordinaryFiniteTensor B (ProjectiveLine S)).map
      ((Etale.scalarPullbackIso φ (ProjectiveLine S ↘ S)).inv.app K)).app _ ≫
    ((Etale.ordinaryFiniteTensor B (ProjectiveLine S)).obj
      ((Etale.ordinaryFinitePullback B (ProjectiveLine S ↘ S)).obj
        ((scalar S.smallEtaleTopology φ).obj K))).map
      (Etale.VectorTraceScalar.line φ N hN hA hB (ProjectiveLine S)
        (Etale.ordinaryFiniteP1_isUnit N S hS))

/-- A projective-line adjunction on the actual ordinary pro-etale finite-ctf domain,
with its counit fixed by the proper counit-mate site comparison and the normalized
ordinary trace. The origin clause is essential surjectivity of that same comparison;
it ensures that normalization at etale origins determines every component.
Source: Charts and det-sp-et-proet-adjunction-transfer, actual counit formula
(blueprint: lem-sp-p1-counit-scalar). -/
structure NormalizedAdjunction (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) where
  comparison_preserves : ∀ L, etaleProperty R S L →
    proCtf R S ((sitePull R S).obj L)
  origins : ∀ K, proCtf R S K → ∃ L, etaleProperty R S L ∧
    Nonempty ((sitePull R S).obj L ≅ K)
  direct_preserves : ∀ M, proCtf R (ProjectiveLine S) M →
    proCtf R S ((direct R S).obj M)
  right_preserves : ∀ K, proCtf R S K →
    proCtf R (ProjectiveLine S) ((right R N hR S).obj K)
  adjunction :
    restrict (proCtf R (ProjectiveLine S)) (proCtf R S)
        (direct R S) direct_preserves ⊣
      restrict (proCtf R S) (proCtf R (ProjectiveLine S))
        (right R N hR S) right_preserves
  counit_normalization : ∀ (L : Etale.DerivedCategoryModule R S)
      (hL : etaleProperty R S L),
    (ambientEtaleProEtaleDirectImageComparison R (ProjectiveLine S ↘ S)).app
        ((Etale.ordinaryFiniteP1Right R N hR S).obj L) ≫
      (direct R S).map (rightSite R N hR S L).hom ≫
      (adjunction.counit.app ⟨(sitePull R S).obj L, comparison_preserves L hL⟩).hom =
    (sitePull R S).map
      ((Etale.projectiveLineTraceDatum N hN R hR S hS).adjunction.counit.app L)

/-- The right scalar arrow in an arbitrary etale-origin coordinate for K. Every
factor is prescribed: the origin iso, the right/site comparison, scalar/site delta,
the ordinary balanced arrow, and the inverse output delta. No map is chosen.
Source: Charts, transport of the canonical right arrow
(blueprint: lem-sp-p1-counit-scalar). -/
def arrowOnOrigin {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (L : Etale.DerivedCategoryModule A S) (e : (sitePull A S).obj L ≅ K) :
    (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K) ⟶
      (right B N hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K) :=
  (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).map
      ((right A N hA S).map e.inv ≫ (rightSite A N hA S L).inv) ≫
    (delta.{u} φ (ProjectiveLine S)).hom.app ((Etale.ordinaryFiniteP1Right A N hA S).obj L) ≫
    (sitePull B (ProjectiveLine S)).map (etaleArrow φ N hN hA hB S hS L) ≫
    (rightSite B N hB S ((scalar S.smallEtaleTopology φ).obj L)).hom ≫
    (right B N hB S).map
      ((delta.{u} φ S).inv.app L ≫ (scalar.{u} (Scheme.ProEt.topology S) φ).map e.hom)

/-- The actual pro-etale counit identity, invertibility and inverse-beta mate
characterization. The hom equivalence belongs to the normalized restricted adjunction;
its arrows are included by the full subcategory inclusion.
The proper coefficient mate is the compact-support coefficient map at the trivial
compactification under the identity-open normalization.
Source: Charts, final two sentences (blueprint: lem-sp-p1-counit-scalar). -/
def ProIdentity {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (dA : NormalizedAdjunction A N hN hA S hS)
    (dB : NormalizedAdjunction B N hN hB S hS)
    (hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K))
    (hTP : ∀ M, proCtf A (ProjectiveLine S) M →
      proCtf B (ProjectiveLine S)
        ((scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj M))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (hK : proCtf A S K)
    (a : (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K) ⟶
      (right B N hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K)) : Prop :=
  (proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app ((right A N hA S).obj K) ≫
      (direct B S).map a ≫
      (dB.adjunction.counit.app
        ⟨(scalar.{u} (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩).hom =
    (scalar.{u} (Scheme.ProEt.topology S) φ).map (dA.adjunction.counit.app ⟨K, hK⟩).hom ∧
  ∃ hβ : IsIso ((proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app
      ((right A N hA S).obj K)),
    IsIso a ∧
    a = (dB.adjunction.homEquiv
      ⟨(scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
        ((right A N hA S).obj K), hTP _ (dA.right_preserves K hK)⟩
      ⟨(scalar.{u} (Scheme.ProEt.topology S) φ).obj K, hTS K hK⟩
      (ObjectProperty.homMk
        (@inv _ _ _ _ ((proEtaleGamma.{u} φ (ProjectiveLine S ↘ S)).app
          ((right A N hA S).obj K)) hβ ≫
          (scalar.{u} (Scheme.ProEt.topology S) φ).map
            (dA.adjunction.counit.app ⟨K, hK⟩).hom))).hom

/-- Scalar compatibility of the actual normalized projective-line counits on both
finite-ctf domains, including characteristic zero and nonflat coefficient maps.
All data introduced existentially are characterized by the displayed canonical maps;
no extra geometric, coefficient, or comparison hypothesis is assumed.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--35.
(blueprint: lem-sp-p1-counit-scalar).

Proof plan:
1. Since char(k) differs from ell, N is invertible on S and P, including char(k)=0.
Finite type over a field makes S Noetherian; properness does the same for P.
The chart-domain theorem supplies preservation, the finite-ctf comparison equivalence,
and an etale origin for every pro-etale input.
2. Apply lem-pur-ordinary-chart-p1-counit-scalar to the etale input. Its trace is
projection onto the free twisted summand of the Kummer-normalized splitting.
lem-sp-finite-p1-coefficient-splitting supplies the same integral Kummer and diagonal
classes. Thus its right arrow is precisely etaleArrow, with the balanced Tate map.
3. Transfer each actual adjunction using det-sp-et-proet-adjunction-transfer and
the specified compact-support comparison. The right functor is identified by
rightSite, built from the actual pullback and tensor comparisons. Exact comparison
commutes with shifts. Scalar/site delta and the balanced Tate map identify its
right scalar arrow with arrowOnOrigin for every origin.
4. Apply lem-sp-et-proet-coefficient-compatibility at the right-adjoint input.
Paste its site/coefficient square with the two normalized counit equations and
the right-arrow comparison. Naturality moves the outer deltas and origin isos.
Cancel the invertible outer maps. The ordinary counit equation then gives the
pro-etale equation, independently of the chosen origin.
5. lem-asd-proper-finite-coefficient-extension makes ordinary beta invertible.
The site/coefficient square and the comparison equivalences do so on pro-etale
finite-ctf inputs. Precompose the counit equation with inverse beta; the actual
B adjunction Hom bijection identifies the specified arrow as its unique transpose.
No purity, exchange, or biduality comparison is used. -/
theorem p1CounitScalarFiniteCtf
    (ℓ n : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hchar : ringChar k ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ℓ ^ n : ℕ) : A) = 0) (hB : ((ℓ ^ n : ℕ) : B) = 0)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    ∃ hN : 0 < ℓ ^ n, ∃ hS : IsUnit ((ℓ ^ n : ℕ) : Γ(S, ⊤)),
    ∃ hNoeth : IsNoetherian S,
    letI := hNoeth
    (∀ (K : Etale.DerivedCategoryModule A S) (_hK : etaleProperty A S K),
      (Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K) ≫
        (Etale.ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          (etaleArrow φ (ℓ ^ n) hN hA hB S hS K) ≫
        (Etale.projectiveLineTraceDatum (ℓ ^ n) hN B hB S hS).adjunction.counit.app
          ((scalar S.smallEtaleTopology φ).obj K) =
      (scalar S.smallEtaleTopology φ).map
        ((Etale.projectiveLineTraceDatum (ℓ ^ n) hN A hA S hS).adjunction.counit.app K) ∧
      ∃ hβ : IsIso ((Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K)),
        IsIso (etaleArrow φ (ℓ ^ n) hN hA hB S hS K) ∧
        etaleArrow φ (ℓ ^ n) hN hA hB S hS K =
          (Etale.projectiveLineTraceDatum (ℓ ^ n) hN B hB S hS).adjunction.homEquiv _ _
            (@inv _ _ _ _ ((Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
              ((Etale.ordinaryFiniteP1Right A (ℓ ^ n) hA S).obj K)) hβ ≫
              (scalar S.smallEtaleTopology φ).map
                ((Etale.projectiveLineTraceDatum (ℓ ^ n) hN A hA S hS).adjunction.counit.app K))) ∧
    ∃ dA : NormalizedAdjunction A (ℓ ^ n) hN hA S hS,
    ∃ dB : NormalizedAdjunction B (ℓ ^ n) hN hB S hS,
    ∃ hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K),
    ∃ hTP : ∀ M, proCtf A (ProjectiveLine S) M →
      proCtf B (ProjectiveLine S)
        ((scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj M),
    ∀ (K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (hK : proCtf A S K),
      ∃ a : (scalar.{u} (Scheme.ProEt.topology (ProjectiveLine S)) φ).obj
          ((right A (ℓ ^ n) hA S).obj K) ⟶
        (right B (ℓ ^ n) hB S).obj ((scalar.{u} (Scheme.ProEt.topology S) φ).obj K),
        (∀ (L : Etale.DerivedCategoryModule A S) (_hL : etaleProperty A S L)
          (e : (sitePull A S).obj L ≅ K),
          a = arrowOnOrigin φ (ℓ ^ n) hN hA hB S hS K L e) ∧
        ProIdentity φ (ℓ ^ n) hN hA hB S hS dA dB hTS hTP K hK a := by
  sorry

end AlgebraicGeometry.ProEtale.P1FiniteCtf
