/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc

/-! # Composition of exceptional images with Frobenius

Source: latest blueprint, sec-deligne-laumon-general/sk-prop-wgen-relative-line,
lem-zl-shriek-composition and its proof (blueprint: lem-zl-shriek-composition).

All restrictions below use the ordinary bounded constructible category. The normalized
comparison data are those of the existing condensed composition theorem. In particular,
the exchange is the proper/open base-change map, not an arbitrary intertwiner.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Geometric base change, in the existing category of separated finite-type schemes.
Source: latest blueprint, geometric-fibre convention in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlGeometricScheme (X₀ : SepFinType D.k₀) : SepFinType D.k :=
  ⟨Over.mk (pullback.snd X₀.obj.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))),
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))),
      inferInstanceAs (QuasiCompact (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))),
      inferInstanceAs (IsSeparated (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))⟩⟩

/-- The geometric map is exactly the map of the base-change functor.
Source: latest blueprint, geometric-fibre convention in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlGeometricHom {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    zlGeometricScheme D X₀ ⟶ zlGeometricScheme D Y₀ :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift
      (pullback.fst X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ f₀.hom.left)
      (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t ↦ pullback.fst X₀.obj.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ t)
          (Over.w f₀.hom)).trans pullback.condition)))
    (pullback.lift_snd ..))

/-- The existing chosen compactification, with Nagata supplying its existence.
Source: latest blueprint, composition constraint of lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlChosenCompactification {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    Compactification (zlGeometricHom D f₀).hom.left :=
  letI := HasCompactification.of_over (zlGeometricHom D f₀).hom
  HasCompactification.compactification (zlGeometricHom D f₀).hom.left

/-- The recorded chosen lower shriek, with its compactifiability instance supplied by Nagata.
Source: latest blueprint, exceptional images in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlAmbientShriek {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :=
  letI := HasCompactification.of_over (zlGeometricHom D f₀).hom
  rightDerivedLowerShriek (Profinite.padicAlgClRingObj ℓ) (zlGeometricHom D f₀).hom.left

/-- The normalized comparison system supplied by the condensed composition theorem.
The refinement equation determines comparison, the identity-on-the-open proper/open
normalization determines composition and open exchange, and exchange_normalized fixes
exchange. Thus the maps used below are determined, rather than chosen from a bare
existence of isomorphisms.
Source: latest blueprint, sk-thm-sf-comp-composition, applied in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlComparisonData (hℓ : ℓ ≠ D.p) :
    CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj ℓ) D.k :=
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  Classical.choice (CompactSupportComposition.coherentData_exists ℓ D.p hℓ.symm D.k
    (Profinite.padicAlgClRingObj ℓ) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))))

/-- Every ordinary bounded constructible object lies in the recorded localizing category.
Source: latest blueprint, first paragraph of lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition).
Proof: adicConstructibilityPredicateComparison identifies ordinary constructibility with
finite constant local models on the Noetherian finite-type scheme. The condensed
Qbar case of det-def-localizing-closure-ctf-equals-bc gives finite Tor amplitude.
By definition every localizing subcategory containing Dctf contains this object,
proving membership in their intersection. -/
theorem zlDbc_mem (X : SepFinType D.k)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.obj.left)) :
    localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ) X.obj.left K.obj := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : QuasiSeparatedSpace X.obj.left := IsLocallyNoetherian.quasiSeparatedSpace
  have heq := (localizingClosure_ctf_equals_bc ℓ X.obj.left
    (Profinite.padicAlgClRingObj ℓ)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  have hpred := (adicConstructibilityPredicateComparison ℓ X.obj.left
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).2
  intro P hP hgen
  apply hgen K.obj
  have hbc : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      X.obj.left K.obj := by
    rw [← hpred]
    exact K.property
  simpa only [heq] using hbc

/-- The actual full inclusion from Dbc into Loc, preserving ambient objects and morphisms.
Source: latest blueprint, restriction of composition to Dbc
(blueprint: lem-zl-shriek-composition). -/
def zlDbcToLoc (X : SepFinType D.k) :=
  (localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ) X.obj.left).lift
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.obj.left)).ι
    (zlDbc_mem D ℓ X)

/-- The chosen ambient exceptional image preserves ordinary bounded constructibility.
Source: latest blueprint, the functors on Dbc in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition).
Proof: use the constructibility comparison and det-def-localizing-closure-ctf-equals-bc to
regard the input as Dctf. Apply the preserves field of sk-thm-sf-comp-composition to the
chosen compactification; compare its constructibility predicate back to the ordinary one. -/
theorem zlShriek_mem (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D Y₀).obj.left)
      ((zlAmbientShriek D ℓ f₀).obj K.obj) := by
  let X := zlGeometricScheme D X₀
  let Y := zlGeometricScheme D Y₀
  let Λ := Profinite.padicAlgClRingObj ℓ
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  have : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : IsLocallyNoetherian Y.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  have : QuasiSeparatedSpace X.obj.left := IsLocallyNoetherian.quasiSeparatedSpace
  have hX := (adicConstructibilityPredicateComparison ℓ X.obj.left Λ .algebraicClosure).2
  have hY := (adicConstructibilityPredicateComparison ℓ Y.obj.left Λ .algebraicClosure).2
  have heq := (localizingClosure_ctf_equals_bc ℓ X.obj.left Λ
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  have hctf : (constantModelBoundedConstructible Λ X.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K.obj := by
    rw [heq, ← hX]
    exact K.property
  have hout := ((zlComparisonData D ℓ hℓ).preserves
    (zlGeometricHom D f₀) (zlChosenCompactification D f₀)).2 K.obj hctf
  exact (congrArg (fun P : ObjectProperty _ ↦ P
    ((zlAmbientShriek D ℓ f₀).obj K.obj)) hY).mpr hout.1

/-- Restriction of the existing chosen exceptional direct image to the ordinary Dbc.
Source: latest blueprint, Rf_! in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlShriek (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :=
  (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D Y₀).obj.left)).lift
    ((boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (zlGeometricScheme D X₀).obj.left)).ι ⋙
      zlAmbientShriek D ℓ f₀) (zlShriek_mem D ℓ hℓ f₀)

/-- Geometric Frobenius inverse image preserves ordinary Dbc.
Source: latest blueprint, Frobenius paragraph of sk-def-sf-weil-complexes, used in
lem-zl-shriek-composition (blueprint: lem-zl-shriek-composition).
Proof: use the exact pullback along the semilinear automorphism and its inverse.
It reindexes covers and finite stratifications and commutes with homology. This is
StrictWeil.action_preserves, transported by the canonical exact-derived comparison
leftDerivedUpperStarIsoMapDerivedCategory and adicConstructibilityPredicateComparison. -/
theorem zlFrobenius_mem (X₀ : SepFinType D.k₀)
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)
      ((moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
        (StrictWeil.modelFrobenius D X₀.obj).hom).obj K.obj) := by
  let X := zlGeometricScheme D X₀
  let Λ := Profinite.padicAlgClRingObj ℓ
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have hpred := (adicConstructibilityPredicateComparison ℓ X.obj.left Λ
    .algebraicClosure).2
  have hK : constantModelBoundedConstructible Λ X.obj.left K.obj := by
    rw [← hpred]
    exact K.property
  have hbc := (StrictWeil.action_preserves Λ
    (StrictWeil.modelFrobenius D X₀.obj) K.obj).1.mpr hK
  have hbc' : boundedConstructible (condensedRingObj Λ X.obj.left)
      ((StrictWeil.action Λ (StrictWeil.modelFrobenius D X₀.obj)).obj K.obj) := by
    exact (congrArg (fun P : ObjectProperty _ ↦ P
      ((StrictWeil.action Λ (StrictWeil.modelFrobenius D X₀.obj)).obj K.obj)) hpred).mpr hbc
  exact (boundedConstructible (condensedRingObj Λ X.obj.left)).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeil.modelFrobenius D X₀.obj).hom).app K.obj).symm hbc'

/-- LFr* on the ordinary Dbc. Its canonical comparison with the termwise exact action
identifies its fixed pairs with the recorded strict Weil complexes.
Source: latest blueprint, P_T in lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition). -/
def zlFrobenius (X₀ : SepFinType D.k₀) :=
  (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)).lift
    ((boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (zlGeometricScheme D X₀).obj.left)).ι ⋙
      moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
        (StrictWeil.modelFrobenius D X₀.obj).hom) (zlFrobenius_mem D ℓ X₀)

/-- The Frobenius square is Cartesian as a square of schemes, without k-linearity.
Source: latest blueprint, second sentence of lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition).
Proof: the universal property of the geometric fibre product gives naturality of
id times Spec(sigma) in the model morphism. Both Frobenius arrows are automorphisms;
apply IsPullback.of_horiz_isIso to this commuting square. -/
theorem zlFrobeniusSquare {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    IsPullback (StrictWeil.modelFrobenius D X₀.obj).hom (zlGeometricHom D f₀).hom.left
      (zlGeometricHom D f₀).hom.left (StrictWeil.modelFrobenius D Y₀.obj).hom := by
  apply IsPullback.of_horiz_isIso
  constructor
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change (StrictWeil.modelFrobenius D X₀.obj).hom ≫
        ((zlGeometricHom D f₀).hom.left ≫ pullback.fst _ _) =
      (zlGeometricHom D f₀).hom.left ≫
        ((StrictWeil.modelFrobenius D Y₀.obj).hom ≫ pullback.fst _ _)
    simp [zlGeometricHom, StrictWeil.modelFrobenius, D.galoisMap_projections,
      ← Category.assoc]
  · simp [zlGeometricHom, StrictWeil.modelFrobenius, Category.assoc,
      D.galoisMap_projections]

/-- Canonical Frobenius exchange, restricted from the normalized proper/open exchange.
Its direction is P_Y Rf_! to Rf_! P_X, as in the node's displayed Weil structures.
Source: latest blueprint, Frobenius compatibility in lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition). -/
def zlFrobeniusExchange (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    zlShriek D ℓ hℓ f₀ ⋙ zlFrobenius D ℓ Y₀ ≅
      zlFrobenius D ℓ X₀ ⋙ zlShriek D ℓ hℓ f₀ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (((zlComparisonData D ℓ hℓ).exchange
      (f := zlGeometricHom D f₀) (f' := zlGeometricHom D f₀)
      (zlFrobeniusSquare D f₀)
      (zlChosenCompactification D f₀) (zlChosenCompactification D f₀)).app
        ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)))
    (fun f ↦ ObjectProperty.hom_ext _
      (((zlComparisonData D ℓ hℓ).exchange
        (f := zlGeometricHom D f₀) (f' := zlGeometricHom D f₀)
        (zlFrobeniusSquare D f₀)
        (zlChosenCompactification D f₀) (zlChosenCompactification D f₀)).hom.naturality
          ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).map f)))

set_option maxHeartbeats 2000000 in
-- Elaborating the restricted comparison unfolds several derived functors and subtype lifts.
/-- Composition of exceptional images on ordinary bounded constructible Qbar complexes,
with its Frobenius exchange square. This makes both arrows of the comparison Weil maps.
Source: latest blueprint, lem-zl-shriek-composition and its proof
(blueprint: lem-zl-shriek-composition).
Proof: (1) Base change the separated finite-type models and morphisms to k using
lem-pod-separated-finite-type-base-change and the scheme conventions. For condensed Qbar,
det-def-localizing-closure-ctf-equals-bc and the constructibility comparison identify Dbc
with Dctf. Restrict the inverse composition constraint of sk-thm-sf-comp-composition.
(2) Apply its composition/exchange equation to the
Cartesian Frobenius squares, allowing their semilinear vertical maps. Invert the
composition constraint to obtain precisely the displayed square. (3) For phi:P_X K~K,
postcompose that square with Rg_!Rf_!(phi), and use naturality of beta. This gives
P_Z(beta_K) followed by phi_B equals phi_A followed by beta_K, the fixed-pair morphism
condition of sk-def-sf-weil-complexes. Invertibility also gives the inverse condition.
Naturality gives a functorial isomorphism on strict Weil pairs. -/
theorem zlShriekComposition (hℓ : ℓ ≠ D.p) {X₀ Y₀ Z₀ : SepFinType D.k₀}
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
    [IsSeparated f₀.hom.left] [LocallyOfFiniteType f₀.hom.left] [QuasiCompact f₀.hom.left]
    [IsSeparated g₀.hom.left] [LocallyOfFiniteType g₀.hom.left] [QuasiCompact g₀.hom.left] :
    ∃ β : zlShriek D ℓ hℓ (f₀ ≫ g₀) ≅ zlShriek D ℓ hℓ f₀ ⋙ zlShriek D ℓ hℓ g₀,
      ∀ K : BoundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (zlGeometricScheme D X₀).obj.left),
        (zlFrobenius D ℓ Z₀).map (β.hom.app K) ≫
            (zlFrobeniusExchange D ℓ hℓ g₀).hom.app ((zlShriek D ℓ hℓ f₀).obj K) ≫
            (zlShriek D ℓ hℓ g₀).map ((zlFrobeniusExchange D ℓ hℓ f₀).hom.app K) =
          (zlFrobeniusExchange D ℓ hℓ (f₀ ≫ g₀)).hom.app K ≫
            β.hom.app ((zlFrobenius D ℓ X₀).obj K) := by
  have hc : zlGeometricHom D (f₀ ≫ g₀) =
      zlGeometricHom D f₀ ≫ zlGeometricHom D g₀ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [zlGeometricHom, Category.assoc]
  have hc' : (zlGeometricHom D f₀).hom.left ≫ (zlGeometricHom D g₀).hom.left =
      (zlGeometricHom D (f₀ ≫ g₀)).hom.left :=
    congrArg (fun f ↦ f.hom.left) hc.symm
  let H := zlComparisonData D ℓ hℓ
  let c₁ := zlChosenCompactification D f₀
  let c₂ := zlChosenCompactification D g₀
  let c₃ := (zlChosenCompactification D (f₀ ≫ g₀)).copy hc'
  let e := H.comp (zlGeometricHom D f₀) (zlGeometricHom D g₀) c₁ c₂ c₃
  let β : zlShriek D ℓ hℓ (f₀ ≫ g₀) ≅
      zlShriek D ℓ hℓ f₀ ⋙ zlShriek D ℓ hℓ g₀ :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      (e.app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)).symm)
      (fun f ↦ ObjectProperty.hom_ext _
        (e.inv.naturality ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).map f)))
  refine ⟨β, ?_⟩
  intro K
  have h := H.laws.2.2.2.2.2.2.2.2.2.2.2
    (zlGeometricHom D f₀) (zlGeometricHom D g₀)
    (zlGeometricHom D f₀) (zlGeometricHom D g₀)
    (StrictWeil.modelFrobenius D X₀.obj).hom
    (StrictWeil.modelFrobenius D Y₀.obj).hom
    (StrictWeil.modelFrobenius D Z₀.obj).hom
    (zlFrobeniusSquare D f₀) (zlFrobeniusSquare D g₀)
    c₁ c₂ c₃ c₁ c₂ c₃
    ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)
  have hex (F G : zlGeometricScheme D X₀ ⟶ zlGeometricScheme D Z₀) (hFG : F = G)
      (sqF : IsPullback (StrictWeil.modelFrobenius D X₀.obj).hom F.hom.left F.hom.left
        (StrictWeil.modelFrobenius D Z₀.obj).hom)
      (sqG : IsPullback (StrictWeil.modelFrobenius D X₀.obj).hom G.hom.left G.hom.left
        (StrictWeil.modelFrobenius D Z₀.obj).hom)
      (c : Compactification G.hom.left) :
      H.exchange (f := F) (f' := F) sqF
          (c.copy (congrArg (fun f ↦ f.hom.left) hFG))
          (c.copy (congrArg (fun f ↦ f.hom.left) hFG)) =
        H.exchange (f := G) (f' := G) sqG c c := by
    cases hFG
    rfl
  have hx := hex (zlGeometricHom D f₀ ≫ zlGeometricHom D g₀)
    (zlGeometricHom D (f₀ ≫ g₀)) hc.symm
    ((zlFrobeniusSquare D f₀).paste_vert (zlFrobeniusSquare D g₀))
    (zlFrobeniusSquare D (f₀ ≫ g₀)) (zlChosenCompactification D (f₀ ≫ g₀))
  rw [hx] at h
  apply ObjectProperty.hom_ext
  change (moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
      (StrictWeil.modelFrobenius D Z₀.obj).hom).map
      (e.inv.app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)) ≫
      (H.exchange (zlFrobeniusSquare D g₀) c₂ c₂).hom.app
        ((zlDbcToLoc D ℓ (zlGeometricScheme D Y₀)).obj ((zlShriek D ℓ hℓ f₀).obj K)) ≫
      (zlAmbientShriek D ℓ g₀).map
        ((H.exchange (zlFrobeniusSquare D f₀) c₁ c₁).hom.app
          ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)) =
    (H.exchange (zlFrobeniusSquare D (f₀ ≫ g₀))
      (zlChosenCompactification D (f₀ ≫ g₀))
      (zlChosenCompactification D (f₀ ≫ g₀))).hom.app
        ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K) ≫
      e.inv.app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj
        ((zlFrobenius D ℓ X₀).obj K))
  have invert {C : Type _} [Category C] (F : C ⥤ C)
      {A B A' B' : C} (e₁ : A ≅ B) (e₂ : A' ≅ B')
      (x : F.obj A ⟶ A') (y : F.obj B ⟶ B')
      (comm : F.map e₁.hom ≫ y = x ≫ e₂.hom) :
      F.map e₁.inv ≫ x = y ≫ e₂.inv := by
    apply (cancel_mono e₂.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← comm, ← Functor.map_comp_assoc, e₁.inv_hom_id, F.map_id, Category.id_comp]
  exact invert
    (moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
      (StrictWeil.modelFrobenius D Z₀.obj).hom)
    (e.app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K))
    (e.app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj
      ((zlFrobenius D ℓ X₀).obj K))) _ _ (h.trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
