/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ReductionCtfFunctors
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
public import WeilConjectures.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction

/-!
# Open locality of the finite exceptional coefficient mate

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Locality
(blueprint: lem-sp-finite-exceptional-coefficient-open-locality).

All right adjoints are on the actual full Dctf subcategories. The comparison for the
restricted map uses the inherited compactification. Counit equations specify both
exceptional coefficient arrows and both right-adjoint identifications, without choosing
an unrelated isomorphism. The final equality is written in ambient intrinsic coordinates;
the full-subcategory inclusions are faithful.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.FiniteExceptionalOpenLocality

/-- The compact-support compositor for the compactification inherited by the source open.
Its open factor is the existing unit-normalized open compositor, and its proper factor
is unchanged. Source: blueprint reduction-exceptional, Locality
(blueprint: lem-sp-finite-exceptional-coefficient-open-locality). -/
def compactIso (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] (p : Z ⟶ Y) :
    reductionCompactSupport R (j ≫ i) p ≅
      sfIntrinsicDerivedOpen R j ⋙ reductionCompactSupport R i p :=
  isoWhiskerRight (sfIntrinsicDerivedOpenComp R j i) (directImageConstantPush R p) ≪≫
    associator _ _ _

/-- The canonical scalar/pullback comparison in intrinsic restriction coordinates.
The outside changes of coordinates preserve the constant-section units; the middle
factor is the existing balanced tensor/pullback comparison, in the required direction.
Source: blueprint reduction-exceptional, Locality; Stacks 06YY
(blueprint: lem-sp-finite-exceptional-coefficient-open-locality). -/
def scalarIso {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) :
    sfIntrinsicDerivedPullback A j ⋙ scalarExtensionFunctor φ U ≅
      scalarExtensionFunctor φ X ⋙ sfIntrinsicDerivedPullback B j :=
  isoWhiskerRight (openSquareDerivedPullbackModel A j).symm
      (scalarExtensionFunctor φ U) ≪≫
    (directImageScalarPullbackIso φ j).symm ≪≫
    isoWhiskerLeft (scalarExtensionFunctor φ X) (openSquareDerivedPullbackModel B j)

/-- The counit-preserving characterization of the right-adjoint open identification.
This is precisely the counit equation for the unique right-adjoint isomorphism between
an adjoint of the inherited compact support and the composite of the open adjunction
`exceptionalOpenAdjunction` (j_! ⊣ j^*) with the given compact-support adjunction.
Only the displayed component is needed.
Source: blueprint reduction-exceptional, Locality; composite-adjunction convention
(blueprint: lem-sp-finite-exceptional-coefficient-open-locality). -/
def CounitIdentification (R : Type u) [CommRing R] [Finite R]
    {U X Z Y : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] (p : Z ⟶ Y)
    (hF : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R i p).obj M.obj))
    (hG : ∀ M : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R (j ≫ i) p).obj M.obj))
    (F : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R)
    (G : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory U R)
    (aF : reductionCtfCompactSupport R i p hF ⊣ F)
    (aG : reductionCtfCompactSupport R (j ≫ i) p hG ⊣ G)
    (K : spFiniteConstructibleTorCategory Y R)
    (δ : (G.obj K).obj ≅ (sfIntrinsicDerivedPullback R j).obj (F.obj K).obj) : Prop :=
  (reductionCompactSupport R i p).map
      ((sfIntrinsicDerivedOpen R j).map δ.hom ≫
        (exceptionalOpenAdjunction j R).counit.app (F.obj K).obj) ≫
      (aF.counit.app K).hom =
    (compactIso R j i p).inv.app (G.obj K).obj ≫ (aG.counit.app K).hom

end AlgebraicGeometry.ProEtale.FiniteExceptionalOpenLocality

namespace AlgebraicGeometry.ProEtale

/-- Open locality of the actual fixed-compactification exceptional coefficient mate.
The equations `hcF` and `hcG` characterize the unique mates: they are the displayed
inverse-coefficient counit equations after multiplication by the invertible actual b.
The two `CounitIdentification` equations fix the unique counit-preserving right-adjoint
identifications. Thus the conclusion is c_g = j_B^*(c_f) a_j under those identifications.
No invertibility of either exceptional mate, finite cohomological dimension of k,
flatness of B over A, or finite projective dimension of B over A is assumed.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Locality
(blueprint: lem-sp-finite-exceptional-coefficient-open-locality).

Proof:
1. For g = j f, inherit the compactification U -> X -> Z -> Y. Its proper part is p,
   and its open part is j i. The existing normalized open compositor gives `compactIso`.
   Compose j_! adjoint to j^* with each restricted compact-support adjunction. Uniqueness
   of right adjoints identifies the result with G_g by its counit equation, exactly
   `CounitIdentification`.
2. Expand `reductionDirectImageComparison` into the proper counit mate followed by the
   normalized open scalar isomorphism. The pro-etale open-coefficient compositor states
   that the normalized comparison for j i is the pasted comparison for i and j. Since
   the proper part p is unchanged, substitution and naturality identify the actual b_g
   with the composite of b_f at j_!(-) and the source-open scalar comparison.
3. The pro-etale open-coefficient-mate identity identifies the open-adjunction mate of
   the inverse open coefficient map with `scalarIso`. Apply mate pasting to Step 2,
   using the inverse of b_f and the composite adjunctions from Step 1. The resulting
   mate is `scalarIso` followed by restriction of c_f. Its inverse transpose is the
   right side of the defining counit equation for c_g. Injectivity of the adjunction
   Hom equivalence gives the claimed equality. This uses no invertibility of c_f or c_g.
-/
theorem finiteExceptionalCoefficient_open_locality
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {U X Z Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (i : X ⟶ Z) [IsOpenImmersion i] [i.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : i ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A i p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B i p).obj M.obj))
    (hGA : ∀ M : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A (j ≫ i) p).obj M.obj))
    (hGB : ∀ M : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B (j ≫ i) p).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (FA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (FB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory U A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory U B)
    (aFA : reductionCtfCompactSupport A i p hFA ⊣ FA)
    (aFB : reductionCtfCompactSupport B i p hFB ⊣ FB)
    (aGA : reductionCtfCompactSupport A (j ≫ i) p hGA ⊣ GA)
    (aGB : reductionCtfCompactSupport B (j ≫ i) p hGB ⊣ GB)
    (K : spFiniteConstructibleTorCategory Y A)
    (δA : (GA.obj K).obj ≅ (sfIntrinsicDerivedPullback A j).obj (FA.obj K).obj)
    (δB : (GB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj ≅
      (sfIntrinsicDerivedPullback B j).obj
        (FB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj)
    (hδA : FiniteExceptionalOpenLocality.CounitIdentification
      A j i p hFA hGA FA GA aFA aGA K δA)
    (hδB : FiniteExceptionalOpenLocality.CounitIdentification
      B j i p hFB hGB FB GB aFB aGB ((reductionCtfScalar φ Y hSY).obj K) δB)
    (cF : (scalarExtensionFunctor φ X).obj (FA.obj K).obj ⟶
      (FB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj)
    (cG : (scalarExtensionFunctor φ U).obj (GA.obj K).obj ⟶
      (GB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj)
    (hcF : (reductionDirectImageComparison φ i p).app (FA.obj K).obj ≫
      (reductionCompactSupport B i p).map cF ≫
        (aFB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
      (scalarExtensionFunctor φ Y).map (aFA.counit.app K).hom)
    (hcG : (reductionDirectImageComparison φ (j ≫ i) p).app (GA.obj K).obj ≫
      (reductionCompactSupport B (j ≫ i) p).map cG ≫
        (aGB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
      (scalarExtensionFunctor φ Y).map (aGA.counit.app K).hom) :
    cG ≫ δB.hom =
      (scalarExtensionFunctor φ U).map δA.hom ≫
        (FiniteExceptionalOpenLocality.scalarIso φ j).hom.app (FA.obj K).obj ≫
          (sfIntrinsicDerivedPullback B j).map cF := by
  sorry

end AlgebraicGeometry.ProEtale
