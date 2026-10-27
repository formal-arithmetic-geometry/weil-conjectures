/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.SecSmoothPurity.IntrinsicCtfRefinementComparison
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
public import Sheaf.Paper.MateOpenRestriction
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Restrict
import Sheaf.Paper.EtaleCtfChartDomain

/-! # Inverse-transpose factorization for source-open composition

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph; Stacks 0DV0, 0F7J, 0GL6
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization).

The refinement comparison is uniquely specified on every bounded-below etale origin.
Thus its use below does not restrict the input to a chosen origin, or choose an arbitrary
comparison. Open composition is the published unit-normalized open compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.OpenInverseTranspose

/-- Restriction of the actual compactification functor to the given full categories.
Source: blueprint Locality, F_h
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
abbrev support (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj Q.obj)) :=
  (spFiniteConstructibleTor Y R).lift
    ((spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R c.i c.g) h

/-- Restrict the recorded exact open extension, retaining its ambient maps.
Source: blueprint Locality, J_R
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
abbrev extension (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj Q.obj)) :=
  (spFiniteConstructibleTor X R).lift
    ((spFiniteConstructibleTor U R).ι ⋙ sfIntrinsicDerivedOpen R j) h

/-- Restrict the recorded exact inverse image to the finite-Tor subcategories.
Source: blueprint Locality, U_R
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
abbrev restriction (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((sfIntrinsicDerivedPullback R j).obj Q.obj)) :=
  (spFiniteConstructibleTor U R).lift
    ((spFiniteConstructibleTor X R).ι ⋙ sfIntrinsicDerivedPullback R j) h

/-- The actual localized open adjunction, restricted along the full inclusions.
Source: Stacks 03DI, 09AE; blueprint Locality, v_R
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
def openAdjunction (R : Type u) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (hJ : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj Q.obj))
    (hU : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((sfIntrinsicDerivedPullback R j).obj Q.obj)) :
    extension R j hJ ⊣ restriction R j hU :=
  (exceptionalOpenAdjunction j R).restrictFullyFaithful
    (spFiniteConstructibleTor U R).fullyFaithfulι
    (spFiniteConstructibleTor X R).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The canonical source-open compositor: change to the restricted compactification,
then apply the published unit-normalized open compositor. This includes arbitrary
compactifications and therefore changes through every common refinement.
Source: Stacks 0F7J; blueprint Locality
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
def composition (R : Type u) [CommRing R] [Finite R]
    {U X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (c : Compactification f) (d : Compactification (j ≫ f))
    (hF : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj Q.obj))
    (hJ : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj Q.obj))
    (hG : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R d.i d.g).obj Q.obj)) :
    support R d hG ≅ extension R j hJ ⋙ support R c hF :=
  Functor.fullyFaithfulCancelRight (spFiniteConstructibleTor Y R).ι
    (refinement R d (c.precomp j) ≪≫
      Functor.isoWhiskerLeft (spFiniteConstructibleTor U R).ι
        (Functor.isoWhiskerRight (sfIntrinsicDerivedOpenComp R j c.i)
          (directImageConstantPush R c.g) ≪≫ Functor.associator _ _ _))

/-- Transport the composite adjunction by the specified compact-support compositor.
In these coordinates G_g is exactly U_R G_f; units and counits are transported together.
Source: Stacks 0DV0; blueprint Locality
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization). -/
def compositeAdjunction (R : Type u) [CommRing R] [Finite R]
    {U X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (c : Compactification f) (d : Compactification (j ≫ f))
    (hF : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj Q.obj))
    (hJ : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor X R ((sfIntrinsicDerivedOpen R j).obj Q.obj))
    (hU : ∀ Q : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor U R ((sfIntrinsicDerivedPullback R j).obj Q.obj))
    (hG : ∀ Q : spFiniteConstructibleTorCategory U R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R d.i d.g).obj Q.obj))
    (G : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R)
    (adj : support R c hF ⊣ G) :
    support R d hG ⊣ G ⋙ restriction R j hU :=
  ((openAdjunction R j hJ hU).comp adj).ofNatIsoLeft
    (composition R j c d hF hJ hG).symm

/-- Composite counits, the specified coefficient-composition equation, and its inverse
naturality factorization on arbitrary intrinsic pro-etale finite-Tor input.
Source: latest blueprint, sk-lem-sp-reduction-exceptional.proof.md, Locality;
Stacks 0DV0, 0GL6 and 0F7J
(blueprint: lem-sp-open-scalar-inverse-transpose-factorization).

Proof:
1. Adjunction.comp computes each composite counit as F_f of the actual open counit
   followed by epsilon_f. Transport along composition gives the first two clauses.
2. Lem-sp-etale-ctf-chart-domain gives an etale Dctf origin for arbitrary L and the
   needed scalar and compact-support domains, without a flatness assumption on B/A.
3. The proper factor for the identity compactification of j is identity: its defining
   transpose is the scalar extension of the identity counit. Thus the normalized open
   comparison of def-sp-reduction-direct-image-comparison is reductionOpenScalarIso.
4. Lem-sp-et-proet-coefficient-compatibility gives the coefficient-composition square
   on etale origins. Naturality at the origin isomorphism and cancellation give the
   third clause for the arbitrary L. The normalization of refinement transports the
   same square to the two supplied compactifications, through any common refinement.
5. Invert this square. Naturality of reductionDirectImageComparison at the actual
   open counit v says TY(F_f(v)) b_f(JL)^(-1) = b_f(M)^(-1) F_f(TX(v)). Substitute
   this and the composite-counit formula. Functoriality and associativity give the
   final clause, with source F_g,B(TU L) and target TY K. No exceptional mate is used.
-/
theorem openScalarInverseTransposeFactorization
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hℓ : p ≠ ℓ)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hN : 1 ≤ ℓ ^ n)
    (_hA : (ℓ ^ n : A) = 0) (_hB : (ℓ ^ n : B) = 0)
    {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (c : Compactification f) (d : Compactification (j ≫ f))
    [c.Z.Over (Spec (.of k))] [d.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (d.Z ↘ Spec (.of k))] [QuasiCompact (d.Z ↘ Spec (.of k))]
    [IsSeparated (d.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    [d.i.IsOver (Spec (.of k))] [d.g.IsOver (Spec (.of k))]
    (hFA : ∀ Q : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A c.i c.g).obj Q.obj))
    (hJA : ∀ Q : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor X A ((sfIntrinsicDerivedOpen A j).obj Q.obj))
    (hUA : ∀ Q : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor U A ((sfIntrinsicDerivedPullback A j).obj Q.obj))
    (hGA : ∀ Q : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A d.i d.g).obj Q.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adjA : support A c hFA ⊣ GA)
    (hFB : ∀ Q : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B c.i c.g).obj Q.obj))
    (hJB : ∀ Q : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor X B ((sfIntrinsicDerivedOpen B j).obj Q.obj))
    (hUB : ∀ Q : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor U B ((sfIntrinsicDerivedPullback B j).obj Q.obj))
    (hGB : ∀ Q : spFiniteConstructibleTorCategory U B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B d.i d.g).obj Q.obj))
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjB : support B c hFB ⊣ GB)
    (hSU : ∀ Q : spFiniteConstructibleTorCategory U A,
      spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj Q.obj))
    (hbf : ∀ Q : spFiniteConstructibleTorCategory X A,
      IsIso ((reductionDirectImageComparison φ c.i c.g).app Q.obj))
    (hbg : ∀ Q : spFiniteConstructibleTorCategory U A,
      IsIso ((reductionDirectImageComparison φ d.i d.g).app Q.obj))
    (K : spFiniteConstructibleTorCategory Y A) :
    (∀ H : spFiniteConstructibleTorCategory Y A,
      (compositeAdjunction A j c d hFA hJA hUA hGA GA adjA).counit.app H =
        (composition A j c d hFA hJA hGA).hom.app
            ((restriction A j hUA).obj (GA.obj H)) ≫
          (support A c hFA).map ((openAdjunction A j hJA hUA).counit.app (GA.obj H)) ≫
          adjA.counit.app H) ∧
    (∀ H : spFiniteConstructibleTorCategory Y B,
      (compositeAdjunction B j c d hFB hJB hUB hGB GB adjB).counit.app H =
        (composition B j c d hFB hJB hGB).hom.app
            ((restriction B j hUB).obj (GB.obj H)) ≫
          (support B c hFB).map ((openAdjunction B j hJB hUB).counit.app (GB.obj H)) ≫
          adjB.counit.app H) ∧
    ((scalarExtensionFunctor φ Y).map
        ((composition A j c d hFA hJA hGA).hom.app ((restriction A j hUA).obj (GA.obj K))).hom ≫
      (reductionDirectImageComparison φ c.i c.g).app
        ((sfIntrinsicDerivedOpen A j).obj ((restriction A j hUA).obj (GA.obj K)).obj) ≫
      (reductionCompactSupport B c.i c.g).map
        ((reductionOpenScalarIso φ j).hom.app ((restriction A j hUA).obj (GA.obj K)).obj) =
      (reductionDirectImageComparison φ d.i d.g).app ((restriction A j hUA).obj (GA.obj K)).obj ≫
        ((composition B j c d hFB hJB hGB).hom.app
          ⟨(scalarExtensionFunctor φ U).obj ((restriction A j hUA).obj (GA.obj K)).obj,
            hSU ((restriction A j hUA).obj (GA.obj K))⟩).hom) ∧
    (@inv _ _ _ _ ((reductionDirectImageComparison φ d.i d.g).app
        ((restriction A j hUA).obj (GA.obj K)).obj)
        (hbg ((restriction A j hUA).obj (GA.obj K))) ≫
      (scalarExtensionFunctor φ Y).map
        ((compositeAdjunction A j c d hFA hJA hUA hGA GA adjA).counit.app K).hom =
      ((composition B j c d hFB hJB hGB).hom.app
          ⟨(scalarExtensionFunctor φ U).obj ((restriction A j hUA).obj (GA.obj K)).obj,
            hSU ((restriction A j hUA).obj (GA.obj K))⟩).hom ≫
        (reductionCompactSupport B c.i c.g).map
          ((reductionOpenScalarIso φ j).inv.app ((restriction A j hUA).obj (GA.obj K)).obj) ≫
        (reductionCompactSupport B c.i c.g).map
          ((scalarExtensionFunctor φ X).map
            ((openAdjunction A j hJA hUA).counit.app (GA.obj K)).hom) ≫
        @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app (GA.obj K).obj)
          (hbf (GA.obj K)) ≫
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenInverseTranspose
