/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
public import Sheaf.Paper.PurityConventions
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
public import Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

import Sheaf.Paper.AffineDiagonalTransposePower
import Sheaf.Paper.AffineDiagonalTraceRestriction
import Sheaf.Paper.AffineDiagonalDncNormalization
import Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration
import Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose

/-! # Affine diagonal integration orientation

Source: Agreement on the model
(blueprint: lem-pur-affine-diagonal-integration-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  Etale.FiniteSmoothPurity.ReesConeNormalized
  Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

/-- Translation identifies both actual integration and its exceptional transpose,
with all compact-support, Tate, and dualizing base-change identifications inserted.
Source: Agreement on the model, translation clause
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: apply lem-pur-affine-translation-trace to the tautological coordinate vector
on X. Its action is compact-support exchange followed by normalized Tate pullback,
so composing with the coordinate comparison gives the first equation. Naturality
of the exceptional Hom bijection (lem-pur-trace-transpose-base-change) gives the
second, with the counit-transposed dualizing base-change mate used in the definition.
At d=0 this is the identity action; the empty base has the same unique arrows. -/
theorem affineDiagonalIntegration_translation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
    let p := affineDiagonalProjection Y d
    let aX := p ≫ aY
    let p₁ := pullback.fst p p
    letI := affineDiagonalProjection_smooth Y d
    letI := SmoothOfRelativeDimension.smooth d p
    letI := Dnc.compactifiable P p₁ aX
    letI := (affineDiagonalProductCoordinates_spec Y d).1
    letI := (affineDiagonalTranslatedCoordinates_spec Y d).1
    let e := asIso (affineDiagonalProductCoordinates Y d)
    let h := asIso (affineDiagonalTranslatedCoordinates Y d)
    let he := (affineDiagonalProductCoordinates_spec Y d).2
    let hh := (affineDiagonalTranslatedCoordinates_spec Y d).2.1
    P.affineDiagonalPresentedIntegration d p₁ aX r hA e he =
        P.affineDiagonalPresentedIntegration d p₁ aX r hA h hh ∧
      P.affineDiagonalPresentedTranspose d p₁ aX r hA e he =
        P.affineDiagonalPresentedTranspose d p₁ aX r hA h hh := by
  exact ⟨affineDiagonalIntegration_translation_integration P Y aY d r hA,
    affineDiagonalIntegration_translation_transpose P Y aY d r hA⟩

/-- Every larger annihilator gives the same integration and transpose under the
root-power comparison, specified on all pure tensors. A common larger exponent
therefore compares any two annihilators. The statement applies to each of p, p1
and the actual normal projection, in their displayed coordinate presentations.
Source: Agreement on the model, independence of an annihilating exponent
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: the power map on roots is fixed by its monic inclusion in G_m. After
extension of scalars to A it is invertible because the smaller power annihilates A;
etaleFiniteTwistPullback supplies the comparison with the stated generator formula.
The supported Kummer boundary commutes with this power map. Thus the projective
trace and its open counit restriction commute with it. Tensor in coordinate order
and paste compact-support composition comparisons to obtain the integration equation.
Apply the exceptional Hom bijection for the transpose equation, with the same
Tate restriction and dualizing mate. For two unordered exponents use their maximum.
At rank zero the coefficient comparison and the identity trace are identities. -/
theorem affineDiagonalIntegration_exponent (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r r' : ℕ) (_hrr : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
    (c : U ≅ affineTraceTower B d) (hc : c.hom ≫ affineTraceProjection B d = f) :
    ∃ (q : U.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1)) ⟶
          U.rootsOfUnitySheaf (P.coefficients.l ^ (r + 1)))
      (e : Scheme.finiteEtaleTateLine U (P.coefficients.l ^ (r' + 1)) P.Coefficient hA' ≅
        Scheme.finiteEtaleTateLine U (P.coefficients.l ^ (r + 1)) P.Coefficient hA),
      q ≫ kernel.ι ((P.coefficients.l ^ (r + 1)) • 𝟙 U.gmSheaf) =
        (P.coefficients.l ^ (r' + 1) / P.coefficients.l ^ (r + 1)) •
          kernel.ι ((P.coefficients.l ^ (r' + 1)) • 𝟙 U.gmSheaf) ∧
      (∀ (V : U.Etaleᵒᵖ) (a : P.Coefficient)
        (z : (U.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1))).obj.obj V),
        e.hom.hom.app V (Scheme.finiteEtaleTateOneGenerator P.Coefficient
          (P.coefficients.l ^ (r' + 1)) U hA' V a z) =
        Scheme.finiteEtaleTateOneGenerator P.Coefficient
          (P.coefficients.l ^ (r + 1)) U hA V a (q.hom.app V z)) ∧
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).map
          (P.affineDiagonalPowerComparison U r r' hA hA' e d).hom ≫
        P.affineDiagonalPresentedIntegration d f aB r hA c hc =
          P.affineDiagonalPresentedIntegration d f aB r' hA' c hc ∧
      (P.affineDiagonalPowerComparison U r r' hA hA' e d).hom ≫
        P.affineDiagonalPresentedTranspose d f aB r hA c hc =
          P.affineDiagonalPresentedTranspose d f aB r' hA' c hc := by
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpower⟩ :=
    (Scheme.finiteEtaleTwistPullbackData P.Coefficient
      (P.coefficients.l ^ (r + 1)) hN hA).laws
  obtain ⟨root, line, hroot, hline, _⟩ := hpower
      (P.coefficients.l ^ (r' + 1))
      (pow_pos P.coefficients.prime.out.pos (r' + 1))
      (pow_dvd_pow _ (Nat.add_le_add_right _hrr 1)) U
      (WeilConjectures.PurityConventions.coefficientPower_isUnit P U (f ≫ aB) r')
  let e := line 1
  have htranspose := P.affineDiagonalTranspose_powerCompatible d f aB r r' _hrr
    hA hA' c hc root e hroot hline
  refine ⟨root, e, hroot, hline, ?_, htranspose⟩
  dsimp only [affineDiagonalPresentedIntegration]
  rw [← Adjunction.homEquiv_naturality_left_symm, htranspose]

/-- Rank zero is the identity adjunction, with no nonempty-base assumption.
Together with the identity zero-coordinate substitution and the normalized
standard-pair DNC comparison this makes all four displayed equations identities.
Source: Agreement on the model, rank-zero and empty-base clause
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof: the zero-fold tower is Y, its projection is identity, its ordered right
and left functors and counit are identities. The compact-support comparison is
the identity-functor comparison. By uniqueness of right adjoints its exceptional
transpose is inverse to dualizingComplexIdIso. The coordinate and Rees lists are
empty; the DNC standard-family normalization is identity. All constructions and
adjunction equations remain valid on the empty scheme. -/
theorem affineDiagonalIntegration_zero (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
    P.affineDiagonalPresentedIntegration 0 (𝟙 Y) aY r hA (Iso.refl Y) (Category.id_comp _) =
        (Etale.rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} P.Coefficient) Y).hom.app _ ∧
      P.affineDiagonalPresentedTranspose 0 (𝟙 Y) aY r hA (Iso.refl Y) (Category.id_comp _) ≫
        (Etale.dualizingComplexIdIso (ModuleCat.{u + 1} P.Coefficient) Y).hom = 𝟙 _ := by
  sorry

/-- All four equations between the specified derived maps, with their canonical
Tate and site comparisons. The existential isomorphisms have their hom maps fixed
by the actual integration transpose; therefore they introduce no orientation choice.
The normalized Rees presentation q is universally quantified, rather than chosen.
Source: Agreement on the model, four displayed equations
(blueprint: lem-pur-affine-diagonal-integration-orientation). -/
def AffineDiagonalIntegrationConclusion (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) : Prop :=
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let W := pullback p p
  let p₁ := pullback.fst p p
  let p₂ := pullback.snd p p
  let s := pullback.diagonal p
  let aX := p ≫ aY
  letI := affineDiagonalProjection_smooth Y d
  letI := SmoothOfRelativeDimension.smooth d p
  letI := Dnc.compactifiable P p aY
  letI := Dnc.compactifiable P p₁ aX
  letI := (P.comparedDiagonalBaseChange d p aX aY rfl).2.2.2.1
  let L := Etale.affineLinearBaseCoefficient P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
  let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let C := fun B : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let B := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback p p).flip
  let α := Dnc.sourceComparison P d p₁ aX s ≪≫
    (C X).mapIso (P.diagonalComparedRestriction p (asIso B))
  let δ := (Dnc.existsUnique_dncInvariance P d p₁ aX s (pullback.diagonal_fst p)).exists.choose
  ∀ (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
    (hq : Etale.FiniteSmoothPurity.ReesConeNormalized s q),
    let πN := Scheme.Hom.normalConeProj p₁ s
    let z := s.normalConeZeroSection
    letI := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
    letI := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
    letI := (affineDiagonalNormalCoordinates_spec Y d q hq).1
    letI := (affineDiagonalProductCoordinates_spec Y d).1
    ∃ (I : L X d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p)
      (J : L W d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p₁)
      (Q : L s.ker.normalCone d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) πN),
      I.hom = P.affineDiagonalPresentedTranspose d p aY r hA (Iso.refl X)
        (Category.id_comp p) ∧
      J.hom = P.affineDiagonalPresentedTranspose d p₁ aX r hA
        (asIso (affineDiagonalProductCoordinates Y d))
        (affineDiagonalProductCoordinates_spec Y d).2 ∧
      Q.hom = P.affineDiagonalPresentedTranspose d πN aX r hA
        (asIso (affineDiagonalNormalCoordinates Y d q))
        (affineDiagonalNormalCoordinates_spec Y d q hq).2 ∧
      (C W).map J.hom = (C W).map
        ((P.affineDiagonalTateRestriction r hA p₂ aX d).inv ≫
          (F p₂).map I.hom ≫ B) ∧
      (let T := (C X).mapIso
          ((P.affineDiagonalTateRestriction r hA s (p₁ ≫ aX) d).symm ≪≫
            (F s).mapIso J) ≪≫ (Dnc.sourceComparison P d p₁ aX s).symm
       let β := Dnc.normalComparison P d p₁ aX s (pullback.diagonal_fst p) ≪≫
          (C X).mapIso ((F z).mapIso Q.symm ≪≫
            P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d)
       T.hom ≫ α.hom = (C X).map I.hom ∧
         δ.hom ≫ β.hom = T.inv ∧
         α.inv ≫ δ.hom ≫ β.hom = (C X).map I.inv)

private lemma inverse_composite {C : Type*} [Category C] {A B D : C}
    (T : A ≅ B) (α : B ≅ D) (I : A ≅ D)
    (h : T.hom ≫ α.hom = I.hom) : α.inv ≫ T.inv = I.inv := by
  exact congrArg Iso.inv (show T ≪≫ α = I from Iso.ext h)

private lemma orientation_composite {C : Type*} [Category C] {A B D E : C}
    (T : A ≅ B) (α : B ≅ D) (I : A ≅ D) (δ : B ≅ E) (β : E ≅ A)
    (htrace : T.hom ≫ α.hom = I.hom) (hD : δ.hom ≫ β.hom = T.inv) :
    α.inv ≫ δ.hom ≫ β.hom = I.inv := by
  rw [hD]
  exact inverse_composite T α I htrace

/-- The diagonal/DNC orientation is inverse to integration-transposed purity.
The setting includes every positive coefficient level n and all finite extensions E.
Quantification over every annihilating ell-power makes the assertion independent of
that presentation. The coordinate tower has X_0=Y and p_0=id, even for empty Y.
Source: main-20261015, projection-purity-agreement proof, Agreement on the model
(blueprint: lem-pur-affine-diagonal-integration-orientation).
Proof:
1. All affine bundles and self-products are separated finite type over k and
Noetherian; their projections are smooth of relative dimension d. The shifted
Tate lines have bounded etale witnesses. Vector-bundle purity and its specified
site comparison make the actual integration transposes I, J and Q invertible.
2. The unit equation of projection-formula coefficient coherence cancels both
unitors in (1 tensor t) Pi. Thus the maps used here are precisely the exceptional
transposes of t, not arbitrary dualizing isomorphisms.
3. Apply affine-space trace base change to b=p. Transport its equation through
the proper/open site comparisons and thm-cbc-finite-level-proetale. Naturality
of the adjunction Hom bijection, lem-pur-trace-transpose-base-change, gives
J=B Lp2* I, with exactly the counit-transposed B displayed here.
4. Pull this equation along the diagonal. Alpha is the pullback of inverse B
followed by the section-composition comparison. Cancel B with its inverse to
give alpha T=I (lem-pur-diagonal-base-change).
5. In polynomial charts put u=y-x. The inverse substitution is y=x+u, and gr_(u)
is polynomial in the degree-one classes v=[u]. The constructed normal map uses
these homogeneous classes, and the Rees comparison fixes u/t. Hence the DNC
coordinates are u=t v, with the prescribed order and sign.
6. The universal translation trace of lem-pur-affine-translation-trace, at the
tautological section over X, preserves the actual integration. Taking its
exceptional transpose identifies J with the standard-bundle transpose under
(x,y)->(x,y-x), with the canonical exceptional base-change mate.
7. The standard-pair DNC family is constant in those coordinates, by
lem-pur-dnc-section-geometry(4). The normalization in thm-pur-dnc-invariance
makes delta identity between the two copies. Beta is zero restriction of Q^-1,
so beta delta=T^-1 as an equality of the specified derived arrows.
8. Compose with alpha^-1 and use Step 4 to obtain beta delta alpha^-1=I^-1.
The site/root comparisons commute with annihilator transitions, so the same
identities hold for every annihilator at every n>=1. At d=0 all traces are the
identity adjunction and the normalized DNC map is identity. On the empty base
the same displayed maps are the unique maps, and all equations remain valid. -/
theorem affineDiagonalIntegrationOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
    P.AffineDiagonalIntegrationConclusion Y aY d r hA := by
  intro q hq
  obtain ⟨I, J, Q, hI, hJ, hQ, hBC, htrace⟩ :=
    P.affineDiagonalTraceRestriction Y aY d r hA q hq
  have hD := P.affineDiagonalDncNormalization Y aY d r hA q hq J Q hJ hQ
  refine ⟨I, J, Q, hI, hJ, hQ, hBC, htrace, hD, ?_⟩
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let aX := p ≫ aY
  let p₁ := pullback.fst p p
  let s := pullback.diagonal p
  let := affineDiagonalProjection_smooth Y d
  let := SmoothOfRelativeDimension.smooth d p
  let := Dnc.compactifiable P p aY
  let := Dnc.compactifiable P p₁ aX
  let := (P.comparedDiagonalBaseChange d p aX aY rfl).2.2.2.1
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let B := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback p p).flip
  let α := Dnc.sourceComparison P d p₁ aX s ≪≫
    C.mapIso (P.diagonalComparedRestriction p (asIso B))
  exact orientation_composite _ α (C.mapIso I) _ _ htrace hD

end WeilConjectures.PurityFiniteSetting
