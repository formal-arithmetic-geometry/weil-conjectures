/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.CoefficientHeartLisseRestriction
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Relative-line stratification with condensed coefficients

Source: latest blueprint, sec-deligne-laumon-general/sk-prop-wgen-relative-line,
thm-zl-relative-line-stratification.md and its proof, paragraphs 1--4
(blueprint: thm-zl-relative-line-stratification).

All strata are schemes over the original finite field through their immersions.
The geometric line is the geometric fibre of the model line, canonically the line
on the geometric base. The final equality specifies the restricted Weil structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedRelativeLine

/-- The relative affine line, with its composite structure map to the finite field.
Source: latest blueprint, thm-zl-relative-line-stratification.md, opening sentence
(blueprint: thm-zl-relative-line-stratification). -/
abbrev lineModel (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) :
    Over (Spec (.of D.k₀)) :=
  Over.mk ((AffineSpace (ULift (Fin 1)) Y₀.left ↘ Y₀.left) ≫ Y₀.hom)

/-- The model line has finite type over the original finite-field base, by composition
of the existing affine-space and base instances.
Source: latest blueprint, thm-zl-relative-line-stratification.md, opening sentence
(blueprint: thm-zl-relative-line-stratification). -/
instance lineModel_locallyOfFiniteType (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] :
    LocallyOfFiniteType (lineModel D Y₀).hom :=
  inferInstanceAs (LocallyOfFiniteType
    ((AffineSpace (ULift (Fin 1)) Y₀.left ↘ Y₀.left) ≫ Y₀.hom))

/-- Quasi-compactness of the model line uses the existing affine projection and composition.
Source: latest blueprint, thm-zl-relative-line-stratification.md, opening sentence
(blueprint: thm-zl-relative-line-stratification). -/
instance lineModel_quasiCompact (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [QuasiCompact Y₀.hom] :
    QuasiCompact (lineModel D Y₀).hom :=
  inferInstanceAs (QuasiCompact
    ((AffineSpace (ULift (Fin 1)) Y₀.left ↘ Y₀.left) ≫ Y₀.hom))

/-- Base change of the actual model immersion, with its two canonical projections.
Source: latest blueprint, thm-zl-relative-line-stratification.md, model-defined strata
(blueprint: thm-zl-relative-line-stratification). -/
abbrev geometricInclusion (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {S₀ : Scheme.{u}} (j₀ : S₀ ⟶ X₀.left) :
    pullback (j₀ ≫ X₀.hom) (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (Over.homMk j₀ rfl : Over.mk (j₀ ≫ X₀.hom) ⟶ X₀)).left

/-- The recorded Galois base-change map specialized to geometric Frobenius on a stratum.
No finite-type instance on the stratum is needed to construct this map.
Source: latest blueprint, thm-zl-relative-line-stratification.proof.md, final paragraph
(blueprint: thm-zl-relative-line-stratification). -/
abbrev stratumFrobenius (D : FiniteFieldDatum.{u}) {S₀ : Scheme.{u}}
    (a₀ : S₀ ⟶ Spec (.of D.k₀)) :
    pullback a₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      pullback a₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  D.galoisMap a₀ (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
    _ (Fintype.ofFinite D.k₀) _ _ _)

/-- Finite reduced source and target stratifications adapted to a constructible Weil module.
The smooth alternative requires every geometric fibre to be affine of dimension one.
The isomorphisms `θS` are precisely the restrictions of `θ`, using canonical composition
comparisons and the Frobenius square, rather than independently chosen Weil structures.

Source: latest blueprint, thm-zl-relative-line-stratification.md and its proof,
paragraphs 1--4 (blueprint: thm-zl-relative-line-stratification).

Proof plan:
1. Pass to reduced strata using invariance of the pro-etale topos under reduction;
   the pulled-back ring, modules, finite constant models and free trivializations transport.
2. Induct on closed subsets of the Noetherian base. The empty base has empty partitions.
   Choose disjoint integral affine opens through its finitely many generic points.
3. On each affine base Spec B, choose a model-defined dense lisse open in Spec B[T].
   A nonzero polynomial in its boundary ideal becomes monic after inverting its leading
   coefficient. Its powers below the degree generate the boundary algebra, making it finite.
   Degree zero gives the zero algebra, and an empty boundary needs no localization.
4. The open complement is smooth by restriction of the relative line. Its geometric fibres
   are lines minus finitely many points: principal affine opens of dimension one.
5. Stratify the finite boundary by lisse reduced strata using closed-subset induction,
   then refine to affine pieces. Their maps to the affine base are separated, of finite
   type and have finite fibres, hence are quasi-finite in the Stacks sense.
6. Apply the outer induction to the remaining proper reduced closed subset of the base.
   Combine the finitely many partitions. All immersions are over the finite-field model,
   so their geometric base changes commute with geometric Frobenius. Pullback composition
   then restricts the original Weil isomorphism by the displayed formula.
-/
theorem exists_stratifications
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (M : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber (lineModel D Y₀)).left)
      Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (D.geometricFiber (lineModel D Y₀)).left))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber (lineModel D Y₀)).left M)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFrobenius (lineModel D Y₀)).hom).obj M ≅ M) :
    ∃ (S : Scheme.FiniteLocallyClosedStratification (lineModel D Y₀).left)
      (T : Scheme.FiniteLocallyClosedStratification Y₀.left)
      (target : Fin S.n → Fin T.n)
      (f : ∀ i : Fin S.n, S.domain i ⟶ T.domain (target i)),
      (∀ i : Fin S.n, IsReduced (S.domain i)) ∧
      (∀ j : Fin T.n, IsReduced (T.domain j)) ∧
      (∀ i : Fin S.n, f i ≫ T.immersion (target i) =
        S.immersion i ≫ (AffineSpace (ULift (Fin 1)) Y₀.left ↘ Y₀.left)) ∧
      (∀ i : Fin S.n,
        (IsSeparated (f i) ∧ Scheme.Hom.IsQuasiFinite (f i)) ∨
        (Smooth (f i) ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T.domain (target i)),
          IsAffine (pullback (f i) y) ∧
            topologicalKrullDim (pullback (f i) y : Scheme.{u}) = (1 : WithBot ℕ∞))) ∧
      (∀ i : Fin S.n, IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (geometricInclusion D (lineModel D Y₀) (S.immersion i))).obj M)) ∧
      ∃ h : ∀ i : Fin S.n,
          stratumFrobenius D (S.immersion i ≫ (lineModel D Y₀).hom) ≫
              geometricInclusion D (lineModel D Y₀) (S.immersion i) =
            geometricInclusion D (lineModel D Y₀) (S.immersion i) ≫
              (D.geometricFrobenius (lineModel D Y₀)).hom,
        ∃ θS : ∀ i : Fin S.n,
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              (stratumFrobenius D (S.immersion i ≫ (lineModel D Y₀).hom))).obj
                ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                  (geometricInclusion D (lineModel D Y₀) (S.immersion i))).obj M) ≅
              (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                (geometricInclusion D (lineModel D Y₀) (S.immersion i))).obj M,
          ∀ i : Fin S.n, θS i =
            ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ)
              (stratumFrobenius D (S.immersion i ≫ (lineModel D Y₀).hom))
              (geometricInclusion D (lineModel D Y₀) (S.immersion i))).app M).symm ≪≫
            eqToIso (congrArg (fun g ↦
              (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj M) (h i)) ≪≫
            (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ)
              (geometricInclusion D (lineModel D Y₀) (S.immersion i))
              (D.geometricFrobenius (lineModel D Y₀)).hom).app M ≪≫
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              (geometricInclusion D (lineModel D Y₀) (S.immersion i))).mapIso θ := by
  sorry

end WeilConjectures.CondensedRelativeLine
