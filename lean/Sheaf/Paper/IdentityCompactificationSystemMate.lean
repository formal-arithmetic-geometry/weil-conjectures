/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.SfDerivedDirectImage
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.ExactDerivedAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence

/-! # Identity compactification on finite and strict-system mates

Source: blueprint prop-cohomological-finiteness, proper case (current proof Step 3;
expanded DAG proof Step 6); Deligne, Weil I (1.3), p. 274
(blueprint: lem-pod-identity-compactification-system-mate).

The identities are in the ordinary derived categories, before evaluation or total limit.
The final clauses retain the recorded quotient-transition and scalar-restriction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures
open FrobeniusExchange

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀)))
  [IsProper Y₀.hom] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The identity-open comparison on whole semilinear systems, with normalized adjunction
and both specified mate equations.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-system-mate).
Proof: every object factors uniquely through the identity open. The extension presheaf
is the original module, so its sheafification gives a natural chain isomorphism that
retains every semilinear transition (def-weil-extension-by-zero and
 def-weil-presheaf-modules-sheafification). The section-normalized unit becomes the
identity; the triangle identity does the same for the counit. Exact descent retains
these maps (def-weil-exact-derived-adjunction). On the ringed sequence site the open
mate restricts to the identity (lem-sf-open-tensor-normalization), giving the first
mate equation. Apply naturality of the simultaneous counit mate at u_N and substitute
that equation. Functoriality gives the compactification-composite equation, inside
the derived category of systems itself (lem-coef-semilinear-derived-sections and
 def-weil-frobenius-square-exchange). -/
theorem identityCompactificationSystemMate (_hl : l ≠ D.p) :
    ∃ u : systemDerivedOpen l E (𝟙 (D.geometricFiber Y₀).left) ≅ 𝟭 _,
      u = ((systemDerivedOpenAdjunction l E (𝟙 (D.geometricFiber Y₀).left)).ofNatIsoRight
        (integralComparisonSystemUnit l E (D.geometricFiber Y₀).left)).leftAdjointUniq
          Adjunction.id ∧
      (∀ N : coefficientSequenceDerived l E (D.geometricFiber Y₀).left,
        (systemDerivedOpenAdjunction l E (𝟙 (D.geometricFiber Y₀).left)).unit.app N ≫
          (integralComparisonSystemUnit l E (D.geometricFiber Y₀).left).hom.app ((systemDerivedOpen
            l E (𝟙 (D.geometricFiber Y₀).left)).obj N) ≫ u.hom.app N = 𝟙 N) ∧
      (∀ N : coefficientSequenceDerived l E (D.geometricFiber Y₀).left,
        (systemDerivedOpenAdjunction l E (𝟙 (D.geometricFiber Y₀).left)).counit.app N =
          (systemDerivedOpen l E (𝟙 (D.geometricFiber Y₀).left)).map ((integralComparisonSystemUnit
            l E (D.geometricFiber Y₀).left).hom.app N) ≫ u.hom.app N) ∧
      (∀ N : coefficientSequenceDerived l E (D.geometricFiber Y₀).left,
        (systemOpenExchange l E (𝟙 (D.geometricFiber Y₀).left) (D.geometricFrobenius Y₀).hom
          (D.geometricFrobenius Y₀).hom (IsPullback.id_vert (D.geometricFrobenius Y₀).hom)).hom.app
          N ≫ u.hom.app ((integralComparisonDerivedSequencePullback l E (D.geometricFrobenius
          Y₀).hom).obj N) =
          (integralComparisonDerivedSequencePullback l E (D.geometricFrobenius Y₀).hom).map
            (u.hom.app N)) ∧
      (∀ N : coefficientSequenceDerived l E (D.geometricFiber Y₀).left,
        (systemExchange l E (D.geometricFiber Y₀).hom (D.geometricFrobenius Y₀).hom (Spec.map
          (CommRingCat.ofHom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _).toRingHom)) (D.galoisMap_projections Y₀.hom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _ (Fintype.ofFinite D.k₀) _ _
            _)).2).app ((systemDerivedOpen l
          E (𝟙 (D.geometricFiber Y₀).left)).obj N) ≫
          (systemDirect l E (D.geometricFiber Y₀).hom).map ((systemOpenExchange l E (𝟙
            (D.geometricFiber Y₀).left) (D.geometricFrobenius Y₀).hom (D.geometricFrobenius Y₀).hom
            (IsPullback.id_vert (D.geometricFrobenius Y₀).hom)).hom.app N) ≫
          (systemDirect l E (D.geometricFiber Y₀).hom).map (u.hom.app
            ((integralComparisonDerivedSequencePullback l E (D.geometricFrobenius Y₀).hom).obj N)) =
        (integralComparisonDerivedSequencePullback l E (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _ (Fintype.ofFinite D.k₀) _ _
            _).toRingHom))).map
          ((systemDirect l E (D.geometricFiber Y₀).hom).map (u.hom.app N)) ≫ (systemExchange l E
          (D.geometricFiber Y₀).hom (D.geometricFrobenius Y₀).hom (Spec.map (CommRingCat.ofHom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _ (Fintype.ofFinite D.k₀) _ _
            _).toRingHom))
          (D.galoisMap_projections Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀
            D.k _ (Fintype.ofFinite D.k₀) _ _ _)).2).app N) := by
  sorry

/-- The same identity-open normalization for every positive finite coefficient level.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-system-mate).
Proof: lem-trf-open-square-exchange restricts the specified finite exchange to the
identity. For the identity open this is the entire map under sfIntrinsicDerivedOpenId.
The ordinary section unit and counit descend termwise to the derived adjunction.
Naturality of the finite counit mate at that comparison, followed by the open identity,
gives the displayed compactification-composite equation. The tensor coordinates use
only the published unit-preserving openSquareDerivedPullbackModel, so the equation
uses precisely constantOpenSquareExchange, not an isomorphism chosen by endpoints. -/
theorem identityCompactificationFiniteMate (_hl : l ≠ D.p) (n : ℕ) :
    (∀ N : proEtaleDerivedCategory (D.geometricFiber Y₀).left (Padic.coefficientExtensionRing l E (n
      + 1)),
      (constantOpenSquareExchange l E (n + 1) (Nat.succ_pos n) (D.geometricFrobenius Y₀).hom (𝟙
        (D.geometricFiber Y₀).left) (𝟙 (D.geometricFiber Y₀).left) (D.geometricFrobenius Y₀).hom
          (IsPullback.id_vert (D.geometricFrobenius Y₀).hom)).hom.app N ≫ (sfIntrinsicDerivedOpenId
            (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app
            ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
            (D.geometricFrobenius Y₀).hom).obj N) =
        (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
          (D.geometricFrobenius Y₀).hom).map ((sfIntrinsicDerivedOpenId
          (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app N)) ∧
    (∀ N : proEtaleDerivedCategory (D.geometricFiber Y₀).left (Padic.coefficientExtensionRing l E (n
      + 1)),
      (finiteTensorExchange (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).hom
        (D.geometricFiber Y₀).hom (D.geometricFrobenius Y₀).hom (Spec.map (CommRingCat.ofHom
        (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _ (Fintype.ofFinite D.k₀) _ _
          _).toRingHom))
        (D.galoisMap_projections Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
          _ (Fintype.ofFinite D.k₀) _ _ _)).2).app ((sfIntrinsicDerivedOpen
          (Padic.coefficientExtensionRing l E (n + 1)) (𝟙
        (D.geometricFiber Y₀).left)).obj N) ≫
        (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
          (Padic.coefficientExtensionRing l E (n + 1))).map ((constantOpenSquareExchange l E (n + 1)
          (Nat.succ_pos n) (D.geometricFrobenius Y₀).hom (𝟙 (D.geometricFiber Y₀).left) (𝟙
          (D.geometricFiber Y₀).left) (D.geometricFrobenius Y₀).hom
          (IsPullback.id_vert (D.geometricFrobenius Y₀).hom)).hom.app N) ≫
        (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
          (Padic.coefficientExtensionRing l E (n + 1))).map ((sfIntrinsicDerivedOpenId
          (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app
          ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
          (D.geometricFrobenius Y₀).hom).obj N)) =
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) (Spec.map
        (CommRingCat.ofHom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
          (Fintype.ofFinite D.k₀) _ _ _).toRingHom))).map ((proEtaleConstantDerivedDirectImage
          (D.geometricFiber Y₀).hom
        (Padic.coefficientExtensionRing l E (n + 1))).map ((sfIntrinsicDerivedOpenId
        (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app N)) ≫
        (finiteTensorExchange (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).hom
        (D.geometricFiber Y₀).hom (D.geometricFrobenius Y₀).hom (Spec.map (CommRingCat.ofHom
        (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _ (Fintype.ofFinite D.k₀) _ _
          _).toRingHom))
        (D.galoisMap_projections Y₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
          _ (Fintype.ofFinite D.k₀) _ _ _)).2).app N) := by
  sorry

/-- The identity-open comparisons identify the full quotient-transition towers.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-system-mate).
Proof: put h_m = Ra_*(u_m). The presheaf-identity scalar comparison e satisfies
Res(u_B) e = u_A Res (lem-sf-open-extension-scalar-restriction-coherence).
Naturality of the normalized direct-image restriction comparison d gives
Res(h_B) c = d (h_A Res), for c = d_J Ra_*(e)
(lem-sf-compact-support-restriction-of-scalars and
 lem-weil-proetale-direct-image-restriction-of-scalars). Apply this square to the
quotient map M_(m+1) to Res(M_m). Naturality of h_(m+1), followed by the canonical
composite-restriction identification, gives exactly the transition equation below.
These are the recorded towers of def-weil-integral-rational-qbar-compact-support
and def-weil-derived-direct-image, not towers with freely chosen arrows.
Before any level evaluation, whisker the canonical system u with system direct
image and exact restriction to completed-coefficient strict towers. This constructs
v in the ordinary derived category of actual strict towers. The published normalized
system-direct-image and restricted-evaluation comparisons identify its evaluations
with the displayed h_n; the scalar square identifies their quotient transitions. -/
theorem identityCompactificationTowers (_hl : l ≠ D.p)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    ∃ v : (coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj ((systemDirect l E
      (D.geometricFiber Y₀).hom).obj ((systemDerivedOpen l E (𝟙 (D.geometricFiber Y₀).left)).obj
      ((reduction l E (D.geometricFiber Y₀).left).obj M.obj))) ≅
        (coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj ((systemDirect l E
          (D.geometricFiber Y₀).hom).obj ((reduction l E (D.geometricFiber Y₀).left).obj M.obj)),
      v = (coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).mapIso ((systemDirect l E
        (D.geometricFiber Y₀).hom).mapIso ((((systemDerivedOpenAdjunction l E (𝟙 (D.geometricFiber
        Y₀).left)).ofNatIsoRight
          (integralComparisonSystemUnit l E (D.geometricFiber Y₀).left)).leftAdjointUniq
            Adjunction.id).app ((reduction l E (D.geometricFiber Y₀).left).obj M.obj))) ∧
    ∃ h : ∀ n : ℕ, sfCompactSupportTerm l E (@Compactification.ofIsProper _ _ (D.geometricFiber
      Y₀).hom
        (inferInstanceAs (IsProper (pullback.snd Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))))
      M.obj n ≅
        sfDirectImageTerm l E (D.geometricFiber Y₀).hom M.obj n,
      (∀ n : ℕ, (h n).hom =
        (scalarReductionDerivedRestriction l E (Spec (.of D.k)) n).map
          ((proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
            (Padic.coefficientExtensionRing l E (n + 1))).map ((sfIntrinsicDerivedOpenId
            (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app
            ((scalarReductionDerivedExtension l E (D.geometricFiber Y₀).left n).obj M.obj)))) ∧
      (∀ n : ℕ, sfCompactSupportTransition l E (@Compactification.ofIsProper _ _ (D.geometricFiber
        Y₀).hom
        (inferInstanceAs (IsProper (pullback.snd Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) M.obj n ≫
          (h n).hom =
        (h (n + 1)).hom ≫ sfDirectImageTransition l E (D.geometricFiber Y₀).hom M.obj n) := by
  sorry

/-- Unit and counit for identity open extension at a finite level are identities
under the canonical identity restriction and open comparison.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-system-mate).
Proof: the ordinary unit sends a section to the same section in the sheafified
identity-extension presheaf. Its identification with the original sheaf makes
this the identity. The triangle identity gives the counit normalization. Exact
derived adjunction localizes these very two maps, so the identities descend. -/
theorem identityCompactificationFiniteAdjunction (_hl : l ≠ D.p) (n : ℕ) :
    (∀ N : proEtaleDerivedCategory (D.geometricFiber Y₀).left (Padic.coefficientExtensionRing l E (n
      + 1)),
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) (𝟙 (D.geometricFiber
        Y₀).left))).unit.app N ≫ (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing l E
        (n + 1)) (D.geometricFiber Y₀).left).hom.app ((sfIntrinsicDerivedOpen
        (Padic.coefficientExtensionRing l E (n + 1)) (𝟙 (D.geometricFiber Y₀).left)).obj N) ≫
        (sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber
          Y₀).left).hom.app N = 𝟙 N) ∧
    (∀ N : proEtaleDerivedCategory (D.geometricFiber Y₀).left (Padic.coefficientExtensionRing l E (n
      + 1)),
      (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) (𝟙 (D.geometricFiber
        Y₀).left))).counit.app N = (sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n +
        1)) (𝟙 (D.geometricFiber Y₀).left)).map ((sfIntrinsicDerivedPullbackId
        (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber Y₀).left).hom.app N) ≫
        (sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber
        Y₀).left).hom.app N) := by
  sorry

/-- Identity-open cancellation retains the specified finite restriction-of-scalars
comparison, including every quotient coefficient map of the strict tower.
Source: blueprint prop-cohomological-finiteness, proper case, expanded Step 6
(blueprint: lem-pod-identity-compactification-system-mate).
Proof: the sheafification comparison commutes with every semilinear module map.
In particular Res(u_B) e = u_A Res for the presheaf-identity comparison e
(lem-sf-open-extension-scalar-restriction-coherence). Apply Ra_* and then use
naturality of the normalized direct-image comparison d at u_B. Since the
specified compact-support comparison is d_J composed with Ra_*(e), this gives
the displayed square. This is the scalar-comparison square used in the final
quotient-transition argument, before restricting to completed coefficients. -/
theorem identityCompactificationScalarRestriction (_hl : l ≠ D.p) (n m : ℕ)
    (φ : (Padic.coefficientExtensionRing l E (n + 1)) →+* (Padic.coefficientExtensionRing l E (m +
      1))) (N : proEtaleDerivedCategory (D.geometricFiber Y₀).left (Padic.coefficientExtensionRing l
      E (m + 1))) :
    (sfCompactSupportRestriction (@Compactification.ofIsProper _ _ (D.geometricFiber Y₀).hom
        (inferInstanceAs (IsProper (pullback.snd Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))) φ).hom.app
      N ≫
      (proEtaleCoefficientRestrictScalars (Spec (.of D.k)) φ).mapDerivedCategory.map
        ((proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
          (Padic.coefficientExtensionRing l E (m + 1))).map
          ((sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (m + 1)) (D.geometricFiber
            Y₀).left).hom.app N)) =
    (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom (Padic.coefficientExtensionRing l
      E (n + 1))).map
        ((sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (n + 1)) (D.geometricFiber
          Y₀).left).hom.app ((proEtaleCoefficientRestrictScalars (D.geometricFiber Y₀).left
          φ).mapDerivedCategory.obj N)) ≫
      (sfDerivedImageRestriction (D.geometricFiber Y₀).hom φ).hom.app N := by
  sorry

end WeilConjectures
