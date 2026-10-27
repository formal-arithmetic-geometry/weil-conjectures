/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.FiniteModelStratumFiltration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.CoefficientHeartLocallyClosedExtension
import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Normalized lisse quotient filtrations for all-continuous coefficients

Source: blueprint main-20261015, sk-lem-coefficient-heart, proof (3);
Stacks Tags 09Y5, 09AH and 0152
(blueprint: lem-sfb-continuous-qbar-normalized-sheaf-filtration).

The predicate packages the witnesses of this assertion. Its quotient equations use
actual cokernel projections, localization units and extension-by-zero counits.
Its normalization square expresses identity on the stratum without choosing
an unspecified identification of the restricted quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Witnesses of the finite open-support filtration, including the canonical quotient
maps and the normalized comparison for every open-then-closed factorization.
The `Fin r` short exact sequences give exactly r distinguished-triangle extensions
from the initial zero object to the final object, up to the displayed endpoint isomorphism.
Source: blueprint sk-lem-coefficient-heart, proof (3), Stacks Tags 09Y5, 09AH and 0152
(blueprint: lem-sfb-continuous-qbar-normalized-sheaf-filtration). -/
def HasNormalizedLisseSheafFiltration (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens),
    Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last r) = ⊤ ∧
    ∃ (S : Fin r → Scheme.{u}) (t : ∀ k : Fin r, S k ⟶ (V k.succ).toScheme),
      (∀ k, IsClosedImmersion (t k)) ∧ (∀ k, IsReduced (S k)) ∧
      (∀ k, Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
      (∀ k, IsLisseCoefficientModule Λ
        ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj M))) ∧
      (∀ k, QuasiCompact (V k).ι) ∧
      (∀ k : Fin r, QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι) ∧
      (∀ k, Mono ((openFiltrationCounit Λ (V k)).app M)) ∧
      IsZero ((openFiltrationPiece Λ (V 0)).obj M) ∧
      IsIso ((openFiltrationCounit Λ (V (Fin.last r))).app M) ∧
      ∃ d : ∀ k : Fin r,
        (openFiltrationPiece Λ (V k.castSucc)).obj M ⟶
          (openFiltrationPiece Λ (V k.succ)).obj M,
        (∀ k, d k ≫ (openFiltrationCounit Λ (V k.succ)).app M =
          (openFiltrationCounit Λ (V k.castSucc)).app M) ∧
        (∀ k, Mono (d k)) ∧
        ∃ q : ∀ k, cokernel (d k) ≅ (openFiltrationStratum Λ (V k.succ) (t k)).obj M,
          (∀ k, cokernel.π (d k) ≫ (q k).hom =
            (openImmersionLowerShriek Λ (V k.succ).ι).map
              ((upperStarLowerStarAdjunction Λ (t k)).unit.app
                ((upperStar Λ (V k.succ).ι).obj M))) ∧
          (∀ k, IsImmersion (t k ≫ (V k.succ).ι)) ∧
          (∀ k, QuasiCompact (t k ≫ (V k.succ).ι)) ∧
          (∀ k, Topology.IsConstructible (Set.range (t k ≫ (V k.succ).ι))) ∧
          (∀ k, ∃ (Z : Scheme.{u}) (j : S k ⟶ Z) (i : Z ⟶ X),
            IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = t k ≫ (V k.succ).ι) ∧
          ∃ b : ∀ k,
            (upperStar Λ (t k ≫ (V k.succ).ι)).obj (cokernel (d k)) ≅
              (upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj M),
            (∀ k, (upperStar Λ (t k ≫ (V k.succ).ι)).map (cokernel.π (d k)) ≫
                (b k).hom =
              (upperStar Λ (t k ≫ (V k.succ).ι)).map
                  ((openFiltrationCounit Λ (V k.succ)).app M) ≫
                (upperStarComp Λ (t k) (V k.succ).ι).hom.app M) ∧
            ∀ (k : Fin r) (Z : Scheme.{u}) (j : S k ⟶ Z) (i : Z ⟶ X)
                [IsOpenImmersion j] [IsClosedImmersion i]
                (h : j ≫ i = t k ≫ (V k.succ).ι),
              QuasiCompact j ∧ ∃ e : cokernel (d k) ≅
                (lowerStar Λ i).obj ((openImmersionLowerShriek Λ j).obj
                  ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj M))),
                ((upperStar Λ (t k ≫ (V k.succ).ι)).map e.hom ≫
                    (upperStarCongr Λ h.symm).hom.app _ ≫
                    (upperStarComp Λ j i).hom.app _ ≫
                    (upperStar Λ j).map
                      ((upperStarLowerStarAdjunction Λ i).counit.app _)) =
                  (b k).hom ≫
                    (openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app _ ∧
                ∃ hz : d k ≫ (cokernel.π (d k) ≫ e.hom) = 0,
                  ∃ hs : (ShortComplex.mk (d k) (cokernel.π (d k) ≫ e.hom) hz).ShortExact,
                    hs.singleTriangle ∈ distTriang _

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- Every constructible module over C(-,Ω) has a finite open-support filtration with
lisse reduced stratum restrictions, normalized immersion extensions and ordinary
unbounded derived short-exact-sequence triangles. The zero module also allows the
empty construction, independently of any stratification of a nonempty X.
Source: blueprint sk-lem-coefficient-heart, proof (3); Stacks Tags 09Y5, 09AH and 0152
(blueprint: lem-sfb-continuous-qbar-normalized-sheaf-filtration).

Proof plan:
1. `lem-sfb-alpha-iso` identifies inverse-image coefficients with the specified R_T.
The internal/sectionwise module equivalence and the ringed-site abelian theorem
identify the actual module categories and their localization maps.
2. `lem-sfb-coefficient-heart-locally-closed-extension` gives Noetherian spaces.
Apply `lem-sfb-finite-model-stratum-filtration` to obtain the finite open chain,
reduced complements, monomorphic counits and compatible inclusions, with zero and
whole endpoints. All opens and their successive complements are quasi-compact.
3. Evaluation on the point identifies Λ(*) with Ω. The field clause of
`lem-sfb-scalar-finite-free-resolutions` makes every finite scalar model finite free.
Scalar extension of a basis and its inverse yields precisely the recorded lisse condition.
4. For each successor, identify the preceding piece with v_!w_!w^*M using
`lem-sfb-locally-closed-module-extension-coherence`. Exact v_! and the unit in
`lem-weil-pbc-proetale-ringed-open-closed` identify the quotient with v_!t_*L.
Restriction gives L, since t^*w_! vanishes and the open unit and closed counit are
invertible. The same coherence comparisons give i_*j_!L for every factorization,
with identity restriction. Noetherian immersion geometry gives all the stated
quasi-compactness and constructibility assertions, and an open-then-closed factorization.
5. `lem-sf-derived-ses-triangle` gives the distinguished triangle of each short exact
sequence. Transport the third vertex by the normalized quotient isomorphism; TR1
keeps it distinguished in the inherited ordinary unbounded derived category.
6. Induct through the r successive triangles starting at zero. The counit at the
last open identifies the result with M[0]. If M is zero, M[0] itself is zero, so the
empty construction is allowed; the empty scheme also allows r=0. -/
theorem exists_continuousQbar_normalizedLisseSheafFiltration
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) X))
    (hM : IsConstantModelConstructible (Profinite.continuousCoefficientRingObj Ω) X M) :
    CondensedRing.HasNormalizedLisseSheafFiltration
      (Profinite.continuousCoefficientRingObj Ω) X M ∧
      (IsZero M → IsZero ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale
