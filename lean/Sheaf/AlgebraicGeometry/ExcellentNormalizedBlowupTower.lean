/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.StructureSheaf
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import Sheaf.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition

/-!
# Geometry of finite normalized point-blowup towers

Source: Stacks Project, Resolution of Surfaces, Tag 0BFT (resolve-lemma-Nagata-normalized-blowup);
Morphisms Tags 035Q, 035S, 0B3I, 0C4P and 02JX; Divisors Tags 02ND and 02NS;
ILO Exposé XVII, §3.4.1 (blueprint: lem-per-excellent-normalized-blowup-tower).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A supplied finite tower of point blowups followed by function-field normalizations has
integral, normal, excellent Noetherian levels of the same dimension; its composite is
projective in the projective-bundle convention, birational, and unchanged over a normal open
avoiding the chosen centers. Length zero is included explicitly.

Source: Stacks Project, Resolution of Surfaces, Tag 0BFT (resolve-lemma-Nagata-normalized-blowup);
Morphisms Tags 035Q, 035S, 0B3I, 0C4P and 02JX; Divisors Tags 02ND and 02NS;
ILO Exposé XVII, §3.4.1 (blueprint: lem-per-excellent-normalized-blowup-tower).

Proof (the eight steps of the DAG):
1. For an integral excellent Noetherian T, the componentwise normalization is its
function-field normalization. On an affine domain A it is Spec of the integral closure of
A in Frac(A). Use lem-per-componentwise-normalization-affine-charts and
lem-per-excellent-normalization-preparation for finiteness, normality and excellence.
These chart rings are domains and their fraction fields equal Frac(A), giving integrality
and the function-field isomorphism by lem-weil-pbc-spec-domain-stalks-function-field.
2. Apply lem-trf-finite-projective-bundle and lem-trf-projective-bundle-proper to the
normalization map. The transcendence-degree term of lem-trf-closed-dominant-dimension
is zero, so normalization preserves dimension.
3. On a normal affine open, an integral rational section extends by
lem-sbc-normal-dense-open-integral-section. Thus its integral closure equals the original
ring; the affine normalization descriptions glue to the identity over every normal open.
4. Induct on the supplied tower. A closed point is not generic because d is positive;
its ideal is nonzero, quasi-coherent, and finitely generated on Noetherian affines.
Apply lem-per-integral-blowup-projective-geometry to its ordinary blowup B.
5. Properness of B over T gives finite type. Finite-type affine chart algebras are excellent
by lem-exc-finite-type-localization-excellent, hence Noetherian; a finite chart cover gives
Noetherianity of B. Apply lem-trf-excellent-scheme-affine-cover for all affine opens.
6. By thm-nagata-global-blowup-complement, B agrees with T away from the point, including
at the generic point. Apply lem-trf-closed-dominant-dimension, then steps 1 and 2 to B.
This gives the induction's normal, integral, excellent Noetherian next level of dimension d.
7. Locally Noetherian schemes are quasi-separated by
lem-weil-pbc-locally-noetherian-quasi-separated and our schemes are quasi-compact.
Apply lem-per-projective-bundle-composition twice. Compose the function-field isomorphisms.
8. Over the normal open U, the initial normalization is the identity by step 3. Each
center misses its inverse image; the ordinary blowup is the identity there by the
complement theorem, and its normalization is the identity by step 3. Induct and compose
these isomorphisms. This includes n = 0 and the empty open; no regular endpoint is built. -/
theorem excellent_normalized_blowup_tower
    (X : Scheme.{u}) [IsIntegral X] (d : ℕ) (hd : 1 ≤ d)
    [IsNoetherian X]
    (hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hDim : topologicalKrullDim X = d)
    (n : ℕ)
    (level : Fin (n + 1) → Scheme.{u})
    (center : ∀ i : Fin n, (level i.castSucc).IdealSheafData)
    (arrow : ∀ i : Fin n, level i.succ ⟶ level i.castSucc)
    (hzero : level 0 = X.normalization)
    (hpoint : ∀ i : Fin n, ∃ x : level i.castSucc,
      IsClosed ({x} : Set (level i.castSucc)) ∧
        center i = Scheme.IdealSheafData.vanishingIdeal
          ⟨closure ({x} : Set (level i.castSucc)), isClosed_closure⟩)
    (hblowup : ∀ i : Fin n, ∃ e : level i.succ ≅ (center i).normalizedBlowup,
      e.hom ≫ (center i).normalizedBlowupMap = arrow i)
    (π : ∀ i : Fin (n + 1), level i ⟶ X)
    (hπzero : π 0 = eqToHom hzero ≫ X.fromNormalization)
    (hπstep : ∀ i : Fin n, arrow i ≫ π i.castSucc = π i.succ)
    (r : level (Fin.last n) ⟶ X)
    (hr : r = π (Fin.last n)) :
    ∃ hIntegral : ∀ i : Fin (n + 1), IsIntegral (level i),
      (∀ i : Fin (n + 1), IsNoetherian (level i)) ∧
      (∀ i : Fin (n + 1), topologicalKrullDim (level i) = d) ∧
      (∀ i : Fin (n + 1), ∀ U : (level i).affineOpens,
        IsExcellent Γ(level i, U)) ∧
      (∀ i : Fin (n + 1), ∀ x : level i,
        IsDomain ((level i).presheaf.stalk x) ∧
          IsIntegrallyClosed ((level i).presheaf.stalk x)) ∧
      IsFinite X.fromNormalization ∧
      (∀ i : Fin n, IsFinite ((center i).blowup.fromReducedNormalization)) ∧
      IsProjectiveBundle r ∧
      (∃ hη : r (@genericPoint (level (Fin.last n)) _ inferInstance
          (@irreducibleSpace_of_isIntegral _ (hIntegral (Fin.last n)))) = genericPoint X,
        IsIso (@Scheme.Hom.functionFieldMap _ _ (hIntegral (Fin.last n))
          inferInstance r hη)) ∧
      (∀ U : X.Opens,
        (∀ x : U.toScheme,
          IsDomain (U.toScheme.presheaf.stalk x) ∧
            IsIntegrallyClosed (U.toScheme.presheaf.stalk x)) →
        (∀ i : Fin n, ∀ x : level i.castSucc,
          x ∈ (center i).support → π i.castSucc x ∉ U) →
        IsIso (pullback.snd r U.ι)) ∧
      (∀ U : X.Opens,
        (∀ x : U.toScheme,
          IsDomain (U.toScheme.presheaf.stalk x) ∧
            IsIntegrallyClosed (U.toScheme.presheaf.stalk x)) →
        IsIso (pullback.snd X.fromNormalization U.ι)) := by
  sorry

end AlgebraicGeometry
