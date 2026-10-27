/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Sheaf.Paper.SupportedModelHullPullback
import Sheaf.Paper.SupportedModelPushforwardStrictColimit
import Sheaf.Paper.ProetaleCechProductClassRecovery
import Sheaf.Paper.ProetaleSupportedModelCoinduction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pro-etale descent for the supported model hull

Source: agent-formulated descent obligation below blueprint latest
sec-six-functors-basics/sk-prop-sf-comp-coherence, refinement (2), first paragraph.
HRS Sections 3--4 supply the ambient setting; Corollary 4.7 does not assert this
hull-locality statement. Exact reference WANTED.
(blueprint: lem-sfb-supported-hull-proetale-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem directImage_preimage_class
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (U V : Scheme.{u})
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [WeaklyEtale b] [QuasiCompact b] [QuasiSeparated b]
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))))
    (hP : IsSupportedModelHullClass Λ V P)
    (hgen : ∀ (W : Scheme.{u}) (p : ScalarModelSupportChain U W)
      (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)),
      HasFiniteConstantLocalModel Λ W L →
        P ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L)))) :
    IsSupportedModelHullClass Λ U
      (P.inverseImage (CondensedRing.moduleObjectDerivedPushforward Λ b)) := by
  let F := (CondensedRing.lowerStar Λ b).rightDerivedFunctor
  change IsSupportedModelHullClass Λ U (P.inverseImage F)
  have : P.IsTriangulated := hP.1
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  have : F.IsRightAdjoint := by
    dsimp only [F]
    infer_instance
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, hgen⟩
  · intro K L i p hip hL
    apply hP.2.2.1 (F.obj K) (F.obj L) (F.map i) (F.map p) _ hL
    rw [← F.map_comp, hip, F.map_id]
  · intro J K c hc hK
    let d := Fan.mk (F.obj c.pt) (fun j ↦ F.map (c.π.app (Discrete.mk j)))
    have hd : IsLimit d :=
      (Fan.isLimitMapConeEquiv F K c) (isLimitOfPreserves F hc)
    exact hP.2.2.2.1 J _ d hd hK
  · intro J _ _ D a hD hmem c hc
    exact supportedModelClass_pushforward_strictColimit Λ U V b P hP J D a hD hmem c hc

/-- Membership in the supported model hull for a module in degree zero descends along
an arbitrary small affine weakly contractible pro-etale covering family.
Source: agent-formulated descent obligation, HRS Sections 3--4 for ambient coefficients;
exact reference WANTED. Corollary 4.7 is not claimed as a reference for hull locality.
(blueprint: lem-sfb-supported-hull-proetale-descent)

Proof plan (the nine steps of the DAG):
1. Handle the empty scheme. Otherwise finite_affine_proetale_refinement and qcqs
   finite-family geometry retain finitely many original affine covering objects.
2. Weakly etale localization, the ringed slice adjunction and internal module
   transport identify exact inverse image with restriction. It preserves products
   and all colimits, hence derived products and common-bound strict filtered colimits.
3. Base-change every open and closed support arrow. Ring-sheaf base-change mates
   identify pullback of its extension with extension of its pullback. Finite scalar
   models pull back to such models. The defining intersection gives hull stability.
4. Derived direct image is triangulated and a right adjoint, hence preserves
   products, zero, isomorphisms and retracts.
5. In the Grothendieck category of small module diagrams, the all-lower-bounds
   Cartan--Eilenberg resolution and total-resolution theorem give simultaneous
   bounded-below injective replacements. Evaluation preserves injectives since its
   coproduct left adjoint is exact. Bounded-below injectives are K-injective.
6. Bounded direct-image continuity identifies the filtered colimit of these strict
   pushforward models with the pushforward of the filtered colimit. Generator-level
   coinduction (lem-sfb-proetale-supported-model-coinduction, not yet stated) and
   the defining intersection imply that qcqs site direct image preserves the hull.
7. The coherent Cech pushforward model (lem-sfb-cech-pushforward-augmented-model,
   not yet stated) identifies N[0] with its total. Each column is a finite product
   of derived direct images from finite intersections. Steps 3 and 6 place every
   column in the hull; intersections need not be affine or weakly contractible.
8. Truncate horizontally at m, discarding the outgoing differential. The kernel
   of the projection to the preceding truncation is the mth column shifted by -m.
   The short-exact-complex triangle and induction put each truncation in the hull.
9. The truncation projections split as graded maps. Their degreewise limit is the
   full nonnegative total, and the sequence from that total to the product of all
   truncations, followed by 1-shift on that product, is degreewise short exact.
   Termwise products compute derived products. Its triangle gives total membership,
   hence N[0] membership. No bound on local generation expressions is needed.
-/
theorem supportedModelHull_proetale_descent
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (I : Type (u + 1)) (U : I → V.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.proetalePrecoverage.coverings V)
    (haffine : ∀ i : I, IsAffine (U i).left)
    (hcontract : ∀ i : I, (Scheme.ProEt.topology V).IsWeaklyContractible.{u + 1} (U i))
    (hlocal : ∀ i : I, supportedModelHull Λ (U i).left
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.upperStar Λ (U i).hom).obj N))) :
    supportedModelHull Λ V ((DerivedCategory.singleFunctor _ 0).obj N) := by
  have _ := hcontract
  intro P hP
  apply proetale_cech_product_class_recovery Λ V N I U hcover haffine P hP.1 hP.2.1
    hP.2.2.2.1
  intro i W _ _ r _ _ _
  have : IsAffine (U i).left := haffine i
  have : CompactSpace (U i).left := inferInstance
  have : QuasiSeparatedSpace (U i).left := inferInstance
  have hrestrict := supportedModelHull_pullback_single Λ W (U i).left r
    ((CondensedRing.upperStar Λ (U i).hom).obj N) (hlocal i)
  apply hrestrict (P.inverseImage
    (CondensedRing.moduleObjectDerivedPushforward Λ (r ≫ (U i).hom)))
  apply directImage_preimage_class Λ W V (r ≫ (U i).hom) P hP
  intro T p L hL
  exact proetale_supported_model_coinduction ℓ Λ hΛ W V (r ≫ (U i).hom) T p L hL P hP

end AlgebraicGeometry.ProEtale
