/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientQbarStratumAssembly
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
import WeilConjectures.AlgebraicGeometry.CondensedLocalModelGluing
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.Topology.ConstructibleIsRetrocompact

/-! # Finite coefficient models on qcqs schemes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sp-original-coefficient-qbar-heart-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A constructible module over the finite-subextension-valued algebraic closure
on a qcqs scheme descends to one finite coefficient field.
Source: Hemo--Richarz--Scholbach, Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sp-original-coefficient-qbar-heart-model)

Proof: on each finite presentation chart, descend the finitely many entries of the
presentation matrices along the filtered colimit of finite coefficient rings.
Descend the transition morphisms and their inverses on overlaps; their finitely
many inverse and cocycle relations hold at a sufficiently large finite extension.
Gluing produces a finitely presented model on each stratum. Refine the finite
constructible stratification to an open-closed filtration. At each step the
extension class descends by bounded-below filtered Ext continuity; enlarge the
finite field to include its entries and relations. Induction glues the finite
coefficient models. The actual flat coefficient extension preserves the cokernels
and extension classes, giving the specified isomorphism. Empty strata and the zero
module use their zero models over the base field. This uses the finite-subextension
coefficient object, not all continuous functions with values in the algebraic closure. -/
theorem originalCoefficientQbarHeartModel
    (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ell))
    (hM : IsConstructibleModuleObject (padicAlgClRingObj X ell) M) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ell E)),
      IsConstructibleModuleObject (padicSubfieldRingObj X ell E) N ∧
      Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ell E)).obj N ≅ M) := by
  obtain ⟨S, hS⟩ := hM
  apply originalCoefficientQbarStratumAssembly X ell M S
  intro a
  have hcompact : IsCompact (S.stratum a) :=
    (S.isConstructible_stratum a).isRetrocompact.isCompact
  have : CompactSpace (S.domain a) := isCompact_univ_iff.mp
    ((S.immersion a).isEmbedding.isCompact_iff.mpr (by
      simpa only [Set.image_univ, S.range_immersion] using hcompact))
  have : QuasiSeparatedSpace (S.domain a) :=
    quasiSeparatedSpace_of_quasiSeparated (S.immersion a)
  obtain ⟨E, U, hfinite, haffine, n, m, d, e⟩ :=
    exists_common_finiteCoefficient_presentation_matrices X (S.domain a)
      (S.immersion a) ell _ (hS a)
  have hN : ∀ i, Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj X ell E)))
      (cokernel (d i)) := fun i ↦ ⟨n i, m i, d i, ⟨Iso.refl _⟩⟩
  obtain ⟨F, hEF, P, eP, eM⟩ := exists_finiteCoefficient_gluing_of_local_models
    X (S.domain a) (S.immersion a) ell _ E U hfinite haffine
      (fun i ↦ cokernel (d i)) hN e
  refine ⟨F, P, ⟨U, fun i ↦ ?_⟩, eM⟩
  obtain ⟨ePi⟩ := eP i
  exact (fp_iff_of_iso ePi).mpr (fp_extend _ _ _ (hN i))

end AlgebraicGeometry.ProEtale.CondensedRing
