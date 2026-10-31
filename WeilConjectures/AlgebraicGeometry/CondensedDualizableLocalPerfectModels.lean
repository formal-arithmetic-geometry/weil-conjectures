/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Topology.Irreducible

import WeilConjectures.AlgebraicGeometry.CondensedAffineLocalPerfectModels
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.AlgebraicGeometry.CondensedWContractibleProjectiveCalculus
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.CondensedLisseProEtaleLocality

/-! # Dualizable condensed complexes and local perfect scalar models

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.3(1),
the following stability observation, Definition 3.5 and Theorem 4.13
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).
All categories are ordinary unbounded derived categories of the published internal module
sheaves. Scalar realization uses the constant-section coefficient map, with derived extension.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

private theorem finite_components_of_openEmbedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] {f : S → T}
    (hf : Topology.IsOpenEmbedding f) (hT : (irreducibleComponents T).Finite) :
    (irreducibleComponents S).Finite := by
  apply Set.Finite.of_injOn (f := fun s : Set S ↦ closure (f '' s)) ?_ ?_ hT
  · intro s hs
    obtain ⟨t, ht, hst⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      _ (hs.1.image f hf.continuous.continuousOn).closure
    have hsub : s ⊆ f ⁻¹' t := fun x hx ↦ hst (subset_closure ⟨x, hx, rfl⟩)
    have hne : (t ∩ Set.range f).Nonempty := by
      obtain ⟨x, hx⟩ := hs.1.1
      exact ⟨f x, hsub hx, ⟨x, rfl⟩⟩
    have heq : f ⁻¹' t = s :=
      Set.Subset.antisymm (hs.2 (preimage_mem_irreducibleComponents ht hf hne).1 hsub)
        hsub
    have hc := closure_image_preimage_of_isPreirreducible f hf.isOpenMap t
      (by simpa only [heq] using hs.1.1) ht.1.2
      (isClosed_of_mem_irreducibleComponents _ ht)
    rw [heq] at hc
    change closure (f '' s) ∈ irreducibleComponents T
    rwa [hc]
  · intro s hs t ht h
    have hs' := hf.isEmbedding.closure_eq_preimage_closure_image s
    have ht' := hf.isEmbedding.closure_eq_preimage_closure_image t
    rw [(isClosed_of_mem_irreducibleComponents _ hs).closure_eq] at hs'
    rw [(isClosed_of_mem_irreducibleComponents _ ht).closure_eq] at ht'
    exact hs'.trans ((congrArg (Set.preimage f) h).trans ht'.symm)

private theorem scalar_realization_dualizable
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)))
    (hP : DerivedCategory.IsPerfectRingComplex P) :
    IsDualizable ((condensedScalarRealization Λ X).obj P) := by
  classical
  let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
  obtain ⟨I, W, f, hcover, hW⟩ :=
    (Scheme.ProEt.weaklyContractible_basis X).1 (Scheme.ProEt.mk (𝟙 X))
  let g (i : I) : (W i).left ⟶ X := (f i).left
  let C : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    { I₀ := I, X := fun i ↦ (W i).left, f := g, mem₀ := by
        change (Presieve.ofArrows W f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
          Scheme.proetalePrecoverage X at hcover
        rw [Presieve.map_ofArrows] at hcover
        exact hcover }
  apply (condensed_dualizable_iff_proetale_cover R X C _).mpr
  intro i
  obtain ⟨D, hD, ⟨e⟩⟩ := hW i
  let := hD
  have : IsAffine ((W i).left) := IsAffine.of_isIso e.inv
  have hΓ : IsWContractibleRing Γ((W i).left, ⊤) := by
    exact RingHom.wContractible_of_ringEquiv
      ((Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.symm.trans
        (asIso e.inv.appTop).commRingCatIsoToRingEquiv)
  let := hΓ
  obtain ⟨σ, _, hσ, _⟩ :=
    (CondensedRing.condensed_wcontractible_projective_calculus R ((W i).left)).2.2.2.2.2
  obtain ⟨c⟩ := condensed_scalarRealization_pullback R (g i)
  exact IsDualizable.of_iso (c.app P).symm (hσ P hP).2

/-- Dualizable objects contain zero and are closed under isomorphisms, all integer shifts
and distinguished cones, with no condition on the components of X.
`HasRightDual` is the existing exact pairing with both evaluation/coevaluation identities.
Source: HRS, observation after Definition 3.3
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).

Proof: apply the generic source-library theorems
`DerivedCategory.isDualizable_shift` and `DerivedCategory.isDualizable_obj₃_of_distTriang`
to the published derived tensor of internal modules. Zero is dualizable with itself as
dual and zero evaluation and coevaluation; the identities follow from zero-object
uniqueness. `IsDualizable.of_iso` transports a dual along an isomorphism. No local
finite-component or projective-unit hypothesis is needed. -/
theorem condensed_dualizable_stable :
    Nonempty (HasRightDual (0 : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ∧
    (∀ K L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      Nonempty (K ≅ L) → Nonempty (HasRightDual K) → Nonempty (HasRightDual L)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (n : ℤ), Nonempty (HasRightDual K) → Nonempty (HasRightDual (K⟦n⟧))) ∧
    (∀ T : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → Nonempty (HasRightDual T.obj₁) →
        Nonempty (HasRightDual T.obj₂) → Nonempty (HasRightDual T.obj₃)) := by
  refine ⟨CategoryTheory.IsZero.isDualizable (isZero_zero _), ?_, ?_, ?_⟩
  · rintro K L ⟨e⟩ hK
    exact IsDualizable.of_iso e hK
  · intro K n hK
    exact DerivedCategory.isDualizable_shift hK n
  · intro T hT h₁ h₂
    exact DerivedCategory.isDualizable_obj₃_of_distTriang T hT h₁ h₂

/-- On schemes with Zariski locally finitely many irreducible components, dualizability
is equivalent to pro-etale local realization of perfect complexes over Γ(*,Λ).
The cover members have independent scalar complexes. No coefficient flatness or
regularity is assumed.
Source: HRS, Definition 3.5 and Theorem 4.13
(blueprint: lem-zl-condensed-dualizable-local-perfect-models).

Proof: for the reverse implication, restrict each perfect scalar model to a
w-contractible affine pro-etale basis. The scalar clause of
`condensed_wcontractible_projective_calculus` makes its realization dualizable.
`condensed_scalarRealization_pullback` identifies the restriction with that realization.
Apply `condensed_dualizable_iff_proetale_cover` first on each cover member and then on X.
This direction needs no component condition.

For the forward implication, choose at each point an affine open contained in a
neighborhood having finitely many irreducible components. Under an open embedding,
the closure of the image of a component is an ambient component: enlarge the closure
to a component, pull back, and use maximality and density. The operation is injective
because pullback recovers the original closed component. Thus the affine open also has
finitely many components. Apply `condensed_affine_dualizable_local_perfect` there to
the pullback of K, which is dualizable by monoidal pullback. Compose the resulting
covers with the Zariski cover indexed by points of X. The canonical derived composition
comparison transports the scalar models to this composite cover. On the empty scheme
the point-indexed cover is empty. Scalar models vary independently across cover members. -/
theorem condensed_dualizable_iff_local_perfect
    (_hcomponents : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (irreducibleComponents U).Finite)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty (HasRightDual K) ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory).obj K ≅
            (condensedScalarRealization Λ (𝒰.X i)).obj P) := by
  constructor
  · intro hK
    classical
    let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
    choose U hxU hU using _hcomponents
    have hV (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
        (irreducibleComponents V).Finite := by
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (hxU x)
      let j : V → U x := fun y ↦ ⟨y.1, hVU y.2⟩
      have hj : Topology.IsOpenEmbedding j := by
        exact Topology.IsOpenEmbedding.of_comp j
          ((U x).isOpen.isOpenEmbedding_subtypeVal)
          (V.isOpen.isOpenEmbedding_subtypeVal)
      exact ⟨V, hV, hxV, finite_components_of_openEmbedding hj (hU x)⟩
    choose V hV hxV hfinite using hV
    let O : X.OpenCover := X.openCoverOfIsOpenCover V (by
      apply TopologicalSpace.IsOpenCover.mk
      apply top_le_iff.mp
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)
    let B := O.weaken (Scheme.zariskiPrecoverage_le_propQCPrecoverage
      (P := @WeaklyEtale))
    have hlocal (x : X) : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (V x),
        ∀ i : C.I₀,
          ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)),
            DerivedCategory.IsPerfectRingComplex P ∧
            Nonempty (((CondensedRing.upperStar Λ (C.f i)).mapDerivedCategory).obj
              (((CondensedRing.upperStar Λ (V x).ι).mapDerivedCategory).obj K) ≅
                (condensedScalarRealization Λ (C.X i)).obj P) := by
      have : IsAffine (V x).toScheme := hV x
      exact condensed_affine_dualizable_local_perfect Λ (V x) (hfinite x) _
        (condensed_derivedPullback_preserves_dualizable R (V x).ι K hK)
    choose C hC using hlocal
    refine ⟨B.bind C, ?_⟩
    rintro ⟨x, i⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hC x i
    refine ⟨P, hP, ⟨?_⟩⟩
    exact (Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarComp Λ ((C x).f i) (V x).ι)).app K ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app K ≪≫ e
  · rintro ⟨C, hC⟩
    let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
    apply (condensed_dualizable_iff_proetale_cover R X C K).mpr
    intro i
    obtain ⟨P, hP, ⟨e⟩⟩ := hC i
    exact IsDualizable.of_iso e.symm (scalar_realization_dualizable Λ (C.X i) P hP)

end AlgebraicGeometry.ProEtale
