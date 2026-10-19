/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # The normalized edge map in the lowest cohomology degree
Source: blueprint main-20261015, lem-pur-gysin-structure, proof steps 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- The cocycle-normalized edge is invertible at the lowest possible cohomology degree.
Source: blueprint main-20261015, lem-pur-gysin-structure, second paragraph and the
canonical good-truncation argument of its first paragraph
(blueprint: lem-pur-concentrated-edge-iso).

Proof: choose a bounded-below injective representative zero below q for K, using good
truncation and the bounded-below injective resolution. In degree q it has no boundaries,
so both Hq of its global sections and global sections of its cohomology are the same
kernel of the differential. Global sections preserve this kernel. The normalization
formula identifies e with this kernel comparison on that representative: the homology
projections are the kernel identifications because degree q-1 is zero. Thus e is an
isomorphism there. Naturality transports invertibility along the representative's derived
isomorphism to K. No vanishing of higher cohomology is required. -/
theorem edge_isIso_of_isGE (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (q : ℤ) (e : hyper P Y q ⟶ localClasses P Y q)
    (he : EdgeNormalization P Y q e) (K : DerivedCategory (ProSheaves P Y))
    [K.IsGE q] : IsIso (e.app K) := by
  let C := ProSheaves P Y
  let E := globalSectionsFunctor (Modules P) Y
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := K.exists_iso_Q_obj_of_isGE q
  obtain ⟨L, hL, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective ⟨J, ⟨q, hJ⟩⟩ q
  have : QuasiIso i.hom := hi
  let I : CochainComplex C ℤ := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj L.obj
  have : I.IsStrictlyGE q := inferInstance
  have : I.IsKInjective := inferInstance
  let kIso : K ≅ DerivedCategory.Q.obj I :=
    eJ ≪≫ asIso (DerivedCategory.Q.map i.hom)
  have hπ : IsIso (I.homologyπ q) :=
    I.isIso_homologyπ (q - 1) q (by simp) (by
      exact (I.isZero_of_isStrictlyGE q (q - 1) (by omega)).eq_of_src _ _)
  have hπ' : IsIso (((E.mapHomologicalComplex (.up ℤ)).obj I).homologyπ q) := by
    apply HomologicalComplex.isIso_homologyπ _ (q - 1) q (by simp)
    exact (E.map_isZero (I.isZero_of_isStrictlyGE q (q - 1) (by omega))).eq_of_src _ _
  have hn := he I
  have hiR : IsIso
      (((((I.sc q).map E).cyclesIsoKernel) ≪≫
        (asIso (kernelComparison (I.sc q).g E)).symm ≪≫
        E.mapIso (I.sc q).cyclesIsoKernel.symm).hom ≫
        E.map (I.homologyπ q) ≫
        E.map ((DerivedCategory.homologyFunctorFactors C q).inv.app I)) := by
    infer_instance
  let f := (((E.mapHomologicalComplex (.up ℤ)).obj I).homologyπ q ≫
    (DerivedCategory.homologyFunctorFactors (Modules P) q).inv.app _ ≫
    (DerivedCategory.homologyFunctor (Modules P) q).map
      (E.rightDerivedFunctorObjQIso I).inv)
  have : IsIso f := by dsimp [f]; infer_instance
  have : IsIso (f ≫ e.app (DerivedCategory.Q.obj I)) := by
    simpa only [f, Category.assoc] using
      (show IsIso _ from hn.symm ▸ hiR)
  have : IsIso (e.app (DerivedCategory.Q.obj I)) := IsIso.of_isIso_comp_left f _
  exact (NatTrans.isIso_app_iff_of_iso e kIso).mpr inferInstance

end AlgebraicGeometry.ProEtale.RetractedSupport
