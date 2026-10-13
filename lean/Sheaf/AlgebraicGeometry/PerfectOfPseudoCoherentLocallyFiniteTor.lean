/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.LocallyFiniteTorDimension
import Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude
import Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import all Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Pseudo-coherent complexes of locally finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Tag 08CQ, implication (2) to (1).
(blueprint: lem-pc-pseudo-coherent-locally-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A pseudo-coherent object with locally finite Tor dimension is perfect.
Source: Stacks Project, Cohomology of Sheaves, Tag 08CQ, implication (2) to (1).
(blueprint: lem-pc-pseudo-coherent-locally-finite-tor-perfect).

Proof: At x choose a pseudo-coherent bounded-above finite-free model on U,
and a Tor neighbourhood W with interval [a,b]. Refine U intersect W to an
affine open V containing x. Exact over-site restriction preserves the upper
bound and free terms, and its derived composition comparison restricts the
representing isomorphism. Lift this finite-free complex through the fully
faithful affine associated-sheaf functor, using its finite-free comparison.
Faithfulness checks the differential relations. The lifted ring complex is
pseudo-coherent by its own finite-free model. The local affine Tor-transfer
lemma gives finite Tor amplitude from the bounds on W. The ring criterion
gives a bounded finite-projective model in the ring derived category.
Associate sheaves to its terms: finite projectives are retracts of finite
free modules, and the associated-sheaf functor preserves the retractions
and zero objects. Thus the model is strictly perfect. The localized derived
sheafification comparison transports the ring-derived isomorphism and the
original local representing isomorphism to give the required perfect model
at x. Empty schemes require no witnesses; zero rings and rank-zero terms
are permitted throughout. -/
theorem isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension (S : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings S.toRingedSpace).over U))]
    [∀ W : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings W.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K)
    (hTor : HasLocallyFiniteTorDimension S K) : IsPerfect S K := by
  intro x
  obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hK x
  obtain ⟨W, hxW, a, c, hac, hW⟩ := hTor x
  obtain ⟨V, hV, hxV, hVUW⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ W) ⟨hxU, hxW⟩
  have hVU : V ≤ U := hVUW.trans inf_le_left
  have hVW : V ≤ W := hVUW.trans inf_le_right
  let F := SheafOfModules.overMap.{uP} (moduleRings S.toRingedSpace) (homOfLE hVU)
  let G := SheafOfModules.overFunctor.{uP} (moduleRings S.toRingedSpace) U
  let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (PV.X i) := by
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
  have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over V) (ULift.{uP} (Fin r))) := by
    obtain ⟨r, ⟨e⟩⟩ := hf i
    let ef : F.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{uP} (Fin r))) ≅
        SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over V) (ULift.{uP} (Fin r)) :=
      (asIso (Limits.sigmaComparison F (fun _ : ULift.{uP} (Fin r) ↦
        SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)))).symm ≪≫
          Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso
            (R := moduleRings S.toRingedSpace) (homOfLE hVU))
    exact ⟨r, ⟨F.mapIso e ≪≫ ef⟩⟩
  have : Limits.PreservesFiniteLimits (G ⋙ F) := Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits (G ⋙ F) := Limits.comp_preservesFiniteColimits _ _
  let eV : (SheafOfModules.overFunctor.{uP}
      (moduleRings S.toRingedSpace) V).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj PV :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{uP}
        (moduleRings S.toRingedSpace) (homOfLE hVU))).symm.app K ≪≫
      (Functor.mapDerivedCategoryCompIso G F).app K ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
        F.mapDerivedCategoryFactors.app P
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_finiteFree_model S V hV PV hbV hfV
  let R := S.presheaf.obj (.op V)
  let : HasDerivedCategory (ModuleCat.{uP} R) := HasDerivedCategory.standard _
  have hMpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    ⟨M, b, hMb, hMf, ⟨Iso.refl _⟩⟩
  let eKM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
  have hMtor := finiteTorAmplitude_of_affine_sheafification_of_open_tor S V hV K M ⟨eKM⟩
    W hVW ⟨a, c, hac, hW⟩
  obtain ⟨E, hEb, hEf, hEp, ⟨eE⟩⟩ :=
    DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
      (DerivedCategory.Q.obj M) hMpc hMtor
  let T := (affinePerfectSheafification S V hV).mapHomologicalComplex (.up ℤ)
  obtain ⟨D, _, ⟨c⟩⟩ := affine_localized_derived_sheafification S V hV
  refine ⟨V, hxV, T.obj E, affine_projective_strictlyPerfect S V hV E hEb hEf hEp, ?_⟩
  exact ⟨eKM ≪≫ (c.app M).symm ≪≫ D.mapIso eE.symm ≪≫ c.app E⟩

end AlgebraicGeometry.Scheme
