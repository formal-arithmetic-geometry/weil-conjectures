/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Constructible
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
import Sheaf.AlgebraicGeometry.LocalSpectrumOpenClassification
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso
import Sheaf.AlgebraicGeometry.LocalPullbackAdjointStalkIso
import Mathlib.Topology.Sheaves.Abelian

/-!
# Higher direct images of retrocompact opens in local dimension at most one

Source: Stacks Project, Varieties, Tag 09N8, lemma-affine
(blueprint: lem-a1-open-dimension-one-higher-image-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If every local ring of a scheme is Noetherian of dimension at most one, the positive
higher direct images of a quasi-coherent module along a retrocompact open inclusion vanish.

Source: Stacks Project, Varieties, Tag 09N8, lemma-affine
(blueprint: lem-a1-open-dimension-one-higher-image-vanishing).

Proof:
1. Test vanishing at each stalk x. The affine-open stalk localization theorem
(lem-weil-pbc-affine-open-stalk-localization), together with localization flatness
(lem-weil-pbc-localization-flat), makes Spec O_{X,x} -> X flat. Retrocompactness makes
U.ι quasi-compact; its diagonal is an isomorphism, so it is quasi-separated. Flat base
change (lem-pc-flat-base-change-cohom) reduces the stalk to the pulled-back open immersion
into Spec O_{X,x}.
2. Apply lem-a1-local-spectrum-open-classification to this Noetherian local ring of
dimension at most one. If its closed point belongs to the pulled-back open, the open is
the whole spectrum and its inclusion has vanishing positive higher direct images.
Otherwise the open has finite discrete underlying space and is affine.
3. In the latter case its morphism to the affine local spectrum is affine. The pullback
of F is quasi-coherent, so lem-pc-affine-morphism-hi gives vanishing in every positive
degree. Both cases give zero stalks, hence the original higher direct image is zero. -/
theorem isZero_higherDirectImage_open_of_stalk_dimension_le_one
    (X : Scheme.{u}) (hnoeth : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (hF : F.IsQuasicoherent) (p : ℕ) (hp : 0 < p) :
    IsZero (((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerived p).obj F) := by
  classical
  let : EnoughInjectives U.toScheme.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives U.toScheme.toRingedSpace).2
  let : F.IsQuasicoherent := hF
  have hqc : QuasiCompact U.ι := by
    apply quasiCompact_iff_forall_isAffineOpen.mpr
    intro V hV
    apply U.ι.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    change IsCompact (U.ι '' (U.ι ⁻¹' (V : Set X)))
    simpa only [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
      Set.inter_comm] using hU hV.isCompact V.isOpen
  let : QuasiCompact U.ι := hqc
  let G : X.Modules :=
    ((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerived p).obj F
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  suffices hA : IsZero (A.obj G) from
    (IsZero.iff_id_eq_zero G).mpr (A.map_injective (hA.eq_of_src _ _))
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (A.obj G)).mpr
  intro x
  let c := X.fromSpecStalk x
  let j := pullback.fst c U.ι
  let g := pullback.snd c U.ι
  let : IsNoetherianRing (X.presheaf.stalk x) := hnoeth x
  let : Flat c := (Scheme.fromSpecStalk_local_properties X x).2.2.2.2.2
  let : Flat g := inferInstanceAs (Flat (pullback.snd c U.ι))
  have hW : IsAffine j.opensRange.toScheme := by
    obtain ⟨hclosed, hopen⟩ := localSpectrum_open_classification
      (X.presheaf.stalk x) (hdim x) j.opensRange
    by_cases hx : IsLocalRing.closedPoint (X.presheaf.stalk x) ∈ j.opensRange
    · rw [hclosed hx]
      exact isAffineOpen_top _
    · exact (hopen hx).2.2
  let : IsAffine (pullback c U.ι) := by
    let := hW
    exact IsAffine.of_isIso j.isoOpensRange.hom
  let : IsAffineHom j := inferInstance
  let : EnoughInjectives (pullback c U.ι).Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives
      (pullback c U.ι).toRingedSpace).2
  let F' := (Scheme.Modules.tensorPullback g).obj F
  let eP := Adjunction.leftAdjointUniq
    (Scheme.Modules.nonempty_tensorPullbackAdjunction g).some
    (Scheme.Modules.pullbackPushforwardAdjunction g)
  let : F'.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback c U.ι).ringCatSheaf).prop_of_iso
      (eP.app F).symm (Scheme.Modules.isQuasicoherent_pullback g F)
  have hz : IsZero (((Scheme.Modules.pushforward j).rightDerived p).obj F') :=
    Scheme.Modules.isZero_higherDirectImage_of_isAffineHom j F' hp
  let I := injectiveResolution F
  let J := injectiveResolution F'
  obtain ⟨t, ht⟩ := Scheme.Modules.flatBaseChangeResolutionLift U.ι c I J
  let beta := Scheme.Modules.flatBaseChangeResolutionBeta U.ι c I J t p
  have : IsIso beta :=
    Scheme.Modules.flatBaseChangeResolutionBeta_isIso U.ι c F I J t ht p
  let a := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction c)).homEquiv
    _ _ beta
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a) :=
    localPullback_adjoint_stalk_isIso X x G _ beta
  have hz' := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero
    ((Scheme.Modules.pushforward c).map_isZero hz)
  have hs := ModuleCat.subsingleton_of_isZero
    (hz'.of_iso (asIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map a)))
  exact @AddCommGrpCat.isZero_of_subsingleton _ hs

end AlgebraicGeometry
