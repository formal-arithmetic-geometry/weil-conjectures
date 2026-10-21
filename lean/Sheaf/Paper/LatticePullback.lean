/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import all Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreePullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Sheaf.Paper.ContinuousCoefficientPullbackIso
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Pullback of continuous integral lattices

Source: blueprint main-20261015, six-functors basics, `sk-lem-stratified-lattice`,
proof, "Pushing down by the trace", restriction to a finite etale stratum;
Stacks Project, Modules on Sites, Tags 03D2 and 03EL
(blueprint: lem-sfb-lattice-pullback).

## Main definitions

- `latticePullbackScalarUnit`: the actual section `1 tensor m` in sheafified scalar extension.
- `continuousLatticePullbackSection`: the unit section of canonical coefficient pullback.

## Main statements

- `lattice_pullback`: the uniquely normalized pulled inclusion is monic, its source and
  target are locally finite free, and its own scalar-extension adjoint is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- Insertion into the existing scalar extension: apply its sheafification unit to `1 tensor m`.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sfb-lattice-pullback). -/
noncomputable def latticePullbackScalarUnit {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (V : X.ProEt) (m : M.val.obj (op V)) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M)).app (op V)
          ((1 : S.obj.obj (op V)) ⊗ₜ[R.obj.obj (op V), (a.hom.app (op V)).hom] m)

/-- The canonical pullback-unit section is inverse image of the section followed by insertion
into scalar extension along the adjunct of precomposition of continuous coefficient functions.
Source: Stacks Project, Tags 03D2 and 09A5; blueprint `sk-lem-stratified-lattice`,
"Pushing down by the trace" (blueprint: lem-sfb-lattice-pullback). -/
noncomputable def continuousLatticePullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (M : ringedSiteModules.{u + 1} (latticeModuleRing X T))
    (V : X.ProEt) (m : M.val.obj (op V)) :
    (continuousModulePullback g T M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  latticePullbackScalarUnit (continuousCoefficientInverseImageMap g T)
    ((Scheme.proEtaleModuleInverseImage g (latticeCoefficientSheaf X T)).obj M)
    ((Scheme.proEtaleBaseChange g).obj V)
    (ProEtaleTensorComparison.inverseSection g M V m)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringPullback_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : Scheme.proEtaleRingModules X R) (V : X.ProEt) (m : M.val.obj (op V)) :
    ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op V) m =
      latticePullbackScalarUnit c.hom ((Scheme.proEtaleModuleInverseImage f R).obj M)
        ((Scheme.proEtaleBaseChange f).obj V) (ProEtaleTensorComparison.inverseSection f M V m) :=
    by
  let adj := Scheme.proEtaleRingModuleAdjunction f R S c
  obtain ⟨k, hk, he⟩ := (Classical.choose_spec
    (Scheme.proEtaleRingModuleAdjunction_existsUnique f R S c)).1 M _ (𝟙 _)
  rw [← adj.homEquiv_id]
  erw [he]
  rw [Adjunction.homEquiv_unit]
  exact hk _ _

set_option backward.isDefEq.respectTransparency false in
private theorem scalarMate_adjunct
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ B} {U : B ⥤ A} {E' : A' ⥤ B'} {U' : B' ⥤ A'}
    (av : E ⊣ U) (au : E' ⊣ U') (P : A ⥤ A') (Q : B ⥤ B')
    (b : U ⋙ P ⟶ Q ⋙ U') (M : A) (L : B) (phi : E.obj M ⟶ L) :
    au.homEquiv _ _ (((mateEquiv av au).symm (TwoSquare.mk _ _ _ _ b)).app M ≫
      Q.map phi) = P.map (av.homEquiv _ _ phi) ≫ b.app L := by
  rw [au.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm av au (TwoSquare.mk _ _ _ _ b) M
  erw [← hu]
  change (P.map (av.unit.app M) ≫ b.app (E.obj M)) ≫ U'.map (Q.map phi) = _
  rw [Category.assoc]
  erw [← b.naturality phi]
  rw [Adjunction.homEquiv_unit, P.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarMate_isIso
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ B} {U : B ⥤ A} {E' : A' ⥤ B'} {U' : B' ⥤ A'}
    {P : A ⥤ A'} {D : A' ⥤ A} {Q : B ⥤ B'} {D' : B' ⥤ B}
    (av : E ⊣ U) (au : E' ⊣ U') (ar : P ⊣ D) (az : Q ⊣ D')
    (b : U ⋙ P ⟶ Q ⋙ U')
    (hb : IsIso ((mateEquiv az ar (TwoSquare.mk _ _ _ _ b)).natTrans)) :
    IsIso (((mateEquiv av au).symm (TwoSquare.mk _ _ _ _ b)).natTrans) := by
  let alpha := TwoSquare.mk _ _ _ _ b
  let gamma := (mateEquiv av au).symm alpha
  have hm : mateEquiv av au gamma = alpha := (mateEquiv av au).apply_symm_apply alpha
  have hc : IsIso (conjugateEquiv (av.comp az) (ar.comp au) gamma.natTrans) := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az gamma, hm]
    exact hb
  exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) gamma.natTrans

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringPullback_locallyFree {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : Scheme.proEtaleRingModules X R) [M.IsFiniteLocallyFree] :
    ((Scheme.proEtaleRingModulePullback f R S c).obj M).IsFiniteLocallyFree := by
  let a : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).obj
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap f R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0} a
  let := SheafOfModules.finiteLocallyFree_pullback.{u + 1, u, 0} a
    (Scheme.proEtaleBaseChangeCoverPreserving f) M
  let e := (SheafOfModules.pullbackPushforwardAdjunction a).leftAdjointUniq
    (Scheme.proEtaleRingModuleAdjunction f R S c)
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (e.app M)

private theorem coefficientSquare {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Type u} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (a : R →+* S) (ha : Continuous a) :
    continuousCoefficientInverseImageMap f R ≫ latticeCoefficientSheafMap Y a ha =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (latticeCoefficientSheafMap X a ha) ≫ continuousCoefficientInverseImageMap f S := by
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  unfold continuousCoefficientInverseImageMap
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
  (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
  (comm : cR.hom ≫ aX =
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (M : Scheme.proEtaleRingModules Y SY) (U : Y.ProEt) (m : M.val.obj (op U)) :
    ((Scheme.proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm).app M).val.app
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app
          ((Scheme.proEtaleRingRestrictScalars aY).obj M)).val.app (op U) m) =
      ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app M).val.app (op U) m := by
  let b := Scheme.proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm
  let d := Scheme.proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cR cS comm
  have h := unit_mateEquiv (Scheme.proEtaleRingModuleAdjunction f SY SX cS)
    (Scheme.proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b) M
  have hm : (mateEquiv (Scheme.proEtaleRingModuleAdjunction f SY SX cS)
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b)).natTrans =
      d.hom := AlgebraicGeometry.Scheme.restrictionPullback_mate
        f RY SY RX SX aY aX cR cS comm
  have hmapp : (mateEquiv (Scheme.proEtaleRingModuleAdjunction f SY SX cS)
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ b)).app
        ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) =
      d.hom.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) := congr_app hm _
  rw [hmapp] at h
  change (Scheme.proEtaleRingRestrictScalars aY).map
      ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app M) ≫
        d.hom.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) =
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app
          ((Scheme.proEtaleRingRestrictScalars aY).obj M) ≫
        (Scheme.proEtaleRingModuleDirectImage f RY RX cR).map (b.app M) at h
  have h' := congrArg (fun t ↦ (t.val.app (op U)) m) h
  have hd := (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f RY SY RX SX aY aX cR cS comm)).1
  change (d.hom.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M)).val.app (op U)
      (((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app M).val.app (op U) m) =
    (b.app M).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
      (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app
        ((Scheme.proEtaleRingRestrictScalars aY).obj M)).val.app (op U) m) at h'
  have hd' : ∀ (N : Scheme.proEtaleRingModules X SX) (W : Y.ProEtᵒᵖ)
      (z : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj W)),
      (d.hom.app N).val.app W z = z := hd
  erw [hd'] at h'
  exact h'.symm


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A lattice inclusion survives arbitrary scheme pullback, including its actual rationalization.
The hypothesis describes the scalar-extension adjoint by its defining unit formula. The
conclusion specifies the unique pulled inclusion on canonical inverse-image unit sections;
the final unit formula makes the rationalization the adjoint of this very inclusion.
`WithAbs` equips the field with its recorded extending absolute value, and
`latticeCoefficientIntegers` equips its valuation subring with the induced topology.

Source: blueprint main-20261015, `sk-lem-stratified-lattice`, proof,
"Pushing down by the trace", restriction of the universal lattice to each stratum;
Stacks Project, Modules on Sites, Tag 03EL (blueprint: lem-sfb-lattice-pullback).

Proof:
1. The spectral norm is ultrametric, so the field and its valuation ring are totally
   disconnected. Their actual continuous coefficient adjuncts are isomorphisms;
   naturality of postcomposition gives the compatible coefficient square.
2. Apply the canonical module pullback to the inclusion and compose with the
   restriction-of-scalars comparison. Its mate identity gives the section formula.
   Adjunction injectivity proves uniqueness, and exact pullback preserves monicity.
3. Pull finite local bases along the base-changed covering family, using localized
   ringed-site pullback and its comparison with ordinary module pullback.
4. Take the inverse mate of the restriction/pullback comparison under the two actual
   scalar-extension adjunctions. Its other mate is an invertible direct-image
   comparison; double mates show the scalar comparison is invertible as well.
5. Compose with the pullback of the given rationalization. The mate unit formula
   identifies its scalar-extension adjoint with the specified pulled inclusion,
   including the required formula on every section.
-/
theorem lattice_pullback (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : ringedSiteModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (M : ringedSiteModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    [L.IsFiniteLocallyFree] [M.IsFiniteLocallyFree]
    (i : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralLatticeCoefficientMap X l E))).obj L) [Mono i]
    (hi : ∃ phi : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap X l E) M ⟶ L,
      IsIso phi ∧ ∀ (V : X.ProEt) (m : M.val.obj (op V)),
        phi.val.app (op V) (latticePullbackScalarUnit (integralLatticeCoefficientMap X l E)
          M V m) = i.val.app (op V) m) :
    ∃! j : continuousModulePullback g (latticeCoefficientIntegers l E) M ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (integralLatticeCoefficientMap Y l E))).obj
                (continuousModulePullback g
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L),
      (∀ (V : X.ProEt) (m : M.val.obj (op V)),
        j.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
            (continuousLatticePullbackSection g (latticeCoefficientIntegers l E) M V m) =
          continuousLatticePullbackSection g
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L V (i.val.app (op V) m)) ∧
      Mono j ∧
      (continuousModulePullback g (latticeCoefficientIntegers l E) M).IsFiniteLocallyFree ∧
      (continuousModulePullback g
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L).IsFiniteLocallyFree ∧
      ∃ beta : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (integralLatticeCoefficientMap Y l E)
            (continuousModulePullback g (latticeCoefficientIntegers l E) M) ⟶
          continuousModulePullback g (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L,
        IsIso beta ∧ ∀ (V : Y.ProEt)
          (m : (continuousModulePullback g (latticeCoefficientIntegers l E) M).val.obj (op V)),
          beta.val.app (op V) (latticePullbackScalarUnit (integralLatticeCoefficientMap Y l E)
            (continuousModulePullback g (latticeCoefficientIntegers l E) M) V m) =
              j.val.app (op V) m := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let A := latticeCoefficientIntegers l E
  let : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (by
    intro x y
    exact isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) x.ofAbs y.ofAbs)
  let : TotallyDisconnectedSpace K := inferInstance
  let : TotallyDisconnectedSpace A := inferInstance
  let R := latticeCoefficientSheaf X A
  let S := latticeCoefficientSheaf X K
  let R' := latticeCoefficientSheaf Y A
  let S' := latticeCoefficientSheaf Y K
  let aX := integralLatticeCoefficientMap X l E
  let aY := integralLatticeCoefficientMap Y l E
  let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso g A
  let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso g K
  let cR := asIso (continuousCoefficientInverseImageMap g A)
  let cS := asIso (continuousCoefficientInverseImageMap g K)
  have comm : cR.hom ≫ aY = (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aX ≫
      cS.hom := coefficientSquare g A.subtype continuous_subtype_val
  let P := Scheme.proEtaleRingModulePullback g R R' cR
  let Q := Scheme.proEtaleRingModulePullback g S S' cS
  let ar := Scheme.proEtaleRingModuleAdjunction g R R' cR
  let az := Scheme.proEtaleRingModuleAdjunction g S S' cS
  let b := Scheme.proEtaleRingRestrictionPullbackInv g R S R' S' aX aY cR cS comm
  let := Scheme.proEtaleRingRestrictionPullbackInv_isIso g R S R' S' aX aY cR cS comm
  let j := P.map i ≫ b.app L
  have hj (V : X.ProEt) (m : M.val.obj (op V)) :
      j.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
        (continuousLatticePullbackSection g A M V m) =
      continuousLatticePullbackSection g K L V (i.val.app (op V) m) := by
    dsimp only [continuousLatticePullbackSection]
    erw [← ringPullback_unit g R R' cR M V m]
    erw [← ringPullback_unit g S S' cS L V (i.val.app (op V) m)]
    have hn := ar.unit.naturality i
    have h := congrArg (fun t ↦ t.val.app (op V) m) hn
    change (b.app L).val.app (op ((Scheme.proEtaleBaseChange g).obj V))
      ((P.map i).val.app (op ((Scheme.proEtaleBaseChange g).obj V))
        ((ar.unit.app M).val.app (op V) m)) = _
    change (ar.unit.app _).val.app (op V) (i.val.app (op V) m) =
      (P.map i).val.app (op ((Scheme.proEtaleBaseChange g).obj V))
        ((ar.unit.app M).val.app (op V) m) at h
    rw [← h]
    exact restrictionPullback_unit g R S R' S' aX aY cR cS comm L V _
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hsX := SheafOfModules.coefficientSheafification.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X)
  have hsY := SheafOfModules.coefficientSheafification.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y)
  let := hsX.1
  let := hsX.2
  let := hsY.1
  let := hsY.2
  let av : SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} aX ⊣
      SheafOfModules.ScalarReductionProof.restriction.{u + 1, u, u + 1, u + 1} aX :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction.{u + 1, u, u + 1} aX
  let au : SheafOfModules.ScalarReductionProof.tensorFunctor.{u + 1, u, u + 1} aY ⊣
      SheafOfModules.ScalarReductionProof.restriction.{u + 1, u, u + 1, u + 1} aY :=
    SheafOfModules.ScalarReductionProof.tensorAdjunction.{u + 1, u, u + 1} aY
  let gamma := (mateEquiv av au).symm (TwoSquare.mk _ _ _ _ b)
  have hm : IsIso ((mateEquiv az ar (TwoSquare.mk _ _ _ _ b)).natTrans) := by
    rw [AlgebraicGeometry.Scheme.restrictionPullback_mate]
    infer_instance
  let := scalarMate_isIso av au ar az b hm
  obtain ⟨phi, hphi, hunit⟩ := hi
  let := hphi
  have hphiAdj : av.homEquiv _ _ phi = i := by
    rw [Adjunction.homEquiv_unit]
    ext V m
    change phi.val.app V ((av.unit.app M).val.app V m) = i.val.app V m
    erw [SheafOfModules.ScalarReductionProof.tensorAdjunction_unit_apply
      aX M V m]
    exact hunit V.unop m
  let beta := gamma.app M ≫ Q.map phi
  have hbeta : au.homEquiv _ _ beta = j := by
    rw [scalarMate_adjunct, hphiAdj]
  refine ⟨j, ⟨hj, ?_, ringPullback_locallyFree g R R' cR M,
    ringPullback_locallyFree g S S' cS L, ⟨beta, ?_, ?_⟩⟩, ?_⟩
  · dsimp only [j]
    infer_instance
  · dsimp only [beta]
    infer_instance
  · intro V m
    have h := congrArg (fun t ↦ t.val.app (op V) m) hbeta
    rw [Adjunction.homEquiv_unit] at h
    change beta.val.app (op V) ((au.unit.app _).val.app (op V) m) = _ at h
    erw [SheafOfModules.ScalarReductionProof.tensorAdjunction_unit_apply
      aY (P.obj M) (op V) m] at h
    exact h
  · intro j' hj'
    apply (ar.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V m
    change j'.val.app (op ((Scheme.proEtaleBaseChange g).obj V.unop))
        ((ar.unit.app M).val.app V m) =
      j.val.app (op ((Scheme.proEtaleBaseChange g).obj V.unop)) ((ar.unit.app M).val.app V m)
    rw [ringPullback_unit]
    exact (hj'.1 V.unop m).trans (hj V.unop m).symm


end AlgebraicGeometry.ProEtale
