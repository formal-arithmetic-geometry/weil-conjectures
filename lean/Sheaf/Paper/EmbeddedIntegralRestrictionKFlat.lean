/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.EmbeddedFiniteCoefficientRealization
import Sheaf.Paper.IntegralModelsEmbeddedScalarFlat
import all Sheaf.Paper.IntegralCoefficientSquareNormalization
import all Sheaf.CategoryTheory.InternalSectionTensorComparison
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses

/-! # K-flat restriction of integral scalars -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem flat_from_small (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u + 1, u + 1, u + 1}
      (R := (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (Scheme.ProEt.topology X)).obj R)
      ((SheafOfModules.pushforward (F := AsSmall.down)
        (J := Scheme.coefficientProEtaleModelTopology.{u, u} X) (𝟙 _)).obj M)) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} M := by
  let d := (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt)
  let a := (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X)
  let R' := (d.sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj R
  have h :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u + 1, u + 1, u + 1}
      R' _).mp hM
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1} R M).mpr
  intro U n b s hs
  obtain ⟨S, hS, hlocal⟩ := h (a.obj U) n b s hs
  refine ⟨S.functorPushforward d, ?_, ?_⟩
  · exact (Functor.mem_inducedTopology_iff_of_isCoverDense d
      (Scheme.ProEt.topology X) S).mp hS
  · intro V f hf
    have hg : S (a.map f) :=
      (Sieve.mem_functorPushforward_iff_of_full_of_faithful d S (a.map f)).mp hf
    exact hlocal (a.obj V) (a.map f) hg

attribute [-instance] integralModel_coefficientMonObj in
/-- Restriction of embedded integral scalars preserves K-flat cochain complexes.

Source: integral-models proof, first paragraph (1), flat scalar restriction;
Stacks Tags 06YN, 06YY and 03ER.
(blueprint: lem-sfb-embedded-integral-restriction-kflat).

Proof: the existing embedded scalar-flatness theorem gives flatness of the
restricted regular B-module on the coefficient-sized equivalent site. Translate
categorical flatness to the independent-universe flatness predicate. Flatness
on the original pro-etale site follows from the local equational criterion:
lift an object and a finite relation by AsSmall.up, take its covering solution
on the small site, and push that covering sieve through AsSmall.down. Fullness,
faithfulness and the induced-topology criterion identify the covering and all
its local solutions. This includes empty covering sieves.

Section-module reconstruction commutes with scalar restriction and sends the
regular internal B-module to the sectionwise unit module. Transport flatness
along those specified isomorphisms. The section tensor comparison identifies
native K-flatness of P with independent-coefficient K-flatness of its section
complex. Apply flat scalar restriction for sheaves of modules: tensoring an
acyclic R-complex with restricted P is identified with the restriction of its
scalar extension tensored over B with P. Flatness makes scalar extension exact,
so this is acyclic. Finally undo the restriction and section tensor isomorphisms.
The argument treats arbitrary integer-indexed complexes and does not infer flat
terms from K-flatness. -/
theorem embeddedIntegralRestrictionKFlat
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X]
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Mod.comap (scalarMap ℓ E X)).mapHomologicalComplex (.up ℤ)).obj P) := by
  let φ := scalarMap ℓ E X
  let R := condensedRingObj (discreteObj (PadicAlgCl.integers ℓ E.1)) X
  let B := integralCoefficientObject X ℓ E
  let J := Scheme.ProEt.topology X
  let eR := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let eB := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let α := CondensedRing.sectionRingMap X φ
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  let β := CondensedRing.sectionModuleComapIso X φ
  let b := β.app (Mod.regular B) ≪≫ U.mapIso (CondensedRing.sectionModuleRegularIso X B)
  have hsmall := integralModelsEmbeddedScalarFlat ℓ E π hπ X
  have hsf := (flat_iff_flatOnSite _).mp hsmall
  have hb : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (eR.functor.obj
      ((Mod.comap φ).obj (Mod.regular B))) := by
    apply flat_from_small.{u} X (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
    let V := SheafOfModules.pushforward (F := AsSmall.down)
      (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (K := Scheme.ProEt.topology X)
      (𝟙 ((AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))))
    change SheafOfModules.IsFlatOnSite
      (R := (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))
      (V.obj (U.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B))))) at hsf
    exact SheafOfModules.flatOnSite_of_iso
      ((AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) J).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))
      (V.mapIso b).symm hsf
  have hb' : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
      (U.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B)))) := by
    exact SheafOfModules.flatOnSite_of_iso.{u + 1, u + 1, u}
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R) b hb
  have hPi := (InternalAbelianSheafModule.comparison_kflat.{u + 1, u + 1, u} J B P).mp
    ((IntegralCoefficientSquare.internal_kflat_iff P).mpr hP)
  have hk := (SheafOfModules.isKFlat_restrictScalars_of_flat.{u + 1, u, u + 1} α hb'
    ((eB.functor.mapHomologicalComplex (.up ℤ)).obj P) hPi).1
  let d := (NatIso.mapHomologicalComplex β (.up ℤ)).app P
  apply (IntegralCoefficientSquare.internal_kflat_iff _).mp
  apply (InternalAbelianSheafModule.comparison_kflat.{u + 1, u + 1, u} J R _).mpr
  exact SheafOfModules.kFlat_iso_independent.{u + 1, u + 1, u}
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R) d.symm hk

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
