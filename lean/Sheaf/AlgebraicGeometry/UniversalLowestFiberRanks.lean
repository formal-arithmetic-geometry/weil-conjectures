/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups M3, K2
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

/-! # Residue ranks on a universally free lowest locus
Source: Stacks Project, Tags 0BDL, 0BDI, 08CI and 09U8.
(blueprint: lem-sc-universal-lowest-fiber-ranks). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
open MonoidalCategory in
/-- The K-flat witness computes homology of tensor with a module in degree zero.
Source: Stacks Project, Tags 06YU and 06YH. -/
private theorem tensor_single_vanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes X E F i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (E ⊗ (DerivedCategory.singleFunctor _ 0).obj F)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := h
  let N := (HomologicalComplex.single _ (.up ℤ) 0).obj F
  obtain ⟨c⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  let e : E ⊗ (DerivedCategory.singleFunctor _ 0).obj F ≅
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P N (curriedTensor _)) :=
    tensorIso eP.symm ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
      (c.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _)

/-- On the spectrum of a field, a rank-r locally free sheaf has r-dimensional sections.
Source: Stacks Project, Tag 0BDI, fibre dimension formula; the free-sheaf sections
calculation in WeilConjectures.AlgebraicGeometry.Modules.FreeComplex. -/
private theorem finrank_sections_of_rank {R : CommRingCat.{u}} (hR : IsField R)
    (M : (Spec R).Modules) (r : ℕ) (hr : M.IsFiniteLocallyFreeOfRank r) :
    Module.finrank R ((moduleSpecΓFunctor (R := R)).obj M) = r := by
  classical
  let := hR.toField
  have := hr
  obtain ⟨ι, U, hU, e⟩ := Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  obtain ⟨x⟩ : Nonempty (Spec R) := inferInstance
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hU.ge (Set.mem_univ x) : x ∈ ⨆ j, U j)
  have : Subsingleton (Spec (.of R)) := inferInstance
  have htop : U j = ⊤ := eq_top_iff.2 fun y _ ↦ by
    rwa [Subsingleton.elim y x]
  have ej := e j
  rw [htop] at ej
  have : IsIso (⊤ : (Spec R).Opens).ι :=
    inferInstanceAs (IsIso (Spec R).topIso.hom)
  obtain ⟨hdim, _⟩ := Modules.finrank_moduleSpecΓFunctor_obj_free hR
    (Modules.isoFreeOfRestrictIso M _ ej.some)
  simpa using hdim

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
set_option linter.unusedVariables false in
/-- Tor amplitude and the residue-field rank tests determine the bottom fibre ranks.
Source: Stacks Project, Tag 0BDL, first paragraph of the proof; Tag 0BDI,
fibre base-change formula; Tags 08CI and 09U8, bounded flat models and pullback.
(blueprint: lem-sc-universal-lowest-fiber-ranks).

Proof: The K-flat tensor comparison identifies each assumed vanishing test
with zero homology of E tensor the corresponding module in degree zero.
The t-structure characterizations give categorical Tor amplitude in [a,b].
The general bounded-flat-model theorem gives a flat complex P representing E,
zero outside [a,b], without needing a <= b. The flat-complex derived-pullback
comparison computes the residue pullback termwise. Below a its terms are zero,
so its homology and its evaluated cohomology vector space are zero; their
finrank is therefore zero.
For the bottom rank, derived composition identifies the residue test at t
with the degree-a fibre cohomology sheaf of Lh*E. A rank-r locally free sheaf
on the spectrum of kappa(t) is globally free: a trivializing cover has a
member containing the unique point, and that member is the whole spectrum.
The existing free-sheaf sections calculation gives dimension r. The derived
fibre base-change isomorphism identifies this vector space with extension
of scalars from the fibre at h(t). Field extension preserves finrank, giving
beta_a(E,h(t)) = r. Perfection is not needed in this argument, but its
hypothesis is kept in the interface. Rank zero is covered by the free-sheaf
calculation. If b < a, the flat model is zero in every degree; no point is
chosen on an empty T. -/
theorem universalLowest_fiber_ranks
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ) (T : Scheme.{u}) (h : T ⟶ S)
    (hres : ∀ t : T,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (T.residueField t)).toRingedSpace)) a).obj
            ((derivedPullback (T.fromSpecResidueField t ≫ h)).obj E)) r) :
    ∀ t : T, (∀ i : ℤ, i < a → derivedFiberBetti S E i (h t) = 0) ∧
      derivedFiberBetti S E a (h t) = r := by
  classical
  let C := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let := SheafOfModules.monoidalCategory S.sheaf
  let := SheafOfModules.symmetricCategory S.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed S.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings S.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution S
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have htor : DerivedCategory.torAmplitudeIn C a b E := by
    intro F
    refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
    · intro i hi
      exact tensor_single_vanishes S E F i (hamp F i (Or.inl hi))
    · intro i hi
      exact tensor_single_vanishes S E F i (hamp F i (Or.inr hi))
  obtain ⟨P, hge, hle, hf, ⟨eP⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn htor
  intro t
  constructor
  · intro i hi
    let g := S.fromSpecResidueField (h t)
    obtain ⟨F, hF, hmap, hAdd, ε, hderived, e, _⟩ :=
      flatComplexDerivedPullback g P
        ⟨b, fun j hj ↦ P.isZero_of_isStrictlyLE b j hj⟩ (fun j ↦ (hf j).2)
    have : F.Additive := hAdd
    let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
    let ec : DerivedCategory.Q.obj Q ≅ (derivedPullback g).obj E :=
      (DerivedCategory.quotientCompQhIso _).symm.app Q ≪≫
      (DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P)).symm ≪≫
      e ≪≫ (derivedPullback g).mapIso
        ((DerivedCategory.quotientCompQhIso _).app P ≪≫ eP)
    have hz : IsZero (Q.homology i) :=
      (Q.sc i).isZero_homology_of_isZero_X₂
        (F.map_isZero (P.isZero_of_isStrictlyGE a i hi))
    have hz' := hz.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso ec.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app Q)
    have hzv : IsZero (derivedFiberCohomology S E i (h t)) :=
      (ModuleCat.restrictScalars.{u, u, u} (ΓSpecIso (S.residueField (h t))).inv.hom).map_isZero
        ((SheafOfModules.evaluation.{u}
          (moduleRings (Spec (S.residueField (h t))).toRingedSpace)
          (Opposite.op ⊤)).map_isZero hz')
    have := ModuleCat.subsingleton_of_isZero hzv
    exact Module.finrank_zero_of_subsingleton
  · obtain ⟨_, _, _, c, _, _⟩ := exists_derivedPullbackComposition
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (T.residueField t)).toRingedSpace)) a
    let eH := H.mapIso ((c (T.fromSpecResidueField t) h).app E)
    have hrank : (H.obj ((derivedPullback (T.fromSpecResidueField t)).obj
        ((derivedPullback h).obj E))).IsFiniteLocallyFreeOfRank r := by
      have := hres t
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eH.symm
    have hd : derivedFiberBetti T ((derivedPullback h).obj E) a t = r :=
      finrank_sections_of_rank (Field.toIsField (T.residueField t)) _ r hrank
    obtain ⟨eb⟩ := derivedFiberCohomology_baseChange_iso S T E h a t
    let := (h.residueFieldMap t).hom.toAlgebra
    have hb : derivedFiberBetti T ((derivedPullback h).obj E) a t =
        derivedFiberBetti S E a (h t) :=
      eb.toLinearEquiv.finrank_eq.trans Module.finrank_baseChange
    exact hb.symm.trans hd

end AlgebraicGeometry.Scheme
