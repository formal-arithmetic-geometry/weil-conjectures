/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ConnectedFibresConstantDegreeZero
import Sheaf.AlgebraicGeometry.PrimeCurveCharPHighVanishing
import Sheaf.AlgebraicGeometry.PrimeCurveGeometricStalkFinite
import Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso
import Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel
import Sheaf.AlgebraicGeometry.ConstructibleCyclicModuleOfAbelian
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel
import Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization

/-!
# Prime coefficients in proper smooth curve families

Source: Stacks Project, more-etale.tex, Tag 0GKV, lemma-proper-smooth-family-curves,
the Noetherian case (blueprint: lem-weil-pbc-proper-smooth-curves-prime-coefficients).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem curve_fiber_dimension_baseChange
    {C S T : Scheme.{u}} (f : C ⟶ S) [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1) (g : T ⟶ S) :
    ∀ t : T, topologicalKrullDim ((pullback.snd f g).fiber t) = 1 := by
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : SmoothOfRelativeDimension 1 f :=
    smoothOfRelativeDimension_of_fiberToSpecResidueField f 1 fun s ↦ by
      have : Smooth (f.fiberToSpecResidueField s) :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IrreducibleSpace (f.fiber s) := inferInstance
      exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq
        (f.fiberToSpecResidueField s) 1).mpr (hdim s)
  intro t
  have : SmoothOfRelativeDimension 1
      ((pullback.snd f g).fiberToSpecResidueField t) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd _ _))
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension
    ((pullback.snd f g).fiberToSpecResidueField t) 1

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def higherDirectImage_baseChange_iso
    (R : Type (u + 1)) [CommRing R] (hR : IsAddTorsion R)
    {C S T : Scheme.{u}} (f : C ⟶ S) [IsProper f] (g : T ⟶ S)
    (q : ℕ) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (upperStar (ModuleCat.{u + 1} R) g).obj (higherDirectImage R f q F) ≅
      higherDirectImage R (pullback.snd f g) q
        ((upperStar (ModuleCat.{u + 1} R) (pullback.fst f g)).obj F) := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let P := upperStar (ModuleCat.{u + 1} R) (pullback.fst f g)
  have : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} R)
      (IsPullback.of_hasPullback f g).toCommSq).app K) :=
    hasTorsionBaseChange_of_isProper R f (IsPullback.of_hasPullback f g) K
      (DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion R C hR K)
  exact ((upperStar (ModuleCat.{u + 1} R) g).mapDerivedCategoryPlusHomologyFunctorIso
      (q : ℤ)).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      (asIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} R)
        (IsPullback.of_hasPullback f g).toCommSq).app K) ≪≫
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) (pullback.snd f g)).mapIso
        ((P.mapDerivedCategoryPlusSingleFunctor 0).app F))

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def constant_baseChange_iso
    (R : Type (u + 1)) [CommRing R] (hR : IsAddTorsion R)
    {C S T : Scheme.{u}} (f : C ⟶ S) [IsProper f] (g : T ⟶ S)
    (q : ℕ) (M : ModuleCat.{u + 1} R) :
    (upperStar (ModuleCat.{u + 1} R) g).obj
      (higherDirectImage R f q ((constantSheaf C.smallEtaleTopology _).obj M)) ≅
    higherDirectImage R (pullback.snd f g) q
      ((constantSheaf (pullback f g).smallEtaleTopology _).obj M) :=
  higherDirectImage_baseChange_iso R hR f g q _ ≪≫
    ((DerivedCategory.Plus.singleFunctor _ 0) ⋙
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) (pullback.snd f g) ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} R) (pullback.fst f g)).app M)

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem prime_restriction_glue
    {S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ell : ℕ)
    (hopen : ∀ (U : Scheme.{u}) (j : U ⟶ S) [IsOpenImmersion j],
      (∀ x : U, IsUnit (ell : U.presheaf.stalk x)) →
      Scheme.IsConstructibleSheaf ((upperStar (ModuleCat.{u + 1} Λ) j).obj F))
    (hclosed : ∀ (Z : Scheme.{u}) (i : Z ⟶ S) [IsClosedImmersion i],
      (ell : Γ(Z, ⊤)) = 0 →
      Scheme.IsConstructibleSheaf ((upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :
    Scheme.IsConstructibleEtaleModuleSheaf F := by
  let U := S.basicOpen (ell : Γ(S, ⊤))
  let I := Scheme.IdealSheafData.ofIdealTop (Ideal.span {(ell : Γ(S, ⊤))})
  let Z := I.subscheme
  have hunit (x : U.toScheme) : IsUnit (ell : U.toScheme.presheaf.stalk x) := by
    have hx := (S.mem_basicOpen_top (ell : Γ(S, ⊤)) (U.ι x)).mp x.2
    have hx' : IsUnit (ell : S.presheaf.stalk (U.ι x)) := by
      simpa only [map_natCast] using hx
    simpa only [map_natCast] using hx'.map (U.ι.stalkMap x).hom
  have hzero : (ell : Γ(Z, ⊤)) = 0 := by
    apply Z.IsSheaf.section_ext
    intro z hz
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (I.subschemeι z)) isOpen_univ
    refine ⟨I.subschemeι ⁻¹ᵁ V, le_top, hzV, ?_⟩
    have he : (ell : Γ(S, V)) ∈ I.ideal ⟨V, hV⟩ := by
      change (ell : Γ(S, V)) ∈
        (Ideal.span {(ell : Γ(S, ⊤))}).map (S.presheaf.map (homOfLE le_top).op).hom
      simpa only [map_natCast] using Ideal.mem_map_of_mem
        (S.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
        (Ideal.subset_span (Set.mem_singleton (ell : Γ(S, ⊤))))
    have hk := (I.ker_subschemeι_app ⟨V, hV⟩).symm ▸ he
    simpa using (RingHom.mem_ker.mp hk)
  have hcomp : Set.range I.subschemeι.base = (Set.range U.ι.base)ᶜ := by
    rw [I.range_subschemeι, Scheme.Opens.range_ι]
    simp [I, U, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mpr
  apply (Scheme.isConstructibleSheaf_iff_upperStar U.ι I.subschemeι hcomp F).mpr
  exact ⟨hopen U.toScheme U.ι hunit, hclosed Z I.subschemeι hzero⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def higherDirectImage_forget_iso
    (R : Type (u + 1)) [CommRing R] {X S : Scheme.{u}}
    (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ) :
    (moduleAbelianForget R S).obj (higherDirectImage R f q F) ≅
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((moduleAbelianForget R X).obj F))) := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  exact ((moduleAbelianForget R S).mapDerivedCategoryPlusHomologyFunctorIso
      (q : ℤ)).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((moduleAbelianDerivedLowerStarIso R f).app K ≪≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
          (((moduleAbelianForget R X).mapDerivedCategoryPlusSingleFunctor 0).app F))

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem prime_invertible_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime]
    (hunit : ∀ s : S, IsUnit (p : S.presheaf.stalk s)) (q : ℕ) :
    Scheme.IsConstructibleSheaf (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
      ((constantSheaf C.smallEtaleTopology _).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) := by
  have : IsNoetherian S := ⟨⟩
  let R := ULift.{u + 1} (ZMod p)
  let M := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R R)
  let G := higherDirectImage R f q M
  have : Scheme.IsLocallyConstantSheaf M :=
    (Sheaf.isConstant_of_iso _ (Iso.refl M)).isLocallyConstantSheaf
  obtain ⟨𝒰, h𝒰⟩ :=
    Scheme.finiteLocallyConstant_of_finite_stalks_of_bijective_specialization G
      (fun Ω _ _ s ↦ prime_constant_stalk_finite f hdim p q Ω s) (by
        intro Ω Ξ _ _ _ _ s t
        exact bijective_moduleSpecialization_of_abelianIso G _
          (higherDirectImage_forget_iso R f M q) s t
          (isIso_strictLocalSpecialization_smooth_proper_prime f p hunit M q s t))
  let d : Scheme.LocallyConstantDatum G :=
    ⟨𝒰, fun i ↦ by
      obtain ⟨E, -, ⟨e⟩⟩ := h𝒰 i
      exact Sheaf.isConstant_of_iso _ e⟩
  have : Scheme.IsFiniteLocallyConstantSheaf G :=
    (Scheme.finite_locally_constant_module_values_iff G).1.mp ⟨d, h𝒰⟩
  exact ⟨Scheme.Stratification.trivial S, fun _ ↦
    Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 S) G⟩


open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem prime_charP_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) (q : ℕ) :
    Scheme.IsConstructibleSheaf (higherDirectImage (ULift.{u + 1} (ZMod p)) f q
      ((constantSheaf C.smallEtaleTopology _).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) := by
  classical
  by_cases hq0 : q = 0
  · subst q
    exact higherDirectImage_zero_constant_constructible f _
  by_cases hq1 : q = 1
  · subst q
    by_cases hS : Nonempty S
    · let _ := hS
      obtain ⟨z⟩ := hS
      have : Nontrivial Γ(S, ⊤) :=
        (S.presheaf.germ ⊤ z (by trivial)).hom.domain_nontrivial
      have : CharP Γ(S, ⊤) p :=
        (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      let k := ULift.{u} (ZMod p)
      let a : S ⟶ Spec (.of k) := S.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          ((ZMod.castHom (dvd_refl p) Γ(S, ⊤)).comp ULift.ringEquiv.toRingHom))
      let _ : S.Over (Spec (.of k)) := ⟨a⟩
      obtain ⟨E, hE, hQ, F, hF, ⟨e⟩⟩ :=
        exists_prime_curve_artinSchreier_kernel f hdim p hp
      have := hE
      have := hQ
      have hkernel := (Scheme.frobenius_vectorBundle_kernel_constructible p S E F hF).2
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (Scheme.isConstructibleEtaleModuleSheaf_of_abelianIso p _ _ e hkernel)
    · have : IsEmpty S := not_nonempty_iff.mp hS
      exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  · exact Scheme.IsConstructibleSheaf.of_isZero
      (prime_higherDirectImage_zero_of_charP f hdim p hp q (by omega))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In a proper smooth family with nonempty geometrically connected one-dimensional
fibres over a Noetherian base, every nonnegative higher direct image of the constant
prime-field module sheaf is constructible. No invertibility of the prime is assumed.
`GeometricallyConnected f` includes nonemptiness. Dimension is measured on residue-field
fibres; field extension preserves their dimension, so this is the geometric fibre condition.
The lift of `ZMod ell` places the same finite prime field in the coefficient universe.

Source: Stacks Project, more-etale.tex, Tag 0GKV, lemma-proper-smooth-family-curves.
(blueprint: lem-weil-pbc-proper-smooth-curves-prime-coefficients)

Proof: Split the base into the basic open D(ell) and the closed subscheme V(ell).
The universal base-change isomorphism for torsion coefficients identifies each
restriction with the corresponding prime-coefficient direct image. Smooth relative
dimension one and geometric connectedness persist. On D(ell), the proved geometric
stalk finiteness lemma and smooth proper specialization, transported by the module/
abelian comparison, give finite local constancy by the specialization criterion.
On V(ell), degree zero is constant by connected-fibre section descent and degrees
above one vanish by the Artin--Schreier curve dimension theorem and proper base
change. Degree one is the Frobenius fixed-point kernel on the first structure
cohomology bundle. The vector-bundle fixed-point theorem gives finite abelian
constructible charts, and the cyclic-module chart comparison lifts them to module
charts. The proved open--closed constructibility theorem glues these two cases.
The full scheme structure on V(ell) ensures ell = 0 even in the presence of nilpotents.
-/
theorem properSmoothCurves_prime_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (ell : ℕ) [Fact ell.Prime] (q : ℕ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ell)) (ULift.{u + 1} (ZMod ell))))))) := by
  have : IsNoetherian S := ⟨⟩
  let R := ULift.{u + 1} (ZMod ell)
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R R)
  change Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage R f q F)
  apply prime_restriction_glue (higherDirectImage R f q F) ell
  · intro U j _ hunit
    have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
    have : TopologicalSpace.NoetherianSpace U :=
      j.isOpenEmbedding.isInducing.noetherianSpace
    have : CompactSpace U := inferInstance
    have h := prime_invertible_constructible (Limits.pullback.snd f j)
      (curve_fiber_dimension_baseChange f h_dim j) ell hunit q
    exact Scheme.IsConstructibleSheaf.of_iso
      (constant_baseChange_iso R (fun z ↦ isOfFinAddOrder_of_finite z)
        f j q (ModuleCat.of R R)).symm
  · intro Z i _ hzero
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isInducing.noetherianSpace
    have : CompactSpace Z := inferInstance
    have h := prime_charP_constructible (Limits.pullback.snd f i)
      (curve_fiber_dimension_baseChange f h_dim i) ell hzero q
    exact Scheme.IsConstructibleSheaf.of_iso
      (constant_baseChange_iso R (fun z ↦ isOfFinAddOrder_of_finite z)
        f i q (ModuleCat.of R R)).symm

end AlgebraicGeometry.Etale
