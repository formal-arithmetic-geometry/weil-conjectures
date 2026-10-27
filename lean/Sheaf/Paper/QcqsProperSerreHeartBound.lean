/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NP and N4
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import Sheaf.Paper.ProperWContractibleClosedFibreRigidity
import Sheaf.Paper.ProfiniteGeometricFamilyHeartCd
import all Sheaf.Paper.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact

/-!
# A uniform proper bound on the constructible weak Serre coproduct heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-serre-heart-bound).

The coefficient hypothesis spells out the five coefficient families A, Z_l, O_E, Q_l, E.
The closure uses finite constant scalar models and coproducts indexed in `Type (u + 1)`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] upperStar upperStarFromPoint
  upperStarComp upperStarLowerStarAdjunction

/-- Exact pullback preserves the generated heart class on qcqs schemes. -/
private theorem pullback_heart {T X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T] [QuasiSeparatedSpace T]
    (a : T ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ T) ((upperStar Λ a).obj M) := by
  let F := upperStar Λ a
  let P := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible Λ T)
  let Q := P.inverseImage F
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    (upperStarLowerStarAdjunction Λ a).leftAdjoint_preservesColimits
  refine hM Q (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _ ?_)
    inferInstance inferInstance inferInstance inferInstance (fun _ ↦ inferInstance)
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hN ⊢
  exact AlgebraicGeometry.ProEtale.stratified_pullback Λ a N hN

/-- The uniform ordinary-fibre bound also bounds fibres over arbitrary fields. -/
private theorem geometric_dimension_bound {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (K : Type u) [Field K] (c : Spec (CommRingCat.of K) ⟶ Y) :
    topologicalKrullDim (pullback f c : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective c
  let i := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) (Spec.map t)
  have hi := IsHomeomorph.topologicalKrullDim_eq _ i.hom.homeomorph.isHomeomorph
  exact hi.symm.le.trans
    ((topologicalKrullDim_pullback_le_of_field (k := Y.residueField y) _ _).trans (he y))

omit [IsCommMonObj Λ] in
/-- W-contractible abelian evaluation remains exact after forgetting the module action. -/
private theorem evaluation_exact {Y : Scheme.{u}}
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w] :
    PreservesFiniteLimits (closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w)) ∧
      PreservesFiniteColimits (closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w)) := by
  obtain ⟨hl, hc, _, _⟩ := Scheme.ProEt.wContractible_sections_exact.{u, u + 1, u + 1}
    Y R w ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1} R)))
  let ev := (sheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}).obj
    (Opposite.op (Scheme.ProEt.mk w))
  have : PreservesFiniteLimits ev := hl
  have : PreservesFiniteColimits ev := hc
  exact ⟨comp_preservesFiniteLimits (Mod.forget (condensedRingObj Λ Y)) ev,
    comp_preservesFiniteColimits (Mod.forget (condensedRingObj Λ Y)) ev⟩

/-- Evaluate direct image using the symmetry of the two orders of fibre product. -/
private noncomputable def evaluation_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w] :
    lowerStar Λ f ⋙ closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w) ≅
      closedFibreModuleEvaluation Λ X (Scheme.ProEt.mk (pullback.fst f w)) := by
  let i : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      (Scheme.ProEt.mk w) ≅ Scheme.ProEt.mk (pullback.fst f w) :=
    MorphismProperty.Over.isoMk (pullbackSymmetry w f) (by simp; rfl)
  exact NatIso.ofComponents (fun M ↦ M.X.obj.mapIso i.symm.op) (by
    intro M N t
    exact (t.hom.hom.naturality _).symm)

/-- Exact target evaluation commutes with derived pushforward and homology. -/
private noncomputable def derived_evaluation_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (r : ℤ) :
    (closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w)).obj
      ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward Λ f).obj K)) ≅
      (DerivedCategory.homologyFunctor _ r).obj
        ((closedFibreModuleEvaluation Λ X
          (Scheme.ProEt.mk (pullback.fst f w))).rightDerivedFunctor.obj K) := by
  let E := closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w)
  have : PreservesFiniteLimits E := (evaluation_exact Λ R w).1
  have : PreservesFiniteColimits E := (evaluation_exact Λ R w).2
  exact (E.mapDerivedCategoryHomologyFunctorIso r).app
      ((lowerStar Λ f).rightDerivedFunctor.obj K) ≪≫
    (DerivedCategory.homologyFunctor _ r).mapIso
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso (lowerStar Λ f) E).symm.app K ≪≫
        (Functor.rightDerivedFunctorNatIso (evaluation_pushforward Λ f R w)).app K)

omit [IsCommMonObj Λ] in
/-- Affine w-contractible tests jointly detect zero module sheaves. -/
private theorem zero_of_evaluation {Y : Scheme.{u}}
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hN : ∀ (R : Type u) [CommRing R] [IsWContractibleRing R]
      (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w],
      IsZero ((closedFibreModuleEvaluation Λ Y (Scheme.ProEt.mk w)).obj N)) :
    IsZero N := by
  have hW (W : Y.ProEt) (D : CommRingCat.{u}) [IsWContractibleRing D]
      (e : Spec D ≅ W.left) : IsZero (N.X.obj.obj (Opposite.op W)) := by
    let w := e.hom ≫ W.hom
    have : WeaklyEtale w := by dsimp [w]; infer_instance
    let i : Scheme.ProEt.mk w ≅ W := MorphismProperty.Over.isoMk e rfl
    exact (hN D w).of_iso (N.X.obj.mapIso i.op)
  have hz : IsZero N.X := by
    apply Sheaf.isZero_of_isZero_obj
    intro V
    suffices hs : Subsingleton (N.X.obj.obj V) from
      @AddCommGrpCat.isZero_of_subsingleton _ hs
    constructor
    intro x y
    obtain ⟨I, W, f, hcover, hW'⟩ := (Scheme.ProEt.weaklyContractible_basis Y).1 V.unop
    apply Sheaf.isSeparated N.X V.unop _
      (Precoverage.generate_mem_toGrothendieck hcover) x y
    rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
    obtain ⟨D, hD, ⟨e⟩⟩ := hW' i
    have := hD
    have hs := AddCommGrpCat.subsingleton_of_isZero (hW (W i) D e)
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rw [hs.elim (N.X.obj.map (f i).op x) (N.X.obj.map (f i).op y)]
  rw [IsZero.iff_id_eq_zero]
  apply Mod.hom_ext
  exact hz.eq_of_src _ _

/-- Proper direct image is uniformly bounded above on the weak Serre coproduct closure
of finite constant-model constructible heart objects over a qcqs base.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-serre-heart-bound).

Proof:
1. Properness makes Y and X qcqs. The finite-type fibre-dimension theorem gives
   a uniform bound e for ordinary fibres. The dimension inequality for field base
   change bounds every geometric fibre by e as well. Set d = 2e + 2.
2. Exact pullback preserves coproducts, and carries finite constant-model
   stratifications to such stratifications. The inverse image of the weak Serre
   coproduct class therefore has all its defining closure properties.
3. Test the desired homology module on an affine w-contractible object Spec R → Y.
   Proper closed-fibre rigidity compares derived evaluation over this test with
   derived sections on the base change to Spec(R / Jac(0)). This closed fibre is
   affine, reduced, zero-dimensional and w-contractible, with separably closed
   residue fields. Its geometric fibres still have dimension at most e.
4. Apply the profinite geometric-family cohomological bound to the pulled-back
   heart object. Cohomology above 2e + 2 of these derived sections vanishes.
5. Abelian evaluation on an affine w-contractible test is exact; forgetting the
   module action is exact too. Thus evaluation commutes with homology and with
   right derivation of pushforward. The underived evaluation comparison uses the
   symmetry of the two pullback orders. Consequently the desired homology module
   evaluates to zero on every such test. These tests form a covering basis; sheaf
   separatedness makes its underlying sheaf zero, hence the module itself is zero.
-/
theorem exists_uniform_serreHeart_bound_of_isProper
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
    {S Y X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f] :
    ∃ d : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible Λ X) M →
      ∀ r : ℤ, (d : ℤ) < r →
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward Λ f).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e, he⟩ := exists_fibre_dimension_bound f
  refine ⟨2 * e + 2, ?_⟩
  intro M hM r hr
  apply zero_of_evaluation Λ
  intro R _ _ w _
  let C := wContractibleClosedPointScheme R
  let b := wContractibleClosedPointImmersion R ≫ w
  let Z := pullback f b
  let a : Z ⟶ X := pullback.fst f b
  let h : Z ⟶ C := pullback.snd f b
  obtain ⟨hCa, hCr, hCd, hCw, hCres, _, _, hrig⟩ :=
    proper_wContractible_closedFibre_rigidity Λ ℓ hΛ f R w
  have : IsAffine C := hCa
  have : IsReduced C := hCr
  have : IsWContractibleRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)) := hCw
  let er := (Scheme.ΓSpecIso (CommRingCat.of
    (R ⧸ Ideal.jacobson (⊥ : Ideal R)))).commRingCatIsoToRingEquiv
  have : IsWContractibleRing Γ(C, ⊤) := RingHom.wContractible_of_ringEquiv er.symm
  have hdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal := by
    intro p
    have hm := hCd (PrimeSpectrum.comap er.symm.toRingHom p)
    exact (Ideal.isMaximal_comap_iff_of_bijective er.symm.toRingHom er.symm.bijective).mp hm
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace h
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated h
  have hgeom (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C) :
      topologicalKrullDim (pullback h c : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
    let i := pullbackLeftPullbackSndIso f b c
    exact (IsHomeomorph.topologicalKrullDim_eq _ i.hom.homeomorph.isHomeomorph).le.trans
      (geometric_dimension_bound f e he K (c ≫ b))
  have hv := profinite_geometric_family_serreHeart_cohomology_vanishes ℓ Λ hΛ
    hdim hCres h e hgeom ((upperStar Λ a).obj M) (pullback_heart Λ a M hM) r
    (by exact_mod_cast hr)
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have := hrig M hM
  let i := asIso ((properClosedFibreDerivedRestriction Λ f R w).app K)
  let j := (condensedModuleSections Λ Z).rightDerivedFunctor.mapIso
    (((upperStar Λ a).mapDerivedCategorySingleFunctor 0).app M)
  exact (hv.of_iso ((DerivedCategory.homologyFunctor _ r).mapIso (i ≪≫ j))).of_iso
    (derived_evaluation_pushforward Λ f R w K r)

end AlgebraicGeometry.ProEtale.CondensedRing
