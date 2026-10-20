/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import Mathlib.AlgebraicGeometry.AffineScheme

import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! # Bottom models on a universally free degree-zero locus

Source: Stacks Project, Tags 0BDL, 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open SheafOfModules Modules Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unit_hom_eq_zero_of_top {Y : Scheme.{u}} {M : Y.Modules}
    (f : Modules.unit Y ⟶ M) (hf : Modules.Hom.app f ⊤ (1 : Γ(Y, ⊤)) = 0) : f = 0 := by
  apply Modules.hom_ext
  intro V
  ext x
  have hnat := ConcreteCategory.congr_hom
    ((Modules.Hom.mapPresheaf f).naturality (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(Y, ⊤))
  have hn : (Modules.unit Y).presheaf.map
      (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(Y, ⊤)) = (1 : Γ(Y, V)) := by
    change Y.presheaf.map _ 1 = 1
    exact map_one _
  change Modules.Hom.app f V ((Modules.unit Y).presheaf.map
      (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(Y, ⊤))) =
    M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (Modules.Hom.app f ⊤ (1 : Γ(Y, ⊤))) at hnat
  have h1 : Modules.Hom.app f V (1 : Γ(Y, V)) = 0 := by
    simpa only [hn, hf, map_zero] using hnat
  have hlin := Modules.Hom.app_smul f (U := V) x (1 : Γ(Y, V))
  simpa [h1] using hlin

private theorem free_hom_eq_zero_of_top {Y : Scheme.{u}} {I : Type u} {M : Y.Modules}
    (f : free (R := Y.ringCatSheaf) I ⟶ M)
    (hf : ∀ x, Modules.Hom.app f ⊤ x = 0) : f = 0 := by
  apply Modules.free_hom_ext
  intro i
  rw [comp_zero]
  apply unit_hom_eq_zero_of_top
  exact hf _

private theorem free_comp_eq_zero_of_mono {Y : Scheme.{u}} (r m : ℕ)
    (f : free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ free (ULift.{u} (Fin r)))
    [Mono f]
    (g : free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ free (ULift.{u} (Fin m)))
    (hfg : f ≫ g = 0) : g = 0 := by
  classical
  let I := ULift.{u} (Fin r)
  let J := ULift.{u} (Fin m)
  let A := freeMatrix f
  let G := freeMatrix g
  have hf : Function.Injective (Modules.Hom.app f ⊤) := by
    exact (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)).map f)).mp inferInstance
  have hA : Function.Injective A.mulVec := by
    intro x y hxy
    apply (freeSectionsEquiv (X := Y) I).symm.injective
    apply hf
    apply (freeSectionsEquiv (X := Y) I).injective
    rw [freeSectionsEquiv_app (X := Y) f, freeSectionsEquiv_app (X := Y) f]
    simpa only [I, A, LinearEquiv.apply_symm_apply] using hxy
  have hAt : Function.Injective A.vecMul :=
    Matrix.vecMul_injective_iff.mpr
      (Matrix.linearIndependent_col_iff_row.mp (Matrix.mulVec_injective_iff.mp hA))
  have hG : G = 0 := by
    ext j i
    have hrow : A.vecMul (G j) = A.vecMul 0 := by
      ext k
      have h := congrArg (fun φ ↦ (freeSectionsEquiv (X := Y) J)
        (Modules.Hom.app φ ⊤
          ((freeSectionsEquiv (X := Y) I).symm (Pi.single k 1)))) hfg
      change (freeSectionsEquiv (X := Y) J)
        (Modules.Hom.app g ⊤ (Modules.Hom.app f ⊤
          ((freeSectionsEquiv (X := Y) I).symm (Pi.single k 1)))) =
        (freeSectionsEquiv (X := Y) J) 0 at h
      rw [freeSectionsEquiv_app (X := Y) g, freeSectionsEquiv_app (X := Y) f,
        LinearEquiv.apply_symm_apply, map_zero] at h
      have hk := congrFun h j
      simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, A, G, Pi.single_apply,
        mul_ite] using hk
    exact congrFun (hAt hrow) i
  apply free_hom_eq_zero_of_top
  intro x
  apply (freeSectionsEquiv (X := Y) J).injective
  rw [map_zero, freeSectionsEquiv_app (X := Y) g]
  change G *ᵥ _ = 0
  rw [hG, Matrix.zero_mulVec]

/-- If a complex has no incoming term in degree zero and both its zeroth term and
zeroth cohomology are free of rank r, its outgoing differential to a finite free term vanishes.

Source: Stacks Project, Tag 0BDL, matrix-chart proof; Tag 0EWY,
More on Algebra, Lemma coker-injective-free.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).

Proof: The vanishing of B.X (-1) makes the incoming differential zero. Consequently
H0(B) is the kernel of d0, with its canonical monomorphism into B.X 0. Use the given
free trivializations of the cohomology and of B.X 0. Under the equivalence from the
localized site to U.toScheme this monomorphism is a square r-by-r matrix A over the
commutative ring of sections, whose multiplication map is injective. By Tag 0EWY,
or Matrix.linearIndependent_col_iff_row combined with the two multiplication-map
injectivity criteria, its transpose is injective. Every coordinate row of d0
annihilates A since the kernel inclusion composed with d0 is zero. Transpose
injectivity therefore makes each coordinate row zero. The finite-free target has
separating coordinates, so d0 is zero on this open. Faithfulness of the open-site
equivalence gives d0 = 0 on the localized site.
When r = 0 the source is zero and the result follows directly; the argument also
allows a zero-rank target and the empty open. No reducedness assumption is used. -/
private theorem finiteFree_bottom_differential_eq_zero
    (S : Scheme.{u}) (U : S.Opens)
    (B : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hprev : IsZero (B.X (-1))) (r m : ℕ)
    (hzero : Nonempty (B.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hone : Nonempty (B.X 1 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))))
    (hH : Nonempty (B.homology 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r)))) :
    B.d 0 1 = 0 := by
  classical
  let ep := B.pOpcyclesIso (-1) 0 (by simp) (hprev.eq_of_src _ 0)
  let f : B.homology 0 ⟶ B.X 0 := B.homologyι 0 ≫ ep.inv
  have : Mono f := by dsimp [f]; infer_instance
  have hfd : f ≫ B.d 0 1 = 0 := by
    have hd : ep.inv ≫ B.d 0 1 = B.fromOpcycles 0 1 := by
      apply (cancel_epi ep.hom).mp
      simp only [Iso.hom_inv_id_assoc]
      exact (B.p_fromOpcycles 0 1).symm
    dsimp only [f]
    rw [Category.assoc, hd, B.homologyι_comp_fromOpcycles]
  let F := (Modules.overEquiv U).functor
  let I := ULift.{u} (Fin r)
  let J := ULift.{u} (Fin m)
  let er : F.obj (free (R := (moduleRings S.toRingedSpace).over U) I) ≅
      free (R := U.toScheme.ringCatSheaf) I :=
    (SheafOfModules.mapFreeIso F I (Modules.overEquivFunctorObjUnitIso U)).symm
  let em : F.obj (free (R := (moduleRings S.toRingedSpace).over U) J) ≅
      free (R := U.toScheme.ringCatSheaf) J :=
    (SheafOfModules.mapFreeIso F J (Modules.overEquivFunctorObjUnitIso U)).symm
  let eH := F.mapIso hH.some ≪≫ er
  let e0 := F.mapIso hzero.some ≪≫ er
  let e1 := F.mapIso hone.some ≪≫ em
  let f' := eH.inv ≫ F.map f ≫ e0.hom
  let g' := e0.inv ≫ F.map (B.d 0 1) ≫ e1.hom
  have : Mono f' := by dsimp [f']; infer_instance
  have hfg : f' ≫ g' = 0 := by
    simp only [f', g', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, hfd, F.map_zero, zero_comp, comp_zero]
  have hg : g' = 0 := free_comp_eq_zero_of_mono r m f' g' hfg
  apply F.map_injective
  rw [F.map_zero]
  apply (cancel_epi e0.inv).mp
  apply (cancel_mono e1.hom).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using hg



private theorem betti_zero_eq_rank
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u}) (K : schemeDerivedCategory S) (s : S)
    (U : S.Opens) (hs : s ∈ U) (r : ℕ)
    (hfree : ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((derivedPullback (k ≫ U.ι)).obj K)) r) :
    derivedFiberBetti S K 0 s = r := by
  classical
  let g := S.fromSpecResidueField s
  have hg : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hs
  let k := IsOpenImmersion.lift U.ι g hg
  have hk : k ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).obj
      ((derivedPullback g).obj K)
  have hH : H.IsFiniteLocallyFreeOfRank r := by
    simpa only [hk] using hfree _ k
  let := hH
  obtain ⟨I, V, hV, e⟩ := Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free H (r := r)
  obtain ⟨x⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, V i by rw [hV]; trivial)
  have htop : V i = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    simpa only [Subsingleton.elim y x] using hi
  have ei := (e i).some
  rw [htop] at ei
  have : IsIso (⊤ : (Spec (S.residueField s)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (S.residueField s)).topIso.hom)
  let eH := Modules.isoFreeOfRestrictIso H _ ei
  have hr := (Modules.finrank_moduleSpecΓFunctor_obj_free
    (Field.toIsField (S.residueField s)) eH).1
  let eV : derivedFiberCohomology S K 0 s ≃ₗ[S.residueField s]
      ((moduleSpecΓFunctor (R := S.residueField s)).obj H) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact eV.finrank_eq.trans (by simpa only [Fintype.card_ulift, Fintype.card_fin] using hr)

private noncomputable def restrictFreeIso (S : Scheme.{u}) (U V : S.Opens)
    (hVU : V ≤ U) (r : ℕ) :
    (SheafOfModules.overMap (moduleRings S.toRingedSpace) (homOfLE hVU)).obj
      (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin r))) ≅
      SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
  (asIso (sigmaComparison
    (SheafOfModules.overMap (moduleRings S.toRingedSpace) (homOfLE hVU))
    (fun _ : ULift.{u} (Fin r) ↦
      SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)))).symm ≪≫
    Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso (homOfLE hVU))

/-- A finite-free residue-rank model can be refined so that its zeroth cohomology
is free of the same rank as its zeroth term. No vanishing hypothesis is needed.

Source: Stacks Project, Tag 0BDL, proof on the rank-r charts; Tag 0BCD.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).

Proof: Choose U0 and r from hloc at s. The residue morphism from Spec kappa(s)
factors through U0. The corresponding test in hloc identifies the dimension of
H0 of the derived fibre with r: on the spectrum of a field a rank-r locally free
sheaf has r-dimensional global sections, with scalars transported by GammaSpecIso.
Thus derivedFiberBetti S K 0 s = r. The identity test on U0 gives H0 of the
derived pullback along U0.ι locally free of rank r. The derived open-pullback
homology comparison identifies it with the restriction of H0(K). Choose a
trivializing neighbourhood of s there and transfer it to its image O in S.
Choose an affine neighbourhood V of s inside U intersect O. Restrict B to V
using exact restriction of module sheaves between the localized sites. This
preserves the bounds and sends each finite free term to a free term on the same
index set. The composition comparison for restriction transports e to the
derived isomorphism on V. Exact restriction commutes with homology, so the free
trivialization of H0(K) on O identifies B'.homology 0 with a free rank-r sheaf
on V. Replace r by the equal Betti number to obtain the conclusion.
No differential is required to vanish, and no negative cohomology or
perfectness assumption is used beyond the given model. The point assumption makes
both relevant residue fields nonzero; no point exists on the empty scheme. -/
private theorem finiteFreeResidueModel_rank_refinement
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (s : S)
    (hloc : ∀ t : S, ∃ U : S.Opens, t ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (U : S.Opens) (hs : s ∈ U) (_hU : IsAffineOpen U)
    (B : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (B.X i))
    (hrank : ∀ i : ℤ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U)
      (ULift.{u} (Fin (derivedFiberBetti S K i s)))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj B) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      ∃ B' : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (B'.X i)) ∧
        (∀ i : ℤ, Nonempty (B'.X i ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over V)
          (ULift.{u} (Fin (derivedFiberBetti S K i s))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) V).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj B') ∧
        Nonempty (B'.homology 0 ≅ SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over V)
          (ULift.{u} (Fin (derivedFiberBetti S K 0 s)))) := by
  classical
  obtain ⟨U0, hs0, r, hfree⟩ := hloc s
  have hr : derivedFiberBetti S K 0 s = r := betti_zero_eq_rank S K s U0 hs0 r hfree
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj K
  let N := (Modules.restrictFunctor U0.ι).obj H
  have hN : N.IsFiniteLocallyFreeOfRank r := by
    have h0 := hfree U0.toScheme (𝟙 _)
    simp only [Category.id_comp] at h0
    let := h0
    obtain ⟨e0⟩ := Modules.nonempty_homology_derivedOpenPullback_iso_restrict U0 K 0
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e0
  let := hN
  obtain ⟨I, W, hW, eW⟩ := Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free N
    (r := r)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show (⟨s, hs0⟩ : U0) ∈ ⨆ i, W i by rw [hW]; trivial)
  let O := U0.ι ''ᵁ W i
  let eO := U0.ι.isoImage (W i)
  have fac : eO.inv ≫ (W i).ι ≫ U0.ι = O.ι := by
    rw [← Category.assoc, U0.isoImage_ι_inv_ι]
    exact S.homOfLE_ι _
  let Hfree : (Modules.restrictFunctor O.ι).obj H ≅
      SheafOfModules.free (R := O.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (Modules.restrictFunctorCongr fac).symm.app H ≪≫
      (Modules.restrictFunctorComp eO.inv ((W i).ι ≫ U0.ι)).app H ≪≫
      (Modules.restrictFunctor eO.inv).mapIso
        ((Modules.restrictFunctorComp (W i).ι U0.ι).app H ≪≫ (eW i).some) ≪≫
      Modules.restrictFreeIso eO.inv _
  let HfreeOver := (Modules.overIsoFreeEquiv H O (ULift.{u} (Fin r))).symm Hfree
  have hsO : s ∈ O := ⟨⟨s, hs0⟩, hi, rfl⟩
  obtain ⟨V, hV, hsV, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ O) ⟨hs, hsO⟩
  have hVU : V ≤ U := hsub.trans inf_le_left
  have hVO : V ≤ O := hsub.trans inf_le_right
  let F := SheafOfModules.overMap (moduleRings S.toRingedSpace) (homOfLE hVU)
  let FO := SheafOfModules.overMap (moduleRings S.toRingedSpace) (homOfLE hVO)
  let G := SheafOfModules.overFunctor (moduleRings S.toRingedSpace) U
  let GV := SheafOfModules.overFunctor (moduleRings S.toRingedSpace) V
  let B' := (F.mapHomologicalComplex (.up ℤ)).obj B
  have : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits _ _
  let e' : GV.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj B' :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap (moduleRings S.toRingedSpace)
        (homOfLE hVU))).symm.app K ≪≫
      (Functor.mapDerivedCategoryCompIso G F).app K ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app B
  let HfreeV : GV.obj H ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
    (SheafOfModules.overFunctorMap (moduleRings S.toRingedSpace)
      (homOfLE hVO)).symm.app H ≪≫ FO.mapIso HfreeOver ≪≫ restrictFreeIso S O V hVO r
  let eH : GV.obj H ≅ B'.homology 0 :=
    (GV.mapDerivedCategoryHomologyFunctorIso 0).app K ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso e' ≪≫
      (DerivedCategory.homologyFunctorFactors _ 0).app B'
  refine ⟨V, hsV, hV, B', ?_, ?_, ⟨e'⟩, ?_⟩
  · obtain ⟨a, b, hb⟩ := hb
    exact ⟨a, b, fun i hi ↦ F.map_isZero (hb i hi)⟩
  · intro i
    exact ⟨F.mapIso (hrank i).some ≪≫
      restrictFreeIso S U V hVU (derivedFiberBetti S K i s)⟩
  · rw [hr]
    exact ⟨eH.symm ≪≫ HfreeV⟩


/-- A perfect complex with universally vanishing negative cohomology and locally
universally free degree-zero cohomology has an affine strictly perfect bottom model.
Source: Stacks Project, Tag 0BDL, matrix-chart proof; Tags 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).

Proof: Choose the universally rank-r neighbourhood of s and test the hypotheses
at Spec kappa(s). Tag 0BCD gives a bounded finite-free model with ranks the fibre
cohomology dimensions. Shrink its affine neighbourhood inside the chosen open.
The negative ranks are zero and the degree-zero rank is r. Exact restriction
and its comparison with derived pullback identify the kernel of d0 with H0(K)
on this chart. The identity test makes that kernel locally free of rank r.
Trivialize it after a further affine shrinking. Its inclusion into the free
rank-r degree-zero term is an injective square matrix. Tag 0EWY says that its
transpose is injective, so the dual of its cokernel vanishes. Each coordinate
of d0 factors through this cokernel and therefore is zero. This proves d0=0
without a reducedness hypothesis. Restricting the model preserves boundedness
and finite freeness and gives the required derived isomorphism. At rank zero
the degree-zero term and differential are zero. There are no points to treat
on an empty scheme. No source module or arrow is part of this assertion. -/
theorem perfect_universalH0_bottom_model
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPerfect S K)
    (hnegative : ∀ (Y : Scheme.{u}) (k : Y ⟶ S) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)))
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      ∃ B : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect S U B ∧
        (∀ i : ℤ, i < 0 → IsZero (B.X i)) ∧ B.d 0 1 = 0 ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj B) := by
  have hbettiNegative : ∀ i : ℤ, i < 0 → derivedFiberBetti S K i s = 0 := by
    intro i hi
    let F := SheafOfModules.evaluation
      (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤)
    have hz : IsZero (F.obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
          ((derivedPullback (S.fromSpecResidueField s)).obj K))) := by
      rw [IsZero.iff_id_eq_zero, ← F.map_id,
        (hnegative _ (S.fromSpecResidueField s) i hi).eq_of_src (𝟙 _) 0]
      exact F.map_zero _ _
    have hs := ModuleCat.isZero_iff_subsingleton.mp hz
    let : Subsingleton (derivedFiberCohomology S K i s) := hs
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨_, _, U, hs, hU, B, hb, hrank, ⟨e⟩⟩ :=
    exists_finiteFreeResidueModel S K hK s
  obtain ⟨V, hsV, hV, B', hb', hrank', he', hH⟩ :=
    finiteFreeResidueModel_rank_refinement S K s hloc U hs hU B hb hrank e
  have hB' : IsStrictlyPerfect S V B' := by
    refine ⟨hb', fun i ↦ ?_⟩
    obtain ⟨ei⟩ := hrank' i
    exact ⟨derivedFiberBetti S K i s, ei.hom, ei.inv, ei.hom_inv_id⟩
  have hnegative' : ∀ i : ℤ, i < 0 → IsZero (B'.X i) := by
    intro i hi
    obtain ⟨ei⟩ := hrank' i
    have hfree : IsZero (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over V)
        (ULift.{u} (Fin (derivedFiberBetti S K i s)))) := by
      rw [hbettiNegative i hi, IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext j
      exact Fin.elim0 j.down
    exact hfree.of_iso ei
  refine ⟨V, hsV, hV, B', hB', hnegative', ?_, he'⟩
  exact finiteFree_bottom_differential_eq_zero S V B' (hnegative' (-1) (by decide))
    (derivedFiberBetti S K 0 s) (derivedFiberBetti S K 1 s) (hrank' 0) (hrank' 1) hH

end AlgebraicGeometry.Scheme
