/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyFinite
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Constructible ranks of ordinary direct images on fibres

Source: Stacks Project, Tags 0B91(2) and 0BDI(3).
(blueprint: lem-sc-picard-fiber-direct-image-rank-constructible).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Affine sections are projective over X and flat over the flat base S. -/
private theorem finiteLocallyFree_isFlatOver {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] (E : X.Modules) [E.IsFiniteLocallyFree] :
    E.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat f ‹_› V U e
  have := (Modules.finitePresentation_projective_sections E U.2).2
  let : Module Γ(S, V.1) Γ(E, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(S, V.1) Γ(X, U.1) Γ(E, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(S, V.1) Γ(X, U.1) Γ(E, U.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical module base change identifies degree-zero fibre cohomology with
ordinary fibre pushforward. -/
private theorem fibre_homology_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Modules.tensorPullback k).Additive]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    [∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : X.Modules) [E.IsFiniteLocallyFree] (hflat : E.IsFlatOver f) (s : S) :
    Nonempty (derivedFiberCohomology S
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj E)) 0 s ≅
      (moduleSpecΓFunctor (R := S.residueField s)).obj
        ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E))) := by
  let g := S.fromSpecResidueField s
  let p := pullback.fst f g
  let q := pullback.snd f g
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hε, htri, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback p)
  have h : F = Modules.tensorPullback p :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let c := ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj E) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback p) (ComplexShape.up ℤ) 0).hom.app E))
  have hc : IsDerivedModulePullbackComparison p E c := ⟨ε, hε, rfl⟩
  let φ := schemeDerivedBaseChangeMap f q g p pullback.condition
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj E) ≫
    (schemeDerivedDirectImage q).map c
  have hφ : IsDerivedModuleBaseChangeMap f g E φ := ⟨c, hc, rfl⟩
  have : IsIso φ := (perfect_derivedDirectImage_baseChange f E hflat).2 g φ hφ
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0
  let P := RingedSpace.moduleDirectImage q.toLRSHom.toShHom
  have : PreservesFiniteLimits P := by
    change PreservesFiniteLimits (Modules.pushforward q)
    infer_instance
  let e := H.mapIso (asIso φ) ≪≫
    P.homologyRightDerivedFunctorObjSingleFunctorIso
      ((Modules.tensorPullback p).obj E) 0 ≪≫
    P.rightDerivedZeroIsoSelf.app ((Modules.tensorPullback p).obj E)
  let V := ModuleCat.restrictScalars (ΓSpecIso (S.residueField s)).inv.hom
  let Γ := SheafOfModules.evaluation
    (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤)
  exact ⟨(Γ ⋙ V).mapIso e⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rank-r locus of the ordinary direct image on residue-field fibres is
locally constructible. No rank condition on E along a whole fibre is required.
Source: Stacks Project, Tags 0B91(2) and 0BDI(3), as used in the second proof
paragraph of Tag 0BDP.
(blueprint: lem-sc-picard-fiber-direct-image-rank-constructible).

Proof:
1. E is finitely presented and flat over S: it is finite locally free on X and f
   is flat. Properness and local finite presentation give finite presentation of f.
   Apply perfect direct image and arbitrary base change (Tag 0B91(2)) to E.
2. On Spec kappa(s), its derived fibre has degree-zero cohomology equal to the
   ordinary direct image of E pulled back to X_s. This uses the canonical
   derived-to-ordinary pullback comparison and degree-zero direct-image identification.
3. A quasi-coherent module on the spectrum of a field is finite locally free of
   rank r exactly when its vector space of global sections has dimension r.
   The vector spaces here are finite dimensional by perfectness.
4. Consequently the displayed locus is the degree-zero Betti-number level set of
   Rf_*E. Perfect implies pseudo-coherent, and Tag 0BDI(3) makes this set locally
   constructible. On an empty fibre the vector space is zero, so such points occur
   precisely in the level r=0. -/
theorem picardFiberDirectImageRank_locallyConstructible {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    Topology.IsLocallyConstructible {s : S |
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r} := by
  classical
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Modules.tensorPullback k).Additive := by
    intro Y Z k
    let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction k)
    let : (Modules.tensorPullback k).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let K := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj E)
  have hflat := finiteLocallyFree_isFlatOver f E
  have hperfect : IsPerfect S K := (perfect_derivedDirectImage_baseChange f E hflat).1
  have hpseudo : IsPseudoCoherent S K := by
    intro s
    obtain ⟨U, hs, P, hP, hKP⟩ := hperfect s
    obtain ⟨V, hsV, _, _, F, ⟨a, b, hb⟩, hfree, hKF⟩ :=
      exists_finiteFree_refinement_of_isStrictlyPerfect S K U P hP hKP s hs
    exact ⟨V, hsV, F, ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩, hfree, hKF⟩
  have heq : {s : S |
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r} =
      {s : S | derivedFiberBetti S K 0 s = r} := by
    ext s
    obtain ⟨e⟩ := fibre_homology_iso f E hflat s
    have : Module.Finite (S.residueField s) (derivedFiberCohomology S K 0 s) :=
      finiteFiberCohomology S K s (hperfect s) 0
    have : Module.Finite (S.residueField s) _ :=
      Module.Finite.of_injective e.symm.toLinearEquiv.toLinearMap
        e.symm.toLinearEquiv.injective
    simp only [Set.mem_ofPred_eq]
    rw [Modules.isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj
      (Field.toIsField (S.residueField s)) _ r]
    exact (congrArg (· = r) e.toLinearEquiv.finrank_eq).symm.to_iff
  rw [heq]
  exact (pseudoCoherent_jump_loci S K hpseudo 0).2.2 r

end AlgebraicGeometry.Scheme
