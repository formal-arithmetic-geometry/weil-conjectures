/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleTensorFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import all Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Nonnegative perfect charts for an ordinary direct image

Source: Stacks Project, Tags 0BDP, second and third proof paragraphs, and 0B91(2).
(blueprint: lem-sc-proper-flat-direct-image-perfect-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A direct image has a locally bounded nonnegative perfect chart whose degree-zero
base changes compute ordinary direct images. A prescribed neighbourhood can be refined.
No reference bundle, rank, or universal rank predicate occurs in this statement.
Source: Stacks Project, Tags 0BDP, second and third proof paragraphs, and 0B91(2).
(blueprint: lem-sc-proper-flat-direct-image-perfect-chart).

Proof: Finite local freeness makes F finitely presented. On affine opens its sections
are projective over the source ring, hence flat over the base ring because f is flat.
Choose an affine neighbourhood V of s inside U. Apply the existing proper flat affine
Cech perfect-model theorem on V: it gives a nonnegative bounded complex D, termwise
flat over the identity, with perfect Q(D) and cohomology comparisons after every
ordinary pullback. Take K=Q(D) and the natural-number upper bound as an integer b.
Affine-relative flatness implies tensor-exact sheaf flatness. A bounded-above complex
of flat sheaves is K-flat. Tensor with M in degree zero is isomorphic to the termwise
tensor complex D tensor M. Its terms outside [0,b] are zero, hence so is its homology;
D itself witnesses the asserted derived-tensor vanishing.
For a:T to V, the recorded derived-pullback counit is invertible on the K-flat D.
The homotopy quotient and derived localization comparison isomorphisms identify
L a* Q(D) with Q of the termwise tensor pullback. Uniqueness of left adjoints identifies
that tensor pullback with ordinary pullback. Apply H^0 and the Cech-model comparison
for the standard cartesian square. Finally the degree-zero right-derived functor of
left-exact pushforward is pushforward itself, and uniqueness of left adjoints again
replaces ordinary pullback of F with tensor pullback. Compose these isomorphisms.
The proof uses the supplied derived localizations in universe w and also covers empty
new bases and bound b=0. -/
theorem exists_properFlatDirectImagePerfectChart
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFiniteLocallyFree] (U : S.Opens) (s : S) (hs : s ∈ U) :
    ∃ V : S.Opens, s ∈ V ∧ V ≤ U ∧
      ∃ (K : schemeDerivedCategory V.toScheme) (b : ℤ),
        IsPerfect V.toScheme K ∧
        (∀ M : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace),
          ∀ i : ℤ, i < 0 ∨ b < i →
            schemeDerivedTensorCohomologyVanishes V.toScheme K M i) ∧
        ∀ (T : Scheme.{u}) (a : T ⟶ V.toScheme),
          Nonempty (((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj
              ((derivedPullback a).obj K)) ≅
            ((Modules.pushforward (pullback.snd f (a ≫ V.ι))).obj
              ((Modules.tensorPullback (pullback.fst f (a ≫ V.ι))).obj F))) := by
  classical
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hs
  have := Modules.isGrothendieckAbelian X
  obtain ⟨D, d, hDge, hDle, hDflat, hDqc, hperfect, hcompare⟩ :=
    Modules.exists_proper_flat_affine_cech_perfect_model f F
      (Modules.isFlatOver_of_isFiniteLocallyFree f F) V hV
  have hDge0 : D.IsStrictlyGE 0 := hDge
  have hDled : D.IsStrictlyLE (d : ℤ) := hDle
  have hD : CochainComplex.IsAcyclicTensorKFlat (R := V.toScheme.sheaf) D :=
    CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace V.toScheme.toRingedSpace D
      ⟨d, fun i hi ↦ D.isZero_of_isStrictlyLE d i hi⟩
      (fun i ↦ isFlat_of_affineFlatOver_identity (D.X i) (hDflat i))
  refine ⟨V, hsV, hVU, DerivedCategory.Q.obj D, d, hperfect, ?_, ?_⟩
  · intro M i hi
    let : MonoidalCategory V.toScheme.Modules :=
      SheafOfModules.monoidalCategory V.toScheme.sheaf
    let : SymmetricCategory V.toScheme.Modules :=
      SheafOfModules.symmetricCategory V.toScheme.sheaf
    let : MonoidalPreadditive V.toScheme.Modules :=
      Classical.choice (SheafOfModules.tensorClosed V.toScheme.sheaf).1
    refine ⟨D, hD, ⟨Iso.refl _⟩, ?_⟩
    have hz : IsZero (D.X i) := by
      rcases hi with hi | hi
      · exact D.isZero_of_isStrictlyGE 0 i hi
      · exact D.isZero_of_isStrictlyLE d i hi
    let e := CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor V.toScheme.Modules) M D
    have hzero : IsZero (((((MonoidalCategory.curriedTensor
        V.toScheme.Modules).flip.obj M).mapHomologicalComplex (.up ℤ)).obj D).homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _
        (((MonoidalCategory.curriedTensor V.toScheme.Modules).flip.obj M).map_isZero hz)
    exact (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e |>.isZero_iff.mpr hzero
  · intro T a
    have := Modules.isGrothendieckAbelian (pullback f (a ≫ V.ι))
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      A, hA, hAmap, hAadd, ε, hε, htri, hK⟩ :=
      (derivedPullback_spec a)
    have hAeq : A = Modules.tensorPullback a :=
      CategoryTheory.Functor.ext hA (fun M N q ↦ hAmap q)
    subst A
    have := hAadd
    have := hK D hD
    let e : (derivedPullback a).obj (DerivedCategory.Q.obj D) ≅
        DerivedCategory.Q.obj
          (((Modules.tensorPullback a).mapHomologicalComplex (.up ℤ)).obj D) :=
      (derivedPullback a).mapIso ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))).symm.app D) ≪≫
        asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D)) ≪≫
        DerivedCategory.Qh.mapIso
          (((Modules.tensorPullback a).mapHomotopyCategoryFactors (.up ℤ)).app D) ≪≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings T.toRingedSpace))).app _
    let et : Modules.tensorPullback a ≅ Modules.pullback a :=
      (Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction a)
    obtain ⟨ec⟩ := hcompare a (pullback.fst f (a ≫ V.ι))
      (pullback.snd f (a ≫ V.ι)) (IsPullback.of_hasPullback f (a ≫ V.ι)) 0
    let ep : Modules.pullback (pullback.fst f (a ≫ V.ι)) ≅
        Modules.tensorPullback (pullback.fst f (a ≫ V.ι)) :=
      ((Modules.nonempty_tensorPullbackAdjunction
        (pullback.fst f (a ≫ V.ι))).some.leftAdjointUniq
          (Modules.pullbackPushforwardAdjunction _)).symm
    let q := Modules.pushforward (pullback.snd f (a ≫ V.ι))
    exact ⟨(DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
        ((NatIso.mapHomologicalComplex et (.up ℤ)).app D) ≪≫ ec ≪≫
      q.rightDerivedZeroIsoSelf.app _ ≪≫ q.mapIso (ep.app F)⟩

end AlgebraicGeometry.Scheme
