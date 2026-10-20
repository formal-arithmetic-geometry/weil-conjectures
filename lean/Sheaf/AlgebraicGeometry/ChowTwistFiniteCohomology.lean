/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent
import Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import Sheaf.AlgebraicGeometry.ProjectiveGraphTwistVanishing
import WeilConjectures.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # Finite cohomology of a sufficiently large Chow twist

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
construction of the module pi_* L^n.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The analytic part of the Chow construction, for a specified projective model.
No integrality, birationality, or generic-stalk condition is required.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
paragraphs defining L and G and applying the relative Leray spectral sequence.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)

Proof:
1. Put p = pi followed by i. The scheme X is Noetherian because it is proper
   over the affine Noetherian T. Separatedness of f gives a closed graph embedding
   of Y into projective space over X. Relative graph-twist vanishing chooses n
   killing every positive higher direct image of L.tensorPow n along p.
2. Invertibility of L makes its powers quasi-coherent and finitely presented.
   The independent projective pushforward argument gives finite type of p_* L^n:
   degree-zero projective finiteness on affine opens and quasi-coherent localization
   suffice. Quasi-coherence and the locally Noetherian finite-type criterion give
   coherence. Transport this along pushforwardComp pi i to i_* pi_* L^n.
3. The given closed embedding over T gives finite cohomology of L^n over Gamma(T,O).
   A linear Leray comparison for p, whose positive higher images vanish, identifies
   these groups with the cohomology of p_* L^n. The pushforwardComp isomorphism
   identifies the latter with that of i_* pi_* L^n. Restrict scalars along f.appTop
   and transport finite generation through the two linear equivalences. -/
theorem exists_chow_twist_finite_cohomology {X W T Y : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (i : W ⟶ X) [IsClosedImmersion i] (π : Y ⟶ W) [IsProper π]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = π ≫ i ≫ f) :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ n : ℕ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((pushforward i).obj ((pushforward π).obj (L.tensorPow n))) ∧
      (∀ q : ℕ,
        letI : Module Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q) :=
            Module.compHom _ f.appTop.hom
        Module.Finite Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q)) := by
  classical
  have : IsLocallyNoetherian T :=
    isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsNoetherian T := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let p := π ≫ i
  have : IsGrothendieckAbelian.{u} Y.Modules :=
    SheafOfModules.isGrothendieckAbelian Y.ringCatSheaf
  have : EnoughInjectives Y.Modules := IsGrothendieckAbelian.enoughInjectives
  have : HasInjectiveResolutions Y.Modules := by infer_instance
  dsimp
  let L := (pullback j).obj
    ((pullback (ProjectiveSpace.toProjInt N T)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
  have hjp : j ≫ (ℙ(N; T) ↘ T) = p ≫ f := by
    simpa only [p, Category.assoc] using hj
  obtain ⟨n₀, hn₀⟩ := exists_isZero_higherDirectImage_graph_twist f p N j hjp
  let k : Y ⟶ ℙ(N; X) := ProjectiveSpace.liftBaseChange p j hjp.symm
  have hk : k ≫ (ℙ(N; X) ↘ X) = p := ProjectiveSpace.liftBaseChange_over _ _ _
  have : L.IsInvertible := by infer_instance
  have : (L.tensorPow n₀).IsQuasicoherent := by infer_instance
  have : (L.tensorPow n₀).IsFinitePresentation := by
    have : SheafOfModules.IsInvertible.{u, u, u} (L.tensorPow n₀) :=
      IsInvertible.sheafOfModules_isInvertible (L.tensorPow n₀)
    exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hft : ((pushforward p).obj (L.tensorPow n₀)).IsFiniteType :=
    isFiniteType_projective_pushforward_independent p N k hk (L.tensorPow n₀)
  have hq : ((pushforward p).obj (L.tensorPow n₀)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated p _
  have hcohP : RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward p).obj (L.tensorPow n₀)) :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr ⟨hq, hft⟩
  refine ⟨n₀, ?_, ?_⟩
  · change RingedSpace.IsCoherent X.toRingedSpace ((pushforward p).obj (L.tensorPow n₀))
    exact hcohP
  · intro q
    let : Module Γ(T, ⊤) (((pushforward i).obj
        ((pushforward π).obj (L.tensorPow n₀))).H q) := Module.compHom _ f.appTop.hom
    let : Module Γ(T, ⊤) (((pushforward p).obj (L.tensorPow n₀)).H q) :=
      Module.compHom _ f.appTop.hom
    have he := nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
      p f (L.tensorPow n₀) (hn₀ n₀ le_rfl) q
    rw [← hjp] at he
    obtain ⟨e⟩ := he
    let : Module Γ(T, ⊤) ((L.tensorPow n₀).H q) :=
      Module.compHom _ (j ≫ (ℙ(N; T) ↘ T)).appTop.hom
    have : Module.Finite Γ(T, ⊤) ((L.tensorPow n₀).H q) := by
      exact finite_H_projective_affine_independent N j (L.tensorPow n₀) q
    exact Module.Finite.equiv e.symm

end AlgebraicGeometry.Scheme.Modules
