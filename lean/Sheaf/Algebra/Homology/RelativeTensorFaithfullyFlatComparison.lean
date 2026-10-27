/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.Algebra.Homology.MixedTotalTensorScalarExtension
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Faithfully flat extension of the coefficient algebra in a relative tensor

Source: Stacks Project, More on Algebra, Tag 0DJF, `lemma-no-change-tor-amplitude`,
with the K-flat mixed tensor construction of Tags 06Y4 and 06Y6.
(blueprint: lem-sfb-relative-tensor-faithfully-flat-comparison)

The mixed tensors retain the coefficient action on the first factor. The universal
counits specify the derived functors and their computation on K-flat representatives;
the comparison is an isomorphism of bifunctors after restricting the second variable
to modules in degree zero. The final clause spells out the Tor-interval condition.
-/

@[expose] public section

set_option autoImplicit false
universe u wR wA wB
open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Relative derived tensor commutes with faithfully flat coefficient extension,
and relative Tor amplitude is preserved and reflected.
Source: Stacks Project, Tag 0DJF, `lemma-no-change-tor-amplitude`; Tags 06Y4 and 06Y6.
(blueprint: lem-sfb-relative-tensor-faithfully-flat-comparison)

Proof, following the six steps of the node:
1. Termwise extension `T(C) = B tensor_A C` is exact by faithful flatness.
   The exact-functor cohomology comparison
   (`lem-weil-pbc-exact-functor-complex-cohomology`) gives
   `H^i(T(C)) = B tensor_A H^i(C)`, so T preserves quasi-isomorphisms.
   Choose an A-K-flat resolution by `lem-pc-source-module-kflat-resolution`.
   Its image under T is quasi-isomorphic to T(C), identifying derived extension
   with termwise extension for every unbounded representative.
2. Resolve each R-module N in degree zero by an R-K-flat complex F, with no
   boundedness assumption. The second-factor derived tensor functor
   (`lem-pc-derived-tensor-second-factor-functor`) computes the mixed tensor by
   Tot(C tensor_R F), after signed symmetry. The restriction comparison
   (`lem-pc-mixed-tensor-restriction-comparison`) identifies its underlying R-complex
   with the ordinary total tensor, and its A-action is the action through C.
   The same construction for T(C) retains its B-action.
3. The chain isomorphism `new-lem-pc-mixed-total-tensor-scalar-extension` identifies
   T(Tot(C tensor_R F)) with Tot(T(C) tensor_R F), by sending
   b tensor (c tensor f) to (b tensor c) tensor f on diagonal summands.
   The inverse regroups these same factors. Localizing gives the derived isomorphism.
4. This chain formula commutes with maps in C and F. Mixed K-flat invariance
   (`lem-pc-mixed-tensor-kflat-quasi-iso`) and the derived-second-factor universal
   property make the comparison independent of resolutions. Localization
   (`lem-weil-pbc-localization-universal-property`) descends naturality to all
   derived K-morphisms; restriction along the single functor gives naturality
   in every module map N to N'.
5. Taking cohomology in step 3 and using step 1 gives the B-linear identification
   B tensor_A H^i(K tensor_R^L N) = H^i((K tensor_A^L B) tensor_R^L N).
   This requires neither A nor B to be R-flat.
6. For every a <= b, tensoring a zero cohomology module with B gives zero.
   Conversely `lem-sc-faithfully-flat-tensor-zero` detects zero cohomology before
   extension. Quantify over all R-modules N and all i outside [a,b]. Restriction
   of scalars changes neither the underlying groups nor their vanishing. -/
theorem relative_tensor_faithfully_flat_comparison
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) ∧
    ∃ (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
      (ε : Q ⋙ L ⟶
        (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ) ⋙ Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)) ∧
      IsIso ε ∧
    ∃ (TA : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
      (TB : DerivedCategory (ModuleCat.{u} B) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
      (εA : (((Functor.whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} A))).obj Q).obj Q).obj
          TA ⟶ ModuleCat.mixedTotalTensor (algebraMap R A) ⋙
            (Functor.whiskeringRight _ _ _).obj Q)
      (εB : (((Functor.whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} B))).obj Q).obj Q).obj
          TB ⟶ ModuleCat.mixedTotalTensor (algebraMap R B) ⋙
            (Functor.whiskeringRight _ _ _).obj Q),
      (∀ C : CochainComplex (ModuleCat.{u} A) ℤ,
        (TA.obj (Q.obj C)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ εA C)
          (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ))) ∧
      (∀ C : CochainComplex (ModuleCat.{u} B) ℤ,
        (TB.obj (Q.obj C)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ εB C)
          (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ))) ∧
      (∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
        (F : CochainComplex (ModuleCat.{u} R) ℤ),
        (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F →
          IsIso ((εA.app C).app F)) ∧
      (∀ (C : CochainComplex (ModuleCat.{u} B) ℤ)
        (F : CochainComplex (ModuleCat.{u} R) ℤ),
        (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F →
          IsIso ((εB.app C).app F)) ∧
      Nonempty (TA ⋙
          (Functor.whiskeringRight _ _ _).obj L ⋙
          (Functor.whiskeringLeft _ _ _).obj (singleFunctor (ModuleCat.{u} R) 0) ≅
        L ⋙ TB ⋙
          (Functor.whiskeringLeft _ _ _).obj (singleFunctor (ModuleCat.{u} R) 0)) ∧
      (∀ (a b : ℤ), a ≤ b → ∀ K : DerivedCategory (ModuleCat.{u} A),
        (∀ (N : ModuleCat.{u} R) (i : ℤ), i < a ∨ b < i →
          IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
            ((TA.obj K).obj ((singleFunctor (ModuleCat.{u} R) 0).obj N)))) ↔
        (∀ (N : ModuleCat.{u} R) (i : ℤ), i < a ∨ b < i →
          IsZero ((homologyFunctor (ModuleCat.{u} B) i).obj
            ((TB.obj (L.obj K)).obj ((singleFunctor (ModuleCat.{u} R) 0).obj N))))) := by
  sorry

end DerivedCategory
