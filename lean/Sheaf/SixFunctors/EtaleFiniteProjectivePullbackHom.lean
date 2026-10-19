/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Pullback of internal Hom from a finite projective constant module

Source: literature/stacks-project/cohomology.tex, Tag 0GM7, label
`lemma-pullback-internal-hom`, proof of (1), the strictly perfect calculation and
final finite-projective identity (blueprint: lem-sf-etale-finite-projective-pullback-hom).

The comparison is the canonical internal-Hom comparison of the strong monoidal
étale inverse-image functor.  Its evaluation normalization is recorded explicitly.
Finite projectivity is expressed by the `Module.Finite` and `Module.Projective` classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory


namespace AlgebraicGeometry.Etale

/-- The canonical pullback comparison for internal Hom of constant module sheaves.

Source: Stacks Project, Tag 0GM7, proof of (1), the finite-projective identity
`h^* Hom(E,F) = Hom(h^*E,h^*F)` (blueprint: lem-sf-etale-finite-projective-pullback-hom).
The map is the internal-Hom comparison of the strong monoidal inverse image.
-/
def finiteProjectivePullbackHomComparison
    (A : Type (u + 1)) [CommRing A] {S S' : Scheme.{u}} (g : S' ⟶ S)
    (M : ModuleCat.{u + 1} A) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((ihom ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).obj F) ⟶
      (ihom ((upperStar (ModuleCat.{u + 1} A) g).obj
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).obj
        ((upperStar (ModuleCat.{u + 1} A) g).obj F) :=
  (Functor.LaxMonoidal.ihomComparison (upperStar (ModuleCat.{u + 1} A) g)
    ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).natTrans.app F

/-- Pullback commutes with internal Hom from a finite projective constant module.

Source: Stacks Project, Tag 0GM7, proof of (1), the strictly perfect calculation and
final finite-projective identity (blueprint: lem-sf-etale-finite-projective-pullback-hom).
Proof: choose a splitting of the finite projective module as a direct summand of a finite
free module.  The comparison for a finite free constant sheaf is the coordinate map on
basis values and is an isomorphism.  Applying the comparison to the splitting and using
naturality gives the two inverse identities for the summand.  The same naturality proves
naturality in the module and target sheaf.  The defining internal-Hom comparison equation
is exactly the pulled-back evaluation pairing, by `Functor.LaxMonoidal.ihomComparison_ev`.
-/
theorem finiteProjectivePullbackHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (M : ModuleCat.{u + 1} A) [Module.Finite A M] [Module.Projective A M]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (finiteProjectivePullbackHomComparison A g M F) ∧
      (∀ (M' : ModuleCat.{u + 1} A) [Module.Finite A M']
          [Module.Projective A M'] (a : M' ⟶ M),
        (upperStar (ModuleCat.{u + 1} A) g).map
            ((MonoidalClosed.pre ((constantSheaf S.smallEtaleTopology
              (ModuleCat.{u + 1} A)).map a)).app F) ≫
            finiteProjectivePullbackHomComparison A g M' F =
          finiteProjectivePullbackHomComparison A g M F ≫
            (MonoidalClosed.pre ((upperStar (ModuleCat.{u + 1} A) g).map
              ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).map a))).app
              ((upperStar (ModuleCat.{u + 1} A) g).obj F) ∧
      (∀ (F' : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : F ⟶ F'),
        (upperStar (ModuleCat.{u + 1} A) g).map
            ((ihom ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).map b) ≫
            finiteProjectivePullbackHomComparison A g M F' =
          finiteProjectivePullbackHomComparison A g M F ≫
            (ihom ((upperStar (ModuleCat.{u + 1} A) g).obj
              ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).map
                ((upperStar (ModuleCat.{u + 1} A) g).map b)) ∧
      ((Functor.LaxMonoidal.μ (upperStar (ModuleCat.{u + 1} A) g)
          ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
          ((ihom ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).obj F)) ≫
        (upperStar (ModuleCat.{u + 1} A) g).map
          ((ihom.ev ((constantSheaf S.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj M)).app F) =
      ((upperStar (ModuleCat.{u + 1} A) g).obj
          ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)) ◁
          finiteProjectivePullbackHomComparison A g M F ≫
        (ihom.ev ((upperStar (ModuleCat.{u + 1} A) g).obj
          ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).app
          ((upperStar (ModuleCat.{u + 1} A) g).obj F))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_⟩ := ModuleCat.isDualizable_of_projective M
    let K := constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)
    let : ExactPairing Mᘁ M := BraidedCategory.exactPairing_swap M Mᘁ
    let : ExactPairing (K.obj Mᘁ) (K.obj M) := ExactPairing.map K Mᘁ M
    exact Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing
      (upperStar (ModuleCat.{u + 1} A) g) (K.obj Mᘁ) (K.obj M) F
  · intro M' _ _ a
    refine ⟨?_, ?_, ?_⟩
    · exact Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app
        (upperStar (ModuleCat.{u + 1} A) g)
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).map a) F
    · intro F' b
      exact (Functor.LaxMonoidal.ihomComparison (upperStar (ModuleCat.{u + 1} A) g)
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)).natTrans.naturality b
    · exact (Functor.LaxMonoidal.ihomComparison_ev (upperStar (ModuleCat.{u + 1} A) g)
        ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) F).symm

end AlgebraicGeometry.Etale
