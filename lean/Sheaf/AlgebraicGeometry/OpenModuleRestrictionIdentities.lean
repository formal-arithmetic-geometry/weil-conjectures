/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Open and closed restrictions of coefficient-linear extension by zero

Source: blueprint main-20261015, Six Functors Basics, restricted functors,
`lem-sfb-dc-open-lower-shriek-preserves.proof.md`, the two restriction assertions;
Stacks Project, Pro-etale Cohomology, Tags 09BN and 09AH, and Modules on Sites, Tag 03DI
(blueprint: lem-sfb-open-module-restriction-identities).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Extension by zero restricts naturally to the original internal coefficient module on
its open support and to zero on the complementary closed subscheme.

Source: blueprint main-20261015, restricted functors,
`lem-sfb-dc-open-lower-shriek-preserves.proof.md`, the two restriction assertions;
Stacks Project, Tags 09BN, 09AH and 03DI
(blueprint: lem-sfb-open-module-restriction-identities).

Proof:
1. Use `lem-sfb-internal-module-operations-transport` to pass through the canonical
   additive equivalences E_T from internal coefficient modules to sectionwise modules.
   The comparisons identify the actual coefficient tensor pullbacks with sectionwise
   pullbacks, and identify the given extension by zero with the sectionwise left adjoint.
2. Apply `lem-sfb-proetale-identified-open-closed` with the section-ring coefficient
   sheaves and their inverse-image identifications induced by the coefficient maps.
   It gives a sectionwise extension F left adjoint to open restriction R, with invertible
   unit and zero closed restriction. Its hypotheses require exactly the complementary
   closed immersion and quasi-compact open immersion here.
3. Compare the sectionwise extension L from Step 1 with F as left adjoints to the same R.
   The comparison F(N) -> L(N) is F of the unit for L followed by the counit for F;
   the reverse comparison is L of the unit for F followed by the counit for L.
   Naturality and the triangle identities show that the two composites are identities.
   This identifies the specified internal extension with F through E_X and E_U.
4. Compose the pullback comparison, the extension comparison, and the inverse of the
   unit for F to obtain E_U(j^*j_!M) isomorphic to E_U(M). Fullness lifts the maps and
   faithfulness checks inverse identities and naturality, giving the first natural iso.
5. Compose the closed pullback and extension comparisons with the zero closed restriction
   of F. The additive equivalence E_Z preserves zero. Fullness and faithfulness lift the
   resulting isomorphisms to internal modules; uniqueness of maps to and from zero gives
   naturality. No coefficient finiteness or Noetherian hypothesis enters these steps. -/
theorem open_module_restriction_identities
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i = (Set.range j)ᶜ) :
    Nonempty (openImmersionLowerShriek Λ j ⋙ upperStar Λ j ≅
      𝟭 (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) ∧
    Nonempty (openImmersionLowerShriek Λ j ⋙ upperStar Λ i ≅
      (Functor.const
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))).obj
        (0 : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) := by
  let ff := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).fullyFaithfulMapModLeft
  have : (openImmersionLowerShriek Λ j).Full := ff.full
  have : (openImmersionLowerShriek Λ j).Faithful := ff.faithful
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful
  refine ⟨⟨(asIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit).symm⟩, ?_⟩
  have hdisj : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  refine ⟨NatIso.ofComponents (fun M ↦
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i hdisj M).isoZero)
    (fun f ↦ ?_)⟩
  exact (isZero_zero _).eq_of_tgt _ _

end AlgebraicGeometry.ProEtale.CondensedRing
