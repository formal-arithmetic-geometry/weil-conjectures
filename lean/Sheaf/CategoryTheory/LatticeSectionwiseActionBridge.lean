/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.CondensedActionTensor
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor
public import Sheaf.CategoryTheory.LatticeRestrictionCupComparison
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # The normalized sectionwise-to-ordinary lattice action bridge

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), agent lattice expansion, ordinary/sectionwise bridge for the regular cup clause
(blueprint: lem-sfb-lattice-sectionwise-action-bridge).

The bridge includes its comparison on every complex and its coefficient tensor normalization.
The additional equations fix the ordinary equivalence over the identity on underlying modules,
the locally constant extension, the trivial actions, and the ordinary tensor comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace Profinite.DiscreteLattice.RestrictionCup

/-- Sectionwise discrete-lattice actions and ordinary lattice actions admit the normalized
bridge, with the same underlying modules and maps. The extension of an ordinary action is
unique, and its restriction to each constant fibre is the corresponding ordinary action.

Source: direct-image stability proof, paragraph (3), agent lattice expansion, returned step 13
(blueprint: lem-sfb-lattice-sectionwise-action-bridge).

Proof:
1. Apply lem-sfb-discrete-condensed-action-equivalence to the universe-lifted discrete lattice.
   Constant sections give the inverse. For an ordinary action, glue its constant actions on
   the finite clopen fibres of each locally constant group section. The coherent sheaf
   criterion identifies sections on this partition with the product of the fibre sections.
   Naturality on each fibre and separatedness prove uniqueness, including the displayed
   formula after any base change on which the section is constant.
2. The action categories are abelian by lem-sfb-condensed-action-injective-infrastructure
   and def-sfb-lattice-derived-invariants-tensor. The additive equivalence and its inverse
   preserve kernel and cokernel universal properties, hence are exact.
3. Fully fixed sections are fixed by the basis constants. Conversely basis-fixed sections
   are fixed by inverses and products and remain so after restriction. The fibre formula
   then fixes them under every group section. The ordinary invariant limit and sectionwise
   invariants have the same included subsheaf. Factor their inclusions through each other;
   monicity proves uniqueness of the resulting invariant isomorphism. Trivial actions agree.
4. By lem-pe-internal-section-tensor-comparison, the relative tensor is generated locally by
   balanced pure tensors. The diagonal constant actions agree on them, and hence on the
   sheafified tensor. Action uniqueness extends this agreement to all group sections.
   The underlying tensor and regular-unit identities give the strong tensor comparisons;
   coherence and the regular algebra identity follow on underlying internal modules.
5. Apply lem-weil-pbc-exact-functor-derived-factorization to the equivalence and the identity
   coefficient functor. Their termwise inverse identities give the derived equivalences
   and the canonical localization factors without identifying the two localization sizes.
6. Apply lem-derived-exact-equivalence-squares to the invariant isomorphism and exact trivial
   actions. The universal right-derived pairs of def-sfb-right-derived-functor yield the
   comparison. Its universal factorization equation is precisely Bridge.normalization on
   every complex, using both computation units and localization factorization maps.
7. The identity coefficient functor preserves flatness, acyclicity and K-flatness. Use the
   internal-section tensor comparison, closed sheaf tensor and functorial flat resolutions
   with lem-derived-right-exact-tensor-comparison. This fixes the binary comparison on
   flat-term K-flat representatives and the unit by localization. The coherence inherited
   from complexes in lem-sfb-derived-monoidal proves the strong tensor diagrams.
8. Assemble these data into Bridge. Its regular identification is the localized underlying
   regular identity. No assertion of the predicate Compatible is used or made.
-/
theorem lattice_sectionwise_action_bridge
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ) :
    ∃ E : Bridge R r,
      (∃ h : E.equivalence.functor ⋙ Action.forget (Modules R) (Group r) =
          CategoryTheory.CondensedBar.forgetAction,
        E.underlying = eqToIso h) ∧
      (∀ N : Equivariant R r,
        ∃! act : ∀ S : Profinite.{u}, C(S, ULift.{u} (Group r)) →*
            Module.End (CategoryTheory.CondensedBar.sectionRing (ring R) S)
              (CategoryTheory.CondensedBar.sections (ring R) N.V S),
          (∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, ULift.{u} (Group r)))
              (x : CategoryTheory.CondensedBar.sections (ring R) N.V S),
            (N.V.X.obj.map f.op).hom (act S g x) =
              act T (g.comp f.hom.hom) ((N.V.X.obj.map f.op).hom x)) ∧
          (∀ (S : Profinite.{u}) (v : Group r)
              (x : CategoryTheory.CondensedBar.sections (ring R) N.V S),
            act S (ContinuousMap.const S (ULift.up v)) x =
              ((N.ρ v).hom.hom.app (op S)) x) ∧
          (∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, ULift.{u} (Group r)))
              (v : Group r) (x : CategoryTheory.CondensedBar.sections (ring R) N.V S),
            (∀ t : T, g (f.hom.hom t) = ULift.up v) →
              (N.V.X.obj.map f.op).hom (act S g x) =
                ((N.ρ v).hom.hom.app (op T)) ((N.V.X.obj.map f.op).hom x))) ∧
      (∀ (N : Equivariant R r) (S : Profinite.{u})
          (g : C(S, ULift.{u} (Group r))),
        ∃ (n : ℕ) (P : Fin n → Profinite.{u}) (ι : ∀ i : Fin n, P i ⟶ S)
            (v : Fin n → Group r),
          Function.Injective v ∧ (∀ i : Fin n, Nonempty (P i)) ∧
          Nonempty (IsColimit (Cofan.mk S ι)) ∧
          (∀ (i : Fin n) (t : P i), g ((ι i).hom.hom t) = ULift.up (v i)) ∧
          Function.Bijective
            (fun x : CategoryTheory.CondensedBar.sections (ring R) N.V S ↦
              fun i : Fin n ↦ (N.V.X.obj.map (ι i).op).hom x)) ∧
      (∀ (N : CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r)))
          (S : Profinite.{u}) (x : CategoryTheory.CondensedBar.sections (ring R) N.module S),
        Profinite.CondensedAction.FixedAll N S x ↔
          ∀ i : Fin r,
            N.act S (ContinuousMap.const S (ULift.up (generator i))) x = x) ∧
      (∀ α : E.equivalence.functor ⋙ invariants R r ≅
          (CategoryTheory.CondensedDerivedRestriction.invariants
            (ring R) (ULift.{u} (Group r))).functor,
        (∀ N, α.hom.app N ≫
            (CategoryTheory.CondensedDerivedRestriction.invariants
              (ring R) (ULift.{u} (Group r))).inclusion.app N =
          limit.π ((Action.functorCategoryEquivalence (Modules R) (Group r)).functor.obj
            (E.equivalence.functor.obj N)) PUnit.unit ≫ E.underlying.hom.app N) →
          α = E.invariants) ∧
      (∃ t : Profinite.CondensedAction.trivial (R := R) (P := ULift.{u} (Group r)) ⋙
          E.equivalence.functor ≅ DerivedCup.trivial R r,
        (∀ M : Modules R, (t.hom.app M).hom = E.underlying.hom.app
          ((Profinite.CondensedAction.trivial (R := R) (P := ULift.{u} (Group r))).obj M)) ∧
        E.regular.hom = t.hom.app (𝟙_ (Modules R))) ∧
      (∃ c : E.equivalence.functor.CoreMonoidal,
        (∀ M N : CategoryTheory.CondensedBar.Equivariant
            (ring R) (ULift.{u} (Group r)),
          (c.μIso M N).hom.hom ≫ E.underlying.hom.app (M ⊗ N) ≫
              ((CategoryTheory.CondensedDerivedRestriction.actionTensor
                (ring R) (ULift.{u} (Group r))).forgetCore.μIso M N).inv =
            E.underlying.hom.app M ⊗ₘ E.underlying.hom.app N) ∧
        c.εIso.hom.hom ≫ E.underlying.hom.app
            (𝟙_ (CategoryTheory.CondensedBar.Equivariant (ring R) (ULift.{u} (Group r)))) ≫
            (CategoryTheory.CondensedDerivedRestriction.actionTensor
              (ring R) (ULift.{u} (Group r))).forgetCore.εIso.inv = 𝟙 (𝟙_ (Modules R))) := by
  sorry

end Profinite.DiscreteLattice.RestrictionCup
