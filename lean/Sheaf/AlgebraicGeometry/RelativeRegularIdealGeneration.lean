/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.HilbertUniformSectionBound
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Topology.Sheaves.LocallySurjective
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Relative generation from regular geometric-fibre ideals

Source: Stacks Project, Varieties, Tags 08A6--08A8; Algebra, Tag 00DV.
(blueprint: lem-sfb-relative-regular-ideal-generation)

The existing HilbertSectionBound definitions supply the actual ideal twists, their
direct images, evaluation and monomial sections. Multiplication is characterized on
every monomial summand of the homogeneous polynomial module, so its normalization
is fixed without choosing an unspecified map. No uniform-bound theorem is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.HilbertSectionBound

noncomputable section

/-- Multiplication of an ideal section by a specified homogeneous monomial, followed
by the basis-normalized twist pairing. This is a construction of the map, rather
than an arbitrary arrow between its source and target.
Source: Stacks Project, Varieties, Tag 08A7; Cohomology of Schemes, Tag 01XT.
(blueprint: lem-sfb-relative-regular-ideal-generation) -/
def regularIdealMonomialMultiplier {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (m : ℤ) (e : ℕ)
    (a : RelativeProjectiveSpace.monomials.{u} n e) :
    idealSections i m ⟶ idealSections i (m + (e : ℤ)) :=
  (Scheme.Modules.pushforward (projection T n)).map
    ((ρ_ (idealTwist i m)).inv ≫
      idealTwist i m ◁ Scheme.Modules.homOfGlobalSection (twist T n e)
        (monomialSection T n e a) ≫ idealTwistMultiplication i m e)

/-- Fibre regularity and the specified section base-change isomorphisms imply
surjectivity of the untwisted evaluation and of homogeneous polynomial multiplication.
The latter arrow is characterized on all monomial summands, not merely asserted to
exist with the same source and target. Writing d=m+e, e nonnegative, enumerates exactly
all integers d at least m.

Source: Stacks Project, Varieties, Tags 08A6--08A8; Algebra, Tag 00DV.
(blueprint: lem-sfb-relative-regular-ideal-generation)

Proof (the five DAG steps):
1. On a geometric fibre the normalized ideal comparison identifies the pulled-back
   ideal with the actual ideal of the pulled-back closed immersion. The twist bases
   pull back with transitions (x_i/x_j)^b, and pullback preserves tensor products
   (lem-weil-pbc-module-pullback-tensor, def-pc-module-pullback,
   def-pc-projective-space-twist, lem-pc-twist-tensor). The section base-change map
   sends a section to its restriction. Thus the pulled-back evaluation, twisted by
   O(m), is the ordinary fibre evaluation. Apply
   lem-sfb-m-regular-coherent-sheaf-consequences with a=b=m and untwist.
2. The evaluation cokernel has finite stalks, as a quotient of the finite-type ideal
   (lem-weil-pbc-finite-type-module-stalk-finite). For x in the ambient space, choose
   an algebraic closure of kappa(x). Its geometric point factors through a geometric
   fibre where evaluation is surjective. The stalk pullback formula, stalk exactness
   and right exactness of tensor identify the cokernel tensored with that closure
   with zero (lem-weil-pbc-module-stalk-pullback, lem-weil-pbc-module-stalk-exact,
   lem-weil-pbc-tensor-right-exact). Faithful field extension detects the zero residue
   quotient (lem-pur-field-vector-space-tensor-nontrivial). Local Nakayama gives zero
   cokernel stalks (lem-weil-pbc-nakayama-local-generators), hence evaluation is epic
   (lem-weil-pbc-locally-surjective-iff-stalks).
3. On each fibre regularity gives surjective multiplication by linear sections in
   every degree at least m. The coordinate sections form the standard basis by
   lem-pc-projective-space-twist-cohomology. Induct on e: e=0 uses 1; at a successor
   expand first in the coordinates, then apply the induction hypothesis and collect
   monomials. This gives surjective multiplication by all degree-e polynomials,
   including n=0 with its single coordinate.
4. The normalized twist pairing and section base-change maps identify the fibre of
   the displayed relative multiplication with that polynomial multiplication: on
   each monomial summand x^a and each section s, both send x^a tensor s to x^a s.
   This comparison uses lem-weil-pbc-module-pullback-tensor and lem-pc-twist-tensor.
   The tensor/coproduct universal property gives the uniquely normalized map.
5. Its cokernel stalks are finite, since K_(m+e) is finite locally free. Tensoring
   with an algebraic closure of a residue field gives zero by steps 3--4. The stalk
   pullback and exactness lemmas, right exactness, faithful field extension and local
   Nakayama, as in step 2, force every cokernel stalk to vanish. The stalkwise
   criterion gives the second epimorphism. For e=0 multiplication is by 1; over
   the empty base all these module sheaves are zero.
-/
theorem relative_regular_ideal_generation {T Z : Scheme.{u}} (n : ℕ) (m : ℤ)
    (hm : 1 ≤ m) (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T))
    [IsClosedImmersion i] [Flat (i ≫ projection T n)]
    [LocallyOfFinitePresentation (i ≫ projection T n)]
    [QuasiCompact (i ≫ projection T n)] [QuasiSeparated (i ≫ projection T n)]
    (hfinite : Scheme.Modules.IsQuasiCoherentFiniteType i.ker.toModules)
    (hideal : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (g : Spec (.of k) ⟶ T),
      ∃ c : (Scheme.Modules.tensorPullback
          (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)).obj i.ker.toModules ≅
            (pullback.snd i (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)).ker.toModules,
        c.hom ≫
            (pullback.snd i (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)).ker.toModulesι =
          (Scheme.Modules.tensorPullback
            (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)).map i.ker.toModulesι ≫
          Scheme.Modules.tensorPullbackObjUnitToUnit
            (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g))
    (hcoherent : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (g : Spec (.of k) ⟶ T), RingedSpace.IsCoherent
        (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace
        (pullback.snd i (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)).ker.toModules)
    (hregular : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (g : Spec (.of k) ⟶ T) (j : ℕ), 1 ≤ j → j ≤ n →
        Subsingleton ((RingedSpace.moduleCohomology
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace j).obj
            ((pullback.snd i (ProjectiveSpace.map
              (ULift.{u} (Fin (n + 1))) g)).ker.toModules ⊗ₘ
                twist (Spec (.of k)) n (m - (j : ℤ)))))
    (hfree : ∀ b : ℤ, m ≤ b → (idealSections i b).IsFiniteLocallyFree)
    (hbase : ∀ (b : ℤ), m ≤ b → ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (g : Spec (.of k) ⟶ T), IsIso (Scheme.Modules.moduleBaseChangeMap
        (projection T n) (projection (Spec (.of k)) n) g
        (ProjectiveSpace.map (ULift.{u} (Fin (n + 1))) g)
        (ProjectiveSpace.map_over (ULift.{u} (Fin (n + 1))) g) (idealTwist i b))) :
    Epi (evaluation i m) ∧
      ∀ e : ℕ, ∃ μ : polynomialModule T n e ⊗ idealSections i m ⟶
          idealSections i (m + (e : ℤ)),
        Epi μ ∧ ∀ a : RelativeProjectiveSpace.monomials.{u} n e,
          (λ_ (idealSections i m)).inv ≫
            MonoidalCategory.whiskerRight (C := T.Modules)
              (Sigma.ι (fun _ : RelativeProjectiveSpace.monomials.{u} n e ↦
                𝟙_ T.Modules) a) (idealSections i m) ≫ μ =
                regularIdealMonomialMultiplier i m e a := by
  sorry

end

end AlgebraicGeometry.HilbertSectionBound
