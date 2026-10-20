/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.BertiniIndependentFunctions
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible
import Sheaf.FieldTheory.BertiniFieldExtension

/-!
# Geometric irreducibility of a general member of a linear system

Source: Stacks Project, More on Morphisms, Tag 0G4F, lemma-bertini-irreducible,
in Varieties Situation 0G47 (blueprint: lem-zl-bertini-irreducible-member).

The helper constructs the member over an extension field using the canonical tensor-pullback
unit, then uses the recorded zero-scheme construction. Codimension is `Order.coheight` on
irreducible closed subsets, ordered by inclusion. Components of a closed subset are its maximal
irreducible closed subsets. Generality is written out using all extension-field points of a
nonempty open in affine coordinate space.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The ideal of the member with coordinates `a` over `K`: pull back the sections `s i`
along `Y_K → Y`, multiply by the functions from `a i`, and take the zero scheme of their sum.
The adjunction chosen here has the prescribed sectionwise unit `m ↦ 1 ⊗ m`.
Source: Stacks Project, Varieties Situation 0G47, formula for `H_v`
(blueprint: lem-zl-bertini-irreducible-member). -/
noncomputable def linearSystemMemberIdeal
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (L : Y.Modules) {r : ℕ} (s : Fin r → Γ(L, ⊤))
    (K : Type u) [Field K] [Algebra k K] (a : Fin r → K) :
    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IdealSheafData :=
  (Scheme.Modules.homOfGlobalSection _
    (∑ i : Fin r,
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
          ((Scheme.ΓSpecIso (.of K)).inv (a i)) •
        (@id Γ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj L, ⊤)
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))).unit.app L).val.app
            (op ⊤) (s i))))).zeroLocus

/-- Under the codimension-two hypotheses, a general member is geometrically irreducible.
The `k`-structure on global sections is restriction of scalars along the structure morphism;
`b` supplies the coordinates in the definition of "general". Maximality is taken among
irreducible closed subsets contained in the indicated intersection or base locus.

Source: Stacks Project, Tag 0G4F, in Varieties Situation 0G47
(blueprint: lem-zl-bertini-irreducible-member).

Proof:
1. Finite type over a field gives a Noetherian scheme (pqf-lem-locnoeth-lft and
   pqf-lem-affine-open-locnoeth). Its nilradical has a positive power zero
   (lem-sc-reduction-nilradical-nilpotent). Reduction and all its field base changes,
   including the section zero schemes and intersections, have identical underlying spaces.
   Thus reduce to an integral scheme (def-pc-integral-scheme).
2. The three vectors in the first hypothesis are independent. At the generic point of W,
   any relation has zero first coefficient. Dependence of the other two would make W a
   component of a single equation, of height at most one by
   lem-weil-pbc-noetherian-height-quotient-bound. Extend them to a basis.
3. Construct the universal zero scheme of sum x_i psi(b_i) over affine parameter space.
   On a trivializing affine Spec A it is Spec A[x_i]/(sum x_i f_i), hence its projection
   is finite type and its field-point fibres are the members defined above
   (def-pc-zero-scheme and def-weil-pbc-mv-polynomial-ring).
4. The first section is nonzero on every nonempty trivializing affine, by integrality.
   The base-locus hypothesis makes every minimal prime of (f_i) have height at least two.
   Apply lem-zl-linear-incidence-irreducible. The irreducible affine incidence charts
   overlap over the complement of the first zero scheme, so their union is irreducible.
5. Choose a trivializing affine meeting W in that complement. Dividing by the first
   section gives functions g_2,...,g_r. The common maximal chain length in a finite-type
   domain (lem-weil-pbc-finite-type-domain-dimension-local-ring) shows W has dimension d-2.
   Apply lem-zl-bertini-independent-functions to obtain constants c_i such that the
   variables, sum g_i x_i, and sum c_i g_i are algebraically independent.
6. The function field K of Y is geometrically irreducible over k by
   lem-zl-generic-point-geometric-irreducibility and is finitely generated as a field.
   Apply lem-zl-bertini-field-extension. Eliminating x_1 identifies the incidence function
   field with K(x_2,...,x_r), geometrically irreducible over the parameter function field;
   independence also gives dominance of the incidence projection.
7. The generic fibre is irreducible, with this function field: localization preserves the
   generic point on its nonempty affine charts. Apply
   lem-zl-generic-point-geometric-irreducibility to make the generic fibre geometrically
   irreducible over the parameter function field.
8. Apply lem-sbc-generic-geometric-irreducibility-shrink to obtain a nonempty parameter
   open with geometrically irreducible residue-field fibres. Every extension-field point
   gives a base change of such a fibre, hence is geometrically irreducible. Transfer back
   through the nilpotent thickenings of step 1. This is precisely generality in 0G47. -/
theorem exists_open_geometricallyIrreducible_linearSystemMember
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ ψ : V →ₗ[k] Γ(L, ⊤),
      (∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds Y),
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support ∩
            (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) W ∧
        ¬ (W : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₁)).zeroLocus.support ∧
        Order.coheight W = 2) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ ⋂ w : V,
            ((Scheme.Modules.homOfGlobalSection L (ψ w)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B) →
      ∀ (r : ℕ) (b : Module.Basis (Fin r) k V),
        ∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
          (U : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
          ∀ (K : Type u) [Field K] [Algebra k K] (a : Fin r → K),
            Set.range (Spec.map
              (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)) ⊆ (U : Set _) →
            GeometricallyIrreducible
              ((linearSystemMemberIdeal (Y ↘ Spec (.of k)) L (fun i ↦ ψ (b i)) K a).subschemeι ≫
                pullback.snd (Y ↘ Spec (.of k))
                  (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry
