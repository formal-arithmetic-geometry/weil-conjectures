module

public import Sheaf.AlgebraicGeometry.GroupScheme.IntegralRootWeights
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic
public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenyBorelRootCompatibility
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The integral root datum and the geometric fibre lattice criteria

Source: Conrad, Reductive group schemes, Definition 5.1.1, Example 5.1.4,
Proposition 5.1.6, Example 5.1.7 and Exercise 6.5.2; Milne, Algebraic Groups,
Propositions 21.48 and 23.29 (blueprint: lem-sfb-integral-split-root-datum).

The lifted integers allow integral schemes and arbitrary geometric fibres to live in
one universe. Root weights use the full group action on tangent vectors, never the
differentials of characters. Rationalization is written with its rational factor first.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

open IntegralRootWeights in
/-- A reductive integral group with a specified split maximal torus has a constant
reduced root datum. Its nonzero tangent weights are free lines after every nonzero
ring base change; its coroots are the base changes of the same integer cocharacters.
Semisimplicity and simple connectedness of every geometric fibre are detected by
the root span and the full weight lattice, respectively.

Source: Conrad, Definition 5.1.1, Example 5.1.4, Proposition 5.1.6, Example 5.1.7,
Exercise 1.6.13(ii) and Exercise 6.5.2; Milne, Propositions 21.48 and 23.29.
(blueprint: lem-sfb-integral-split-root-datum)

Proof plan:
1. Choose a finite integral basis of M. Relative diagonalizable character duality
   identifies the character and cocharacter lattices with M and its integer dual:
   locally constant integer homomorphisms on Spec Z are constant, since every
   nonempty open contains the generic point. The Hopf formulas identify all base changes.
2. Apply relative-tangent-weight-base-change and relative-torus-bundle-weights to
   conjugation. Tangent weights are finite projective and have constant rank on Spec Z.
   Reductive-rank-one-reflections gives rank one for each nonzero generic weight.
   A finite projective Z-module embeds in a finite free one; subgroup-finite-free
   makes it free. Thus the nonzero weight support is constant, with free root lines.
3. Reducedness in the geometric generic fibre supplies opposite roots. Apply
   relative-canonical-root-exponential and relative-opposite-root-reflection-map.
   Character duality makes each resulting coroot one fixed integer dual vector.
   The rank-one formula gives pairing two and the geometric coroot identification.
4. In the geometric generic fibre, reductive-borel-pair-structure and Borel maximal
   torus conjugacy supply the reduced datum. Rank-one reflections give finite Weyl
   group and compatible root/coroot reflections. These are integer equalities, so
   they hold in M. Tangent base change and the relative reflection map give the
   same root lines and coroots over every nonzero ring, including nonreduced ones.
5. Apply semisimple-roots-span to each algebraically closed field. The resulting
   condition is exactly that the rational roots span the rationalized character lattice.
6. Under this span condition, simply-connected-character-lattice gives M=P in
   any simply connected geometric fibre, for example over the algebraic closure of Q.
7. Conversely let M=P and take a surjective homomorphism H→G_k with finite central
   scheme-theoretic kernel. Algebraic-group-homomorphism-factorization gives a flat
   quotient onto its closed image. Smooth-geometrically-reduced makes that image all
   of G_k. Central-isogeny-borel-root-compatibility identifies roots and coroot pairings;
   isogeny-root-power-laws makes every root exponent one, even for nonreduced kernels.
8. The induced injective finite-cokernel character map is rationally invertible.
   Each inverse image of an integral character pairs integrally with every coroot,
   hence lies in P=M. The map is therefore surjective. The isomorphism clause of
   root-datum-isogeny-realization now makes the original homomorphism an isomorphism.
9. Empty roots are allowed: spanning then forces M=0 and P=0. A nonzero torus
   fails the span condition. Nonzero coefficient rings retain nonzero free root lines. -/
theorem integral_split_root_datum
    (M : Type u) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (G : Grp (Over (Spec (.of (ULift.{u} ℤ)))))
    (i : ringDiagonalizableGroup (ULift.{u} ℤ) M ⟶ G)
    (hsm : Smooth G.X.hom) (haff : IsAffineHom G.X.hom)
    (hfp : LocallyOfFinitePresentation G.X.hom)
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra (ULift.{u} ℤ) F],
      ReductiveTorusCentralizer.IsReductive ((scalarChange (ULift.{u} ℤ) F).obj G))
    (hclosed : IsClosedImmersion i.hom.hom.left)
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra (ULift.{u} ℤ) F],
      ReductiveTorusCentralizer.IsMaximalTorus
        ((scalarChange (ULift.{u} ℤ) F).map i)) :
    ∃ (Φ : Finset M) (P : RootDatum Φ M (Module.Dual ℤ M)),
      (∀ α : Φ, P.root α = α.val) ∧
      (∀ (m : M) (ν : Module.Dual ℤ M), P.toLinearMap m ν = ν m) ∧
      P.IsReduced ∧ Finite P.weylGroup ∧
      (∀ (A : Type u) [CommRing A] [Nontrivial A] [Algebra (ULift.{u} ℤ) A],
        (∀ m : M, m ∈ Φ ↔ m ≠ 0 ∧ weight (A := A) G i m ≠ ⊥) ∧
        ∀ α : Φ, Nonempty (weight (A := A) G i α.val ≃ₗ[A] A)) ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra (ULift.{u} ℤ) F]
        (α : Φ), IsGeometricCoroot G i α.val (P.coroot α) F) ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra (ULift.{u} ℤ) F],
        IsSemisimpleGroupScheme ((scalarChange (ULift.{u} ℤ) F).obj G).X ↔
          Submodule.span ℚ (Set.range (fun α : Φ ↦
            TensorProduct.mk ℤ ℚ M 1 α.val)) = ⊤) ∧
      (Submodule.span ℚ (Set.range (fun α : Φ ↦
          TensorProduct.mk ℤ ℚ M 1 α.val)) = ⊤ →
        ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra (ULift.{u} ℤ) F],
          (∀ (H : Over (Spec (.of F))) [GrpObj H],
            IsSemisimpleGroupScheme H →
            ∀ (f : H ⟶ ((scalarChange (ULift.{u} ℤ) F).obj G).X) [IsMonHom f],
              Surjective f.left → IsFinite (GrpObj.ker f).hom →
              (∀ (W : Over (Spec (.of F))) (x : W ⟶ GrpObj.ker f) (g : W ⟶ H),
                (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f) ↔
          ∀ v : ℚ ⊗[ℤ] M,
            (∃ m : M, TensorProduct.mk ℤ ℚ M 1 m = v) ↔
              ∀ α : Φ, ∃ n : ℤ,
                (((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot α)).liftBaseChange ℚ) v =
                  (n : ℚ)) := by
  sorry

end AlgebraicGeometry
