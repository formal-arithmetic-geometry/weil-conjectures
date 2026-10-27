module

public import Sheaf.AlgebraicGeometry.GroupScheme.GeometricParabolicSubgroup
public import Sheaf.AlgebraicGeometry.GroupScheme.UniversalConjugationWeight
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Module
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections

/-! # Parabolics over a local ring are compared on their closed-fibre Lie algebras

Source: Conrad, Reductive group schemes, Corollary 5.2.7(2), printed pp.155--156
(blueprint: lem-sfb-local-parabolic-lie-inclusion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open IsLocalRing
open scoped MonObj

namespace AlgebraicGeometry.LocalParabolic

/-- The tangent subspace of a closed-fibre subgroup, inside the ambient Lie algebra.
The existing differential is composition of actual dual-number tangent points.
Source: Conrad, Corollary 5.2.7(2), p.155
(blueprint: lem-sfb-local-parabolic-lie-inclusion). -/
def lieImage {A : Type u} [CommRing A] [IsLocalRing A]
    {P G : Grp (Over (Spec (.of A)))} (i : P ⟶ G) :
    Submodule (ResidueField A)
      (GrpObj.Lie ((GeometricParabolic.fibre (residue A)).obj G).X) :=
  (GrpObj.differential ((GeometricParabolic.fibre (residue A)).map i).hom.hom).toLinearMap.range

/-- The χ-weight summand of a subgroup's closed-fibre tangent subspace, regarded
inside Lie(G_k). This uses all algebra-valued torus points, even for finite k.
Source: Conrad, Section 4.1 and Corollary 5.2.7(2), p.155
(blueprint: lem-sfb-local-parabolic-lie-inclusion). -/
def weightImage {A : Type u} [CommRing A] [IsLocalRing A]
    {T P G : Grp (Over (Spec (.of A)))} (iT : T ⟶ G) (iP : P ⟶ G)
    (χ : RankOneRoots.Character ((GeometricParabolic.fibre (residue A)).obj T)) :
    Submodule (ResidueField A)
      (GrpObj.Lie ((GeometricParabolic.fibre (residue A)).obj G).X) :=
  UniversalConjugationWeight.weight ((GeometricParabolic.fibre (residue A)).map iT) χ ⊓
    lieImage iP

/-- Parabolic inclusion, its equality consequence, and the full-character Borel
consequence over the residue field. Equality of embedded subgroups is expressed
by an isomorphism commuting with the embeddings, rather than equality of their
chosen representatives.

Source: Conrad, Corollary 5.2.7(2), printed pp.155--156
(blueprint: lem-sfb-local-parabolic-lie-inclusion).

Proof plan:
1. The closed subgroups are finitely presented: their coordinate algebras are
   quotients of a finite-type algebra over the Noetherian ring A, using
   lem-weil-pbc-finite-type-algebra-noetherian. Choose a cocharacter λ of T with
   P=P_G(λ) by lem-sfb-local-parabolic-cocharacter-description. It acts on Q.
2. By lem-sfb-relative-tangent-weight-base-change the relative tangent modules
   and their character summands are finite projective and commute with reduction.
   Closed subgroup differentials are injective and preserve characters. Coarsen
   along λ. By lem-sfb-relative-dynamic-subgroups, Lie(P) is the nonnegative part.
3. Closed-fibre inclusion kills every negative summand of Lie(Q) modulo m.
   Nakayama (lem-weil-pbc-nakayama-local-generators, empty generating family)
   kills these finite summands over A. There are only nonnegative weights.
4. Let R=P_Q(λ). By lem-sfb-relative-dynamic-subgroups it is smooth with the
   full tangent module of Q, compatibly with base change. On every geometric
   fibre, lem-sfb-smooth-subgroup-tangent-generation gives R_F=Q_F. Then
   lem-sfb-flat-geometric-fibre-open-criterion gives R=Q over A.
5. Every Q-point therefore has an extended λ-orbit. Composing this extension
   with Q→G gives membership in P_G(λ)=P. This proves subgroup inclusion on
   all algebras, hence as schemes. Exchange P,Q for the equality consequence.
6. For Borels, extend k to an algebraic closure. Naturality in
   lem-sfb-affine-group-lie-tangent-calculus and character base change in
   lem-sfb-relative-tangent-weight-base-change identify the tangent inclusions.
   By lem-sfb-regular-cocharacter-borel-description the Borel tangent spaces
   are Lie(T) plus the positive root spaces; lem-sfb-reductive-rank-one-reflections
   identifies the zero space and gives dimension one for each nonzero root space.
   Faithful extension of scalars descends these subspace equalities to k.
   Equality of the nonzero character supports then gives equality of tangent
   spaces and step 5 gives equality of Borels. Characters are never differentiated.
-/
theorem local_parabolic_lie_inclusion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (G P Q T : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsReductive ((GeometricParabolic.fibre f).obj G))
    (iP : P ⟶ G) (iQ : Q ⟶ G)
    [IsClosedImmersion iP.hom.hom.left] [IsClosedImmersion iQ.hom.hom.left]
    [Smooth P.X.hom] [Smooth Q.X.hom]
    (hP : GeometricParabolic.HasParabolicFibres iP)
    (hQ : GeometricParabolic.HasParabolicFibres iQ)
    (iT : T ⟶ G) [IsClosedImmersion iT.hom.hom.left]
    (jP : T ⟶ P) (jQ : T ⟶ Q) (hjP : jP ≫ iP = iT) (hjQ : jQ ≫ iQ = iT)
    (r : ℕ) (eT : T ≅ RingGroupSchemes.splitTorus A r)
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsMaximalTorus ((GeometricParabolic.fibre f).map iT)) :
    (lieImage iQ ≤ lieImage iP → ∃ j : Q ⟶ P, j ≫ iP = iQ) ∧
      (lieImage iP = lieImage iQ → ∃ e : P ≅ Q, e.hom ≫ iQ = iP) ∧
      (GeometricParabolic.HasBorelFibres iP → GeometricParabolic.HasBorelFibres iQ →
        (({χ | χ.hom.hom ≠ 1 ∧ weightImage iT iP χ ≠ ⊥} =
            {χ | χ.hom.hom ≠ 1 ∧ weightImage iT iQ χ ≠ ⊥} →
          ∃ e : P ≅ Q, e.hom ≫ iQ = iP) ∧
        weightImage iT iP 0 = lieImage iT ∧
        weightImage iT iQ 0 = lieImage iT ∧
        ∀ χ : RankOneRoots.Character ((GeometricParabolic.fibre (residue A)).obj T),
          χ.hom.hom ≠ 1 →
          (weightImage iT iP χ ≠ ⊥ →
            weightImage iT iP χ = UniversalConjugationWeight.weight
                ((GeometricParabolic.fibre (residue A)).map iT) χ ∧
              Module.finrank (ResidueField A) (UniversalConjugationWeight.weight
                ((GeometricParabolic.fibre (residue A)).map iT) χ) = 1) ∧
          (weightImage iT iQ χ ≠ ⊥ →
            weightImage iT iQ χ = UniversalConjugationWeight.weight
                ((GeometricParabolic.fibre (residue A)).map iT) χ ∧
              Module.finrank (ResidueField A) (UniversalConjugationWeight.weight
                ((GeometricParabolic.fibre (residue A)).map iT) χ) = 1))) := by
  sorry

end AlgebraicGeometry.LocalParabolic
