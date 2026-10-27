module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
import Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup
import Mathlib.RingTheory.Flat.Basic

/-!
# A torus-stable central vector subgroup of a split unipotent group

Source: Conrad--Lichtenstein, Linear Algebraic Groups I, Appendix D.3,
proof of Theorem D.3.2, printed p.86; Conrad, The structure of solvable groups
over general fields, Theorem 2.6, Corollary 2.7 and Proposition 3.2, pp.12--16;
Milne, Algebraic Groups (2017), Proposition 14.32, p.289.
(blueprint: lem-sfb-split-unipotent-central-vector-subgroup).

The split series and faithful geometric matrix unipotence use the existing definitions.
`ModObj` supplies an actual action morphism and its unit and associativity diagrams.
Multiplication preservation, subgroup stability, and centrality are tested on all algebras.
The group isomorphism with a power of G_a carries no equivariance or linearity condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A nontrivial split unipotent group has a nonzero central vector subgroup stable
under the given split torus action, over an arbitrary field.
Source: Conrad--Lichtenstein, Linear Algebraic Groups I, proof of Theorem D.3.2, p.86;
Conrad, The structure of solvable groupsover general fields, Theorem 2.6,
Corollary 2.7 and Proposition 3.2, pp.12--16; Milne, Proposition 14.32, p.289.
(blueprint: lem-sfb-split-unipotent-central-vector-subgroup).

Proof:
1. In characteristic zero form the represented centre Z(U) using
lem-sfb-affine-group-centre-base-change, then its open-and-closed identity component C
using lem-sfb-finite-type-group-identity-subgroup. Cartier smoothness
(lem-sfb-char-zero-affine-group-smooth) and the identity section
(lem-sbc-connected-rational-point-geometrically-connected) make C smooth and geometrically
connected. The central G_a supplied by lem-sfb-unipotent-central-additive-subgroup lies in
C, so C is nontrivial.
2. A closed unitriangular embedding of U from
lem-sfb-geometric-unipotence-unitriangular-embedding restricts to C. The theorem
lem-sfb-char-zero-commutative-unipotent-vector-group gives C isomorphic to G_a^d.
Nontriviality excludes d = 0.
3. In positive characteristic p the last nontrivial term of the split additive series
is G_a, yielding a nonconstant affine-line map into U. Thus U is not wound. By
lem-sfb-unipotent-cckp-kernel-wound-criterion its canonical smooth connected central
p-torsion subgroup F is not wound either.
4. Apply lem-sfb-commutative-p-torsion-vector-wound-factor to F. Its canonical vector
factor C has positive dimension because F is not wound. It is closed, smooth, central
in U and geometrically connected, the latter also following from C being a vector group.
5. Over the separable closure, every group automorphism preserves C: in characteristic
zero use centre base change and the identity component; in characteristic p use the
largest-subgroup characterization of F and the characterization of C by pointed
affine-line maps. Hence every point of the split torus over the separable closure
preserves this closed subgroup.
6. For f in the ideal of C, its pullback along E times C to U is a Laurent polynomial
with coefficients in k[C]. Over the infinite separable closure all evaluations vanish.
Resolve its finitely many coefficients in a vector-space basis and apply the polynomial
root bound successively in each variable, after multiplying by a monomial. All
coefficients vanish. Descend using lem-sfb-field-extension-tensor-injective. Thus the
action restricts to C as a morphism; its identities are inherited. If s = 0 evaluation
already is the identity. Since C is central in U, conjugation fixes its points over every
commutative k-algebra. No action linearity under the vector-group isomorphism is needed. -/
theorem exists_splitUnipotent_central_vector_subgroup {k : Type u} [Field k]
    (U : Grp (Over (Spec (.of k))))
    (hU : SolvableGroupStructure.IsAlgebraic U)
    (hunipotent : SolvableGroupStructure.IsUnipotent U)
    (hsplit : ∃ n : ℕ, SplitUnipotentLength U n)
    (hne : ¬ Nonempty (U ≅ Grp.trivial _)) (s : ℕ)
    [a : ModObj (MultiplicativeType.splitTorus k s).X U.X]
    (hautomorphism : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (e : StandardGroupSchemes.affine k R ⟶ (MultiplicativeType.splitTorus k s).X)
      (x y : StandardGroupSchemes.affine k R ⟶ U.X),
      lift e (x * y) ≫ a.smul = (lift e x ≫ a.smul) * (lift e y ≫ a.smul)) :
    ∃ (d : ℕ), 1 ≤ d ∧
      ∃ (C : Grp (Over (Spec (.of k)))) (i : C ⟶ U),
        IsClosedSubgroupScheme i.hom.hom ∧ Smooth C.X.hom ∧
        GeometricallyConnected C.X.hom ∧
        Nonempty (C ≅ ∏ᶜ (fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k))) ∧
        (∀ (R : Type u) [CommRing R] [Algebra k R]
          (e : StandardGroupSchemes.affine k R ⟶ (MultiplicativeType.splitTorus k s).X)
          (c : StandardGroupSchemes.affine k R ⟶ C.X),
          ∃ c' : StandardGroupSchemes.affine k R ⟶ C.X,
            c' ≫ i.hom.hom = lift e (c ≫ i.hom.hom) ≫ a.smul) ∧
        (∀ (R : Type u) [CommRing R] [Algebra k R]
          (x : StandardGroupSchemes.affine k R ⟶ U.X)
          (c : StandardGroupSchemes.affine k R ⟶ C.X),
          x * (c ≫ i.hom.hom) * x⁻¹ = c ≫ i.hom.hom) := by
  sorry

end AlgebraicGeometry
