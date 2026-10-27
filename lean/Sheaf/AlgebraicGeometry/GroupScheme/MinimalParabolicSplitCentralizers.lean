module

public import Sheaf.AlgebraicGeometry.GroupScheme.RationalParabolic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Split-torus centralizers in a minimal rational parabolic

Source: Milne, Algebraic Groups (2017), Theorem 25.6(b),(c), printed pp.545--546,
with the author's erratum imposing minimality in (b).
(blueprint: lem-sfb-minimal-parabolic-split-centralizers)

The two input tori are indexed by Fin 2. The radical is characterized by its largest
smooth geometrically connected normal unipotent subgroup property. The multiplication
map of underlying schemes is an isomorphism; normality identifies the induced action
with conjugation. The conjugacy is an equality of morphisms, hence of subgroup schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Centralizers of the two maximal split tori in a minimal rational parabolic are
reductive Levi complements, conjugate by a rational point of its unipotent radical.
Source: Milne, Theorem 25.6(b),(c), pp.545--546, with the author's p.545 erratum.
(blueprint: lem-sfb-minimal-parabolic-split-centralizers)

Proof plan:
1. For each torus S_i, lem-sfb-parabolic-prescribed-split-cocharacter gives a
   cocharacter lambda_i^0 in S_i with P = P(lambda_i^0), on all algebra points.
   Its hypothesis is maximality in P, so maximality in G is not presumed.
2. By lem-sfb-affine-group-faithful-linear-representation embed G in GL(V).
   Use lem-sfb-split-torus-representation-weight-decomposition for weights chi_a,
   and lem-sfb-split-torus-hom-matrices for integral character/cocharacter coordinates.
   Choose an integral mu avoiding all nonzero differences chi_a-chi_b: evaluating
   each nonzero linear form at (1,M,...,M^(r-1)) excludes finitely many integers M.
   For r = 0 use mu = 0. Put lambda_i = N lambda_i^0 + mu, with positive N larger
   than every absolute pairing of a weight difference with mu. Old nonzero signs
   persist; every nonzero weight difference now has nonzero pairing.
3. Conjugation by nu multiplies entry g_ab by t^(pairing(chi_a-chi_b,nu)).
   Extension over A[t] is equivalent to vanishing of negative-weight entries; the
   determinant remains invertible. Defining equations of the closed subgroup G
   descend from Laurent polynomials since A[t] embeds in A[t,t^-1]. Thus
   P(lambda_i) is contained in P. By lem-sfb-reductive-cocharacter-parabolic-geometry
   it is parabolic, hence equals P by minimality. Comparing Laurent coefficients
   shows that centralizing lambda_i imposes exactly the equations for centralizing
   S_i, including over nonreduced A. Write L_i = Z(lambda_i).
4. The same geometry gives smooth geometrically connected L_i and V_i = U(lambda_i),
   a retraction P -> L_i with kernel V_i, and multiplication V_i x L_i isomorphic
   to P. Over the algebraic closure, lem-sfb-reductive-torus-fixed-subgroup makes
   L_i reductive. Order the faithful basis by lambda_i-weight: the kernel's negative
   entries vanish and its weight-zero blocks are identity. Its matrices are block
   upper unitriangular, so (g-I)^dim(V) = 0. Thus V_i is unipotent as defined.
5. For any smooth geometrically connected normal unipotent N in P, extend to the
   algebraic closure. Factor its map to L_i by lem-sfb-affine-homomorphism-flat-image.
   The retraction is faithfully flat, since under P = V_i x L_i its coordinate map
   tensors with the nonzero vector space k[V_i]. By
   lem-sfb-unipotent-normal-quotient-image its image is smooth connected normal
   unipotent; reductivity of L_i makes it trivial. Thus N is contained in V_i after
   extension, and faithful scalar extension descends the defining-ideal inclusion.
   Conversely V_i has all these properties, hence V_1 = R_u(P) = V_2 = U.
6. Factor lambda_1 through its flat closed image T using
   lem-sfb-affine-homomorphism-flat-image. By lem-sfb-field-split-torus-flat-quotient,
   T and its image D under the second retraction are split tori. The inverse image
   of D is U semidirect D and contains T. The cocharacter geometry supplies U's
   additive series; lem-sbc-connected-rational-point-geometrically-connected makes
   its connected terms geometrically connected. Apply
   lem-sfb-split-unipotent-torus-absorption to obtain u in U(k) with uTu^-1 in D.
   Then nu = Int(u) lambda_1 lies in L_2, P(nu) = P, and C_G(nu) = uL_1u^-1 = M.
7. Since nu lies in L_2 = C_G(lambda_2), the cocharacters commute, so lambda_2 lies
   in M too. If a reductive J contains eta and lies in P(eta), its defining equations
   show P^J(eta) = J. Apply lem-sfb-reductive-cocharacter-parabolic-geometry in J;
   its kernel is unipotent by the weight decomposition and the unitriangular
   calculation of step 4. Reductivity, followed by faithful scalar descent, makes
   this kernel trivial. Hence J centralizes eta. Apply this first to (M,lambda_2)
   and then to (L_2,nu), obtaining M contained in L_2 and L_2 contained in M.
8. All formulas hold on every algebra, so the conjugacy is scheme-theoretic and
   uses the single rational u. Rank zero, empty weight-difference sets and zero
   cocharacters were allowed. If P = G is minimal, reductivity gives U = 1 and
   both centralizers equal G. No infinitude or perfectness was used. -/
theorem minimal_parabolic_split_centralizers
    {k : Type u} [Field k] (G P : Grp (Over (Spec (.of k))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iP : P ⟶ G) (hP : IsMinimalParabolicGroupScheme iP)
    (S : Fin 2 → Grp (Over (Spec (.of k)))) (iS : ∀ a : Fin 2, S a ⟶ P)
    (hclosed : ∀ a : Fin 2, IsClosedSubgroupScheme (iS a).hom.hom)
    (hsplit : ∀ a : Fin 2, ∃ r : ℕ, Nonempty (S a ≅ MultiplicativeType.splitTorus k r))
    (hmax : ∀ (a : Fin 2) (T : Grp (Over (Spec (.of k)))) (j : T ⟶ P),
      IsClosedSubgroupScheme j.hom.hom →
        (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)) →
          ∀ f : S a ⟶ T, f ≫ j = iS a → IsIso f) :
    ∃ (U : Grp (Over (Spec (.of k)))) (iU : U ⟶ P),
      IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj U).X.left ∧
      SolvableGroupStructure.IsUnipotent U ∧
      (∀ (N : Grp (Over (Spec (.of k)))) (j : N ⟶ P),
        IsClosedSubgroupScheme j.hom.hom → IsNormalSubgroupScheme j.hom.hom →
        ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj N).X.left →
        SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = j) ∧
      ∃ (L : Fin 2 → Grp (Over (Spec (.of k)))) (iL : ∀ a : Fin 2, L a ⟶ P),
        (∀ a : Fin 2,
          IsClosedSubgroupScheme (iL a).hom.hom ∧ ReductiveTorusCentralizer.IsReductive (L a) ∧
          (∀ (A : Type u) [CommRing A] [Algebra k A],
            ReductiveTorusCentralizer.centralizerPoints (iS a ≫ iP) A =
              Set.range (fun l : StandardGroupSchemes.affine k A ⟶ (L a).X ↦
                l ≫ (iL a ≫ iP).hom.hom)) ∧
          IsIso ((fst U.X (L a).X ≫ iU.hom.hom) *
            (snd U.X (L a).X ≫ (iL a).hom.hom)) ∧
          ∃ c : (L a).X ⊗ U.X ⟶ U.X,
            c ≫ iU.hom.hom =
              (fst _ _ ≫ (iL a).hom.hom) * (snd _ _ ≫ iU.hom.hom) *
                (fst _ _ ≫ (iL a).hom.hom)⁻¹) ∧
        ∃ (u : 𝟙_ (Over (Spec (.of k))) ⟶ U.X) (e : L 0 ≅ L 1),
          (toUnit (L 0).X ≫ u ≫ iU.hom.hom) * (iL 0).hom.hom *
            (toUnit (L 0).X ≫ u ≫ iU.hom.hom)⁻¹ =
              e.hom.hom.hom ≫ (iL 1).hom.hom := by
  sorry

end AlgebraicGeometry
