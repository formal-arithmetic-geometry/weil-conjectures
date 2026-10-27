/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Restriction and cohomology for a fixed regular hyperplane

Source: Stacks Project, Varieties, Tags 089Z, 08A0 and 0EGK
(blueprint: lem-sfb-fixed-hyperplane-restriction-cohomology).

## Main declarations

* `fixedHyperplaneGlobalSectionsMap`: the actual section map of an `i`-map.
* `fixedHyperplaneCohomologyMultiplication`: multiplication on module cohomology.
* `fixedHyperplaneCohomologyRestriction`: the specified cohomology restriction.
* `fixed_hyperplane_restriction_cohomology`: the short and long exact sequences,
  surjectivity for linear sections, and compatibility with products.

The section is prescribed, and its injectivity is a hypothesis. In particular the field
need not be infinite. The degree pair `d, 1 + d` runs over all pairs `D - 1, D`.
The module and section maps are the existing canonical hyperplane maps; the boundary is
transported through the specified cohomology edge map.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

/-- The actual map on global sections of an `i`-map, using restriction along
`i⁻¹(X) = H`. No identification with a freely chosen degree-zero isomorphism is used.
Source: Stacks, Cohomology, Tag 01FB and Varieties, Tag 0EGK
(blueprint: lem-sfb-fixed-hyperplane-restriction-cohomology). -/
def fixedHyperplaneGlobalSectionsMap {X H : Scheme.{u}} (i : H ⟶ X)
    {M : X.Modules} {N : H.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward i).obj N) : Γ(M, ⊤) → Γ(N, ⊤) :=
  fun m ↦ N.presheaf.map
    (eqToHom (by simp) : (⊤ : H.Opens) ⟶ i ⁻¹ᵁ (⊤ : X.Opens)).op (φ.app ⊤ m)

/-- Multiplication by a linear section on module sheaf cohomology, in degree `q`.
Source: Stacks, Tag 0EGK
(blueprint: lem-sfb-fixed-hyperplane-restriction-cohomology). -/
def fixedHyperplaneCohomologyMultiplication (k : Type u) [Field k] (n : ℕ)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules) (d : ℤ)
    (s : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) (q : ℕ) :=
  (forget₂ _ AddCommGrpCat.{u}).map
    ((RingedSpace.moduleCohomology
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace q).map
        (regularHyperplaneMultiplication k n E d s))

/-- The canonical restriction on cohomology: the `i`-map is the tensor-pullback unit
followed by the canonical pullback-tensor comparison. In degree zero it is the actual
restriction on sections, as in `fixedHyperplaneGlobalSectionsMap`.
Source: Stacks, Tags 01FB and 0EGK
(blueprint: lem-sfb-fixed-hyperplane-restriction-cohomology). -/
def fixedHyperplaneCohomologyRestriction (k : Type u) [Field k] (n : ℕ)
    {H : Scheme.{u}} (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules) (d : ℤ) (q : ℕ) :=
  Scheme.Modules.moduleCohomologyFMap i
    (regularHyperplaneRestriction i E
      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) q

/-- A fixed nonzero section acting injectively gives the restriction sequence and its
full long exact cohomology sequence. The three repeating exactness positions, together
with the initial injection in degree zero, specify the entire long exact sequence.
Restriction of linear sections is surjective and restriction commutes with multiplication.
On the right of the final identity, `regularHyperplaneRestrictedMultiplication` is
multiplication by the restricted linear section, through the canonical tensor comparison;
on a standard frame it sends `m e_j^(d)` to `c m e_j^(1+d)`. The penultimate clause says
that this multiplication depends only on the restriction `v|_H` of `v`, so that it is
multiplication by the section `v|_H` of `i^* O(1)` and the final identity is
`r_(1+d)(u v) = r_d(u) (v|_H)`.

Source: Stacks, Varieties, Tags 089Z, 08A0 and 0EGK, fixed-section variant
(blueprint: lem-sfb-fixed-hyperplane-restriction-cohomology).

Proof:
1. On a trivializing affine open write s = a e. The ideal of its zero scheme is (a),
   so the image of multiplication is I_H E(1+d). The closed-immersion unit-quotient
   theorem (lem-weil-pbc-closed-immersion-unit-quotient) identifies the quotient with
   i_* i^* E(1+d). The pullback-tensor comparison (lem-weil-pbc-module-pullback-tensor,
   lem-pc-twist-tensor) identifies this with i_*(i^*E tensor i^*O(1+d)). The quotient
   arrow is the normalized adjunction unit, hence precisely regularHyperplaneRestriction.
   The assumed injectivity makes this sequence short exact.
2. The standard affine charts of H have coordinate rings k[T_l/T_j]/(a_j), finite type
   over the Noetherian field k. They are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian, so H is locally Noetherian
   (pqf-def-locnoeth). Coherent i^*E is quasi-coherent by pqf-lem-coherent-ft-locnoeth;
   each pulled-back twist is locally free of rank one, so its tensor with i^*E is
   quasi-coherent. A closed immersion is affine.
3. Enough injectives (lem-sc-ringed-space-module-sheaves-enough-injectives) and left
   exact global sections (lem-sc-global-sections-left-exact) give the full derived
   long exact sequence (lem-weil-pbc-derived-functor-long-exact, pqf-def-cohomology).
4. Apply lem-weil-pbc-affine-morphism-cohomology-edge to the quasi-coherent restricted
   twists. The specified edge map is invertible. Transport the third terms and the
   boundaries through it; regularHyperplaneConnecting is exactly this boundary.
   The composition rule (lem-weil-pbc-module-cohomology-fmap-functorial) identifies
   the transported arrow with fixedHyperplaneCohomologyRestriction. The degree-zero
   rule (lem-weil-pbc-module-cohomology-fmap-basic-properties) identifies it with the
   actual map on sections. Transport by isomorphisms preserves all three exactness
   positions and the initial monomorphism.
5. By lem-pc-projective-space-twist-cohomology, nonzero s is a nonzero linear form.
   Its multiplier on every standard affine chart is a nonzero polynomial, so is a
   nonzerodivisor; this remains true after localization. Apply the same quotient
   calculation to O_X mapping into O_X(1). Since H^1(P^n_k,O_X) = 0 for n at least
   one by the same twist-cohomology calculation, the degree-zero sequence proves
   surjectivity of restriction of linear sections, also over finite fields.
6. The pullback-tensor comparison sends i^*(u tensor v) to i^*u tensor i^*v.
   In the standard frames the twist product is (m,c) mapping to cm; restriction
   sends the coefficients to their images in O_H. Both orders give c-bar m-bar.
   In particular the restricted multiplication only involves c-bar, the image of v
   in the sections of i^*O(1), so it depends only on v|_H. These identities glue
   and give the final section equality, including all
   negative twists (lem-weil-pbc-module-pullback-tensor, lem-pc-twist-tensor). -/
theorem fixed_hyperplane_restriction_cohomology (k : Type u) [Field k]
    (n : ℕ) (hn : 1 ≤ n)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules)
    (hE : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace E)
    (s : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) (hs : s ≠ 0)
    {H : Scheme.{u}} (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    [IsClosedImmersion i]
    (hH : i.ker = Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection _ s))
    (hG : RingedSpace.IsCoherent H.toRingedSpace ((Scheme.Modules.tensorPullback i).obj E))
    (hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n E d s)) :
    (∀ d : ℤ,
      ∃ w : regularHyperplaneMultiplication k n E d s ≫
        regularHyperplaneRestriction i E
          (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)) = 0,
      ∃ hS : (ShortComplex.mk (regularHyperplaneMultiplication k n E d s)
        (regularHyperplaneRestriction i E
          (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) w).ShortExact,
        Function.Injective (fixedHyperplaneCohomologyMultiplication k n E d s 0) ∧
        ∀ q : ℕ,
          ∃ he : IsIso (Scheme.Modules.moduleCohomologyEdgeMap i
            (MonoidalCategoryStruct.tensorObj (C := H.Modules)
              ((Scheme.Modules.tensorPullback i).obj E)
              ((Scheme.Modules.tensorPullback i).obj
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)))) q),
            Function.Exact (fixedHyperplaneCohomologyMultiplication k n E d s q)
              (fixedHyperplaneCohomologyRestriction k n i E (1 + d) q) ∧
            Function.Exact (fixedHyperplaneCohomologyRestriction k n i E (1 + d) q)
              (regularHyperplaneConnecting i (regularHyperplaneMultiplication k n E d s)
                (regularHyperplaneRestriction i E
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) w hS q he) ∧
            Function.Exact
              (regularHyperplaneConnecting i (regularHyperplaneMultiplication k n E d s)
                (regularHyperplaneRestriction i E
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) w hS q he)
              (fixedHyperplaneCohomologyMultiplication k n E d s (q + 1))) ∧
    Function.Surjective (fixedHyperplaneGlobalSectionsMap i
      ((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1))) ∧
    (∀ (d : ℤ) (v v' : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)),
      fixedHyperplaneGlobalSectionsMap i
          ((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1)) v =
        fixedHyperplaneGlobalSectionsMap i
          ((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1)) v' →
      regularHyperplaneRestrictedMultiplication k n i E d v =
        regularHyperplaneRestrictedMultiplication k n i E d v') ∧
    ∀ (d : ℤ) (u : Γ(E ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d, ⊤))
      (v : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)),
      fixedHyperplaneGlobalSectionsMap i
          (regularHyperplaneRestriction i E
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)))
          ((regularHyperplaneMultiplication k n E d v).app ⊤ u) =
        (regularHyperplaneRestrictedMultiplication k n i E d v).app ⊤
          (fixedHyperplaneGlobalSectionsMap i
            (regularHyperplaneRestriction i E
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) u) := by
  sorry

end
end AlgebraicGeometry.ProjectiveSpace
