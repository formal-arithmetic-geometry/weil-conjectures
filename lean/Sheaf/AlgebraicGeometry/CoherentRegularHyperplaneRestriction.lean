/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistMul
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# A common regular hyperplane and twisted restriction sequences

Source: Stacks Project, Varieties, Tags 08A0, 089Z and 0EGK, and the finite-family
remark following 08A0 (blueprint: lem-sfb-coherent-regular-hyperplane-restriction).

The helper maps use the actual section, tensor pullback and normalized adjunction.
The twist on the hyperplane is the pulled-back ambient twist, as in 0EGK.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

/-- The linear section with the given coefficients.
Source: Stacks, Tag 08A0 (blueprint: lem-sfb-coherent-regular-hyperplane-restriction). -/
def regularHyperplaneLinearSection (k : Type u) [Field k] (n : ℕ)
    (a : Fin (n + 1) → k) :
    Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤) :=
  ∑ j : Fin (n + 1),
    Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))) (a j) •
      twistOneSection (ULift.{u} (Fin (n + 1))) (Spec (.of k)) ⟨j⟩

/-- Multiplication on a twisted module by a section of the degree-one twist.
The degree is written `1 + d`, avoiding any choice of arithmetic transport.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-regular-hyperplane-restriction). -/
def regularHyperplaneMultiplication (k : Type u) [Field k] (n : ℕ)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules) (d : ℤ)
    (t : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) :
    E ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d ⟶
      E ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d) :=
  E ◁ twistMulHom rfl t

/-- Restriction to a closed subscheme, with the canonical tensor comparison.
The value is `i^* E ⊗ i^* L`, so for `L = O(d)` it is exactly `G(d)`.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-regular-hyperplane-restriction). -/
def regularHyperplaneRestriction {X H : Scheme.{u}} (i : H ⟶ X) (E L : X.Modules) :
    E ⊗ L ⟶ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.tensorPullback i).obj E ⊗ (Scheme.Modules.tensorPullback i).obj L) :=
  (Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app (E ⊗ L) ≫
    (Scheme.Modules.pushforward i).map (Scheme.Modules.boundaryPullbackTensorIso i E L).hom

/-- Multiplication by the restricted linear section on the restricted twisted module.
This is tensor pullback of the actual ambient multiplication, through the tensor comparison.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-regular-hyperplane-restriction). -/
def regularHyperplaneRestrictedMultiplication (k : Type u) [Field k] (n : ℕ)
    {H : Scheme.{u}} (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules) (d : ℤ)
    (t : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) :=
  (Scheme.Modules.boundaryPullbackTensorIso i E
      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).inv ≫
    (Scheme.Modules.tensorPullback i).map (regularHyperplaneMultiplication k n E d t) ≫
    (Scheme.Modules.boundaryPullbackTensorIso i E
      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))).hom

/-- The connecting map after the canonical closed-pushforward cohomology comparison.
The standard derived categories fix sizes without adding a hypothesis to the statement.
Source: Stacks, Tag 0EGK (blueprint: lem-sfb-coherent-regular-hyperplane-restriction). -/
def regularHyperplaneConnecting {X H : Scheme.{u}} (i : H ⟶ X)
    {A B : X.Modules} {N : H.Modules} (f : A ⟶ B)
    (g : B ⟶ (Scheme.Modules.pushforward i).obj N) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) (q : ℕ)
    (h : IsIso (Scheme.Modules.moduleCohomologyEdgeMap i N q)) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology H.toRingedSpace q).obj N) ⟶
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj A) :=
  @inv _ _ _ _ (Scheme.Modules.moduleCohomologyEdgeMap i N q) h ≫
    (forget₂ _ AddCommGrpCat.{u}).map
      (@RingedSpace.moduleCohomologyBoundary X.toRingedSpace
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (ShortComplex.mk f g w) hS q)

/-- One linear section is regular for every member of a finite coherent family.
Here `i^* O(d)` is the twist on `H`; the displayed scheme isomorphism identifies it
with the standard twist on projective space of dimension `n - 1`. The degree pair
`d, 1 + d` parametrizes exactly the pairs `d - 1, d` in the source.

Source: Stacks, Tags 08A0, 089Z, 0EGK and the finite-family remark after 08A0
(blueprint: lem-sfb-coherent-regular-hyperplane-restriction).

Proof:
1. On the standard affine charts, the rings are finite type over the field and hence
   Noetherian (lem-wf-affine-noetherian-components). Coherence implies quasi-coherence
   (pqf-lem-coherent-ft-locnoeth). Coherent affine sections are finite modules
   (lem-weil-pbc-coherent-affine-sections-finite), and the tilde counit identifies
   their associated sheaves with the given modules
   (lem-weil-pbc-affine-tilde-gamma-adjunction). The twist frames identify section
   multiplication with multiplication by a_j + sum of a_l times T_l/T_j.
2. Each finite module has finitely many associated primes
   (lem-weil-pbc-noetherian-associated-primes-finite). Each prime excludes a proper
   linear subspace of coefficient vectors: the j-th unit vector maps to 1. Avoid
   all these finitely many subspaces and the zero subspace simultaneously
   (lem-pc-finite-linear-avoidance). This also handles the empty family.
3. The associated-prime description of module zerodivisors
   (lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes) makes the
   chosen multiplication injective on each affine module. Clearing denominators
   preserves injectivity on localizations, hence on sheaves, for every twist
   (lem-weil-pbc-spec-module-tilde-sections).
4. The quotient graded ring by the linear form defines its closed zero scheme.
   Eliminate a variable with nonzero coefficient to identify the quotient with a
   polynomial ring on n variables. Proj functoriality gives H isomorphic to P^(n-1)
   (prop-nagata-relative-proj-functoriality), over k.
5. The transition functions of all pulled-back twists agree with the standard
   transitions, including negative powers (def-pc-projective-space-twist).
   Affine pullback is M tensor A/(f), which is finite, so the restricted modules
   are coherent (lem-weil-pbc-module-pullback-quasi-coherent,
   lem-weil-pbc-module-pullback-affine-sections, pqf-lem-coherent-ft-locnoeth).
6. On every chart the cokernel is M/fM, canonically M tensor A/(f), with quotient
   arrow m to m tensor 1. The tilde adjunction preserves cokernels and the formulas
   commute with localization, so they glue to the stated restriction sequence
   (lem-weil-pbc-affine-tilde-gamma-adjunction). The tensor comparison writes its
   final term as the pushforward of G tensor i^* O(d).
7. The natural module/abelian cohomology comparison
   (lem-sc-module-abelian-zariski-cohomology), the topological description
   (def-sc-topological-abelian-cohomology), and closed-embedding invariance
   (lem-sc-cohomology-closed-immersion-pushforward) make the canonical edge maps
   isomorphisms in every nonnegative degree, naturally in the restricted module.
8. Enough injectives and left exact global sections
   (lem-sc-ringed-space-module-sheaves-enough-injectives,
   lem-sc-global-sections-left-exact) give the associated long exact sequence
   (lem-weil-pbc-derived-functor-long-exact, pqf-def-cohomology). Transport its
   third term through the edge map to obtain the two asserted exact positions;
   regularHyperplaneConnecting is precisely its transported connecting morphism.
9. For any chosen-module map u, u(fm)=f u(m) and restriction sends u(m) to
   (u tensor 1)(m tensor 1). For another linear form t, restriction sends tm to
   the restricted t times the restricted m. These identities localize and glue,
   proving naturality of both sequence arrows and multiplication compatibility.
   The edge-map square follows from the same natural cohomology comparisons. -/
theorem exists_coherent_regular_hyperplane (k : Type u) [Field k] [Infinite k]
    (n : ℕ) (hn : 1 ≤ n) (v : ℕ)
    (E : Fin v → (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules)
    (hE : ∀ α, RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace (E α)) :
    ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ regularHyperplaneLinearSection k n a ≠ 0 ∧
      ∃ (H : Scheme.{u}) (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))),
        IsClosedImmersion i ∧
        i.ker = Scheme.Modules.Hom.zeroLocus
          (Scheme.Modules.homOfGlobalSection _ (regularHyperplaneLinearSection k n a)) ∧
        ∃ e : H ≅ ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)),
          e.hom ≫ (ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)) ↘ Spec (.of k)) =
            i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)) ∧
          (∀ d : ℤ, Nonempty
            ((Scheme.Modules.tensorPullback i).obj
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≅
              (Scheme.Modules.tensorPullback e.hom).obj
                (twist (ULift.{u} (Fin ((n - 1) + 1))) (Spec (.of k)) d))) ∧
          (∀ α, RingedSpace.IsCoherent H.toRingedSpace
            ((Scheme.Modules.tensorPullback i).obj (E α))) ∧
          (∀ (α : Fin v) (d : ℤ),
            ∃ w : regularHyperplaneMultiplication k n (E α) d
                (regularHyperplaneLinearSection k n a) ≫
              regularHyperplaneRestriction i (E α)
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)) = 0,
            ∃ hS : (ShortComplex.mk
              (regularHyperplaneMultiplication k n (E α) d
                (regularHyperplaneLinearSection k n a))
              (regularHyperplaneRestriction i (E α)
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) w).ShortExact,
            ∀ q : ℕ, ∃ h : IsIso (Scheme.Modules.moduleCohomologyEdgeMap i
              (MonoidalCategoryStruct.tensorObj (C := H.Modules)
                ((Scheme.Modules.tensorPullback i).obj (E α))
                ((Scheme.Modules.tensorPullback i).obj
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)))) q),
              Function.Exact
                ((forget₂ _ AddCommGrpCat.{u}).map
                  ((RingedSpace.moduleCohomology
                    (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace q).map
                    (regularHyperplaneMultiplication k n (E α) d
                      (regularHyperplaneLinearSection k n a))))
                (Scheme.Modules.moduleCohomologyFMap i
                  (regularHyperplaneRestriction i (E α)
                    (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) q) ∧
              Function.Exact
                (Scheme.Modules.moduleCohomologyFMap i
                  (regularHyperplaneRestriction i (E α)
                    (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) q)
                (regularHyperplaneConnecting i
                  (regularHyperplaneMultiplication k n (E α) d
                    (regularHyperplaneLinearSection k n a))
                  (regularHyperplaneRestriction i (E α)
                    (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d))) w hS q h)) ∧
          (∀ (α β : Fin v) (u : E α ⟶ E β) (d : ℤ),
            regularHyperplaneMultiplication k n (E α) d
                (regularHyperplaneLinearSection k n a) ≫
                (u ▷ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)) =
              (u ▷ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≫
                regularHyperplaneMultiplication k n (E β) d
                  (regularHyperplaneLinearSection k n a) ∧
            regularHyperplaneRestriction i (E α)
                (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≫
                (Scheme.Modules.pushforward i).map
                  ((Scheme.Modules.tensorPullback i).map u ▷
                    (Scheme.Modules.tensorPullback i).obj
                      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) =
              (u ▷ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≫
                regularHyperplaneRestriction i (E β)
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) ∧
          (∀ (α : Fin v) (d : ℤ)
            (t : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)),
            regularHyperplaneMultiplication k n (E α) d t ≫
                regularHyperplaneRestriction i (E α)
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (1 + d)) =
              regularHyperplaneRestriction i (E α)
                  (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≫
                (Scheme.Modules.pushforward i).map
                  (regularHyperplaneRestrictedMultiplication k n i (E α) d t)) ∧
          (∀ (α β : Fin v) (u : E α ⟶ E β) (d : ℤ) (q : ℕ),
            (forget₂ _ AddCommGrpCat.{u}).map
                ((RingedSpace.moduleCohomology
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace q).map
                  ((Scheme.Modules.pushforward i).map
                    ((Scheme.Modules.tensorPullback i).map u ▷
                      (Scheme.Modules.tensorPullback i).obj
                        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)))) ≫
                Scheme.Modules.moduleCohomologyEdgeMap i
                  (MonoidalCategoryStruct.tensorObj (C := H.Modules)
                ((Scheme.Modules.tensorPullback i).obj (E β))
                    ((Scheme.Modules.tensorPullback i).obj
                      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d))) q =
              Scheme.Modules.moduleCohomologyEdgeMap i
                  (MonoidalCategoryStruct.tensorObj (C := H.Modules)
                ((Scheme.Modules.tensorPullback i).obj (E α))
                    ((Scheme.Modules.tensorPullback i).obj
                      (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d))) q ≫
                (forget₂ _ AddCommGrpCat.{u}).map
                  ((RingedSpace.moduleCohomology H.toRingedSpace q).map
                    ((Scheme.Modules.tensorPullback i).map u ▷
                      (Scheme.Modules.tensorPullback i).obj
                        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)))) := by
  sorry

end
end AlgebraicGeometry.ProjectiveSpace
