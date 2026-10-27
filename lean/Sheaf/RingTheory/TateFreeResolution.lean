module

public import Sheaf.RingTheory.DividedPowerDGA
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Tate resolutions with a prescribed polynomial augmentation

Source: Stacks Project, `dpa.tex`, Tag 09PN (`lemma-tate-resolution`), properties
(1)--(4), the Noetherian finiteness assertion and the monomial construction.
(blueprint: lem-sfb-tate-free-resolution)

The degree-zero identification is an injective algebra map with image exactly the
zero component. The tower is the recorded polynomial presentation, with its initial
polynomial algebra fixed and a finite set of variables in degree `k + 1` at step `k`.
The homology equivalence is required to be the one induced by the augmentation.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace GradedAlgebra

/-- A prescribed finite polynomial surjection over a Noetherian ring extends to a
polynomial divided-power DGA resolution, with finitely many variables in each positive
degree and free coefficient modules. Source: Stacks Project, Tag 09PN
(blueprint: lem-sfb-tate-free-resolution).

Proof: The polynomial ring P is Noetherian by
`lem-weil-pbc-finite-type-algebra-noetherian`, so its augmentation kernel has a finite
list of generators (`def-weil-pbc-noetherian-ring`). Start with P in degree zero.
Adjoin a degree-one exterior variable for every kernel generator using
`lem-sfb-adjoin-dga-cycle`. The variable-adjunction coordinates
(`lem-sfb-divided-power-variable-adjunction`) show that H_0 is S via the prescribed
map, and each component at this finite stage is finite free over P.

Inductively, after adjoining variables through degree m, the degree-m term is finite
free over P on the exterior and divided monomials. Its cycle submodule has finitely
many generators by `lem-weil-pbc-noetherian-submodule-finite`. Adjoin variables of
degree m+1 with differentials these cycle representatives. The cycle-adjunction
lemma extends the differential and divided powers. These adjunctions kill H_m and
leave the homology below m unchanged: only the new degree-(m+1) generators contribute
new boundaries in degree m. Extend the augmentation by zero on positive degrees.

Take the increasing union of these stages using the variable-adjunction union
presentation. All operations agree on overlaps and every identity holds in a finite
stage. For each i the terms and differentials computing H_i stabilize by stage i+1;
therefore H_0 is S by the augmentation and every positive homology vanishes. Only
finitely many variables occur in each degree. Their exterior and divided monomials
of a fixed total degree give a finite P-basis. Expanding their coefficients in the
ordinary polynomial monomial R-basis (`def-weil-pbc-mv-polynomial-ring`) gives an
R-basis in every degree. Surjectivity and the augmentation-kernel calculation give
exactness at degree zero; positive homology vanishing gives exactness elsewhere.
The construction allows empty lists of generators throughout. -/
theorem exists_tate_free_resolution (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Type v) [CommRing S] [Algebra R S] (n : ℕ)
    (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π) :
    ∃ (A : VariableAdjunction.AlgebraData.{u, max u v} R)
      (D : DividedPowerDGA A.grade)
      (ι : MvPolynomial (Fin n) R →ₐ[R] A.Carrier) (ε : A.Carrier →ₐ[R] S),
      Function.Injective ι ∧
      (∀ x : A.Carrier, x ∈ A.grade 0 ↔ ∃ f : MvPolynomial (Fin n) R, ι f = x) ∧
      ε.comp ι = π ∧
      (∀ (i : ℕ) (x : A.Carrier), 0 < i → x ∈ A.grade i → ε x = 0) ∧
      (∀ x : A.Carrier, ε (D.d x) = 0) ∧
      (∃ h : D.homology 0 ≃ₗ[R] S, ∀ z : D.chainComplex.cycles 0,
        h (D.chainComplex.homologyπ 0 z) =
          ε (Subtype.val (@id (integerComponent A.grade 0) (D.chainComplex.iCycles 0 z)))) ∧
      (∀ i : ℕ, 0 < i → Subsingleton (D.homology (i : ℤ))) ∧
      (∀ i : ℕ, Module.Free R (A.grade i)) ∧
      Function.Exact (D.componentDifferential 0).hom
        (ε.toLinearMap.domRestrict (integerComponent A.grade 0)) ∧
      ∃ (B : ℕ → VariableAdjunction.AlgebraData.{u, max u v} R)
        (γ : ∀ k : ℕ, GradedDividedPowers (B k).grade)
        (b : MvPolynomial (Fin n) R ≃ₐ[R] (B 0).Carrier)
        (J : ℕ → Type (max u v)),
        (∀ m : ℕ, (B 0).grade m = if m = 0 then ⊤ else ⊥) ∧
        (∀ k : ℕ, Finite (J k)) ∧
        ∃ p : ∀ k : ℕ, VariableAdjunction.SetPresentation (B k) (γ k)
          (k + 1) (J k) (B (k + 1)),
          (∀ k : ℕ, VariableAdjunction.SetNormalized (p k) (γ (k + 1))) ∧
          ∃ q : VariableAdjunction.UnionPresentation B γ (fun k : ℕ ↦ k + 1) J p A,
            (q.into 0).toAlgHom.comp b.toAlgHom = ι ∧
            ∀ k : ℕ, VariableAdjunction.Preserves (q.into k) (γ k) D.toGradedDividedPowers
    := by
  sorry

end GradedAlgebra
