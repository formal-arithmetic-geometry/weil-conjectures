module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open Classical in
/-- Prefix-labelled junction deletions contribute the unadvanced partial sorting stages.
Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.

Proof: Fix sigma, a and a partial sorting permutation tau. In the prefix of
q = cechJunction sigma tau a, q(r) = sigma(r). Injectivity of sigma shows
that q(r) = sigma(a) and r <= a hold exactly when r = a. Removing this
position gives q composed with a.succAbove = tau: below a this uses the
fixed-prefix condition, and at and above a it uses the tail branch of q.
The composite of the two index maps is the index map for tau, since their
composites with every projection agree by indexMap_pr and the chosen fibre
product universal property. Apply functoriality of F and move integer scalar
multiplication through its additive maps. The two powers (-1)^a multiply
to 1, so the remaining term is sign(tau) times the restriction along tau.
For a pair failing the stable or partial sorting filter, both contributions
are zero. The partial sorting filter is exactly the filter defining B(a).
Summing these identities over r, tau, a and sigma, and commuting the sigma
and a sums, gives the claimed equality. No uniqueness of stable sorting is
needed here. Repeated values of t are harmless since deletion uses labels.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-prefix-contribution) -/
theorem cechFirstSortingJunctionPrefixContribution (X : Scheme.{u}) {I : Type v}
    [LinearOrder I] (U : I → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) :
    let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
        (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
      ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
        F.map (S.indexMap t (cechJunction σ τ a)).op
          ((-1 : ℤ) ^ r.val •
            F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
              (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
    let P := ∑ σ, ∑ a, ∑ τ, ∑ r,
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ r.val ≤ a.val then E σ a τ r else 0
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ, ∑ τ, if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    P = ∑ a : Fin (p + 2), B a.val t := by sorry
end AlgebraicGeometry.Scheme
