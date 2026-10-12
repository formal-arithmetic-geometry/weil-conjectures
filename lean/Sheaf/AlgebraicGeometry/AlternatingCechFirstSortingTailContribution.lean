module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open Classical in
/-- Tail-labelled junction deletions contribute the negatives of the advanced stages.
Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.

Proof: For each fixed sigma and a, the permutation satisfying the partial
sorting filter is unique: its prefix is sigma below a and its tail is the
increasing enumeration of the unused labels. The same construction defines
the unique partial permutation rho at stage a+1 (including stage p+2).
Let tau be the stage-a permutation and b = tau.symm (sigma a). Then b >= a,
since a label in the fixed prefix cannot equal sigma a by injectivity.
The tail junction label sigma a occurs exactly at r = b+1. Removing that
position leaves rho, obtained from tau by moving the entry at b to a and
shifting entries a through b-1 one place right. This fixes sigma through a
and leaves the remaining tail increasing. This move has sign (-1)^(b-a),
including b=a when it is the identity. Thus sign(rho) = (-1)^(b-a) sign(tau).
The deletion coefficient (-1)^a (-1)^(b+1) sign(tau) equals -sign(rho),
because a+b+1 and b-a+1 differ by 2a. Comparing all projections with
indexMap_pr and the fibre product universal property identifies the two
index-map composite with the map for rho. Functoriality and additivity of F
therefore turn the unique tail term into the negative stage-a+1 term.
Apply this for each sigma, retaining its stable sorting filter on both sides,
and sum over a and sigma. At the last a, tau=rho=sigma and b=a, so the same
argument still applies. Labels, rather than their values in I, are compared,
so repetitions in t cause no extra terms; an empty I admits no such t.
(blueprint: lem-pc-alternating-cech-first-sorting-junction-tail-contribution) -/
theorem cechFirstSortingJunctionTailContribution (X : Scheme.{u}) {I : Type v}
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
    let T := ∑ σ, ∑ a, ∑ τ, ∑ r,
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ a.val < r.val then E σ a τ r else 0
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ, ∑ τ, if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    T = - ∑ a : Fin (p + 2), B (a.val + 1) t := by sorry
end AlgebraicGeometry.Scheme
