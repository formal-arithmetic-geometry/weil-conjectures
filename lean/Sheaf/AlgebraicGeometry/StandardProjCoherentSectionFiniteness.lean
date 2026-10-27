module

public import Sheaf.AlgebraicGeometry.StandardProjTwistTensor
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # Finite generation of nonnegative coherent twisted sections

Source: Stacks Project, coherent.tex, Tag 0AG6, lemma-coherent-on-proj, opening
assertion and part (4), with k = 0; Tag 01YS, lemma-coherent-projective, part (5).
(blueprint: lem-sfb-standard-proj-coherent-section-finiteness).

The homogeneous-action equations specify the canonical S-module structure, rather
than assuming a module structure. Graded-ring decomposition and additivity determine
its action on all scalars and all elements of the direct sum. The map twistMul is
multiplication by the canonical section of the twist, equivalently multiplication
through the canonical tensor comparison of standardProjTwistTensor.
On the Noetherian Proj asserted here, coherence is equivalent to quasi-coherence
and finite type by Stacks 01XZ; the statement uses the recorded predicate for this.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules
open scoped DirectSum

namespace AlgebraicGeometry.Proj

/-- Proj of a standard graded algebra over a Noetherian degree-zero ring is
Noetherian. For every coherent module, its nonnegative twisted-section sum has
the canonical homogeneous action and is finite for that action.

Source: Stacks Project, coherent.tex, Tag 0AG6, opening and (4), specialized to k=0,
and Tag 01YS, proof of (5); Tag 01XZ identifies coherence with quasi-coherence
and finite type on the Noetherian scheme X.
(blueprint: lem-sfb-standard-proj-coherent-section-finiteness).

Proof:
1. Put R = S_0. Choose degree-one algebra generators, padding with zero generators
   to obtain r >= 1, and a graded surjection C = R[T_0,...,T_r] onto S. The opens
   D_+(s_j) cover Proj, since a prime containing all s_j contains S_+. Apply
   prop-nagata-relative-proj-functoriality to obtain a closed immersion i into P^r_R.
2. By lem-weil-pbc-proj-polynomial-twist-chart the projective charts are polynomial
   rings over R. By lem-sfb-graded-proj-quotient-twist-comparison their inverse images
   are the quotient charts of X, with surjective coordinate-ring maps. These finite
   type R-algebras are Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
   Thus both P and X have finite Noetherian affine covers, including empty X.
3. Set G = i_*F. By lem-pc-closed-immersion-coherent-cohomology it is coherent and
   satisfies the projection isomorphisms. The local frames T_j^d identify the
   projective twists with shifted-module twists; their transition is (T_j/T_l)^d.
   The quotient twist comparison identifies their pullbacks with O_X(d). Taking
   sections gives H^0(P,G(d)) = H^0(X,F(d)), compatibly with multiplication: the
   projection map sends g tensor t to g tensor i^*t and a polynomial c to psi(c).
   Hence the section sums identify as C-modules by restriction along C -> S.
4. By lem-pc-projective-space-twist-quotient choose a finite sum E of O_P(-m_j),
   with m_j >= 0, surjecting onto G with coherent kernel K. Tensoring by O_P(d)
   stays exact by lem-sc-ext-tensor-exact and invertibility of the twist.
   lem-pc-twist-tensor identifies E(d). The long exact sequence from
   pqf-def-cohomology and lem-pc-projective-space-serre-vanishing give a b >= 0
   for which H^0(E(d)) -> H^0(G(d)) is surjective for d >= b. These maps respect
   homogeneous multiplication since they come from the fixed sheaf map E -> G.
5. As r >= 1, lem-pc-projective-space-twist-cohomology identifies H^0(O(d-m_j))
   with C_(d-m_j), zero in negative degree. On a chart its coefficient is
   a/T_l^(d-m_j), so multiplication by c acts as c/T_l^e. Thus the nonnegative
   section sum Q of E is the finite graded free sum of C(-m_j). The ring C is
   Noetherian. Its submodule Q_{>=b} is finite by
   lem-weil-pbc-noetherian-submodule-finite and surjects onto the high section tail.
   The images of finite generators generate that tail.
6. Each low twist G(d) is coherent, being locally G, so its H^0 is finite over R
   by lem-pc-projective-space-coherent-finiteness. Add their finite generators in
   the finitely many degrees 0 <= d < b to the high-tail generators. Every section
   sum has finite support and is their C-linear combination. The action factors
   through C -> S, so the same generators work over S. For b=0 there are no low
   generators; for F=0 or empty X the empty family generates. The homogeneous
   action is precisely multiplication by s/1, expressed by twistMul below.
-/
theorem standardProjCoherentSectionFiniteness
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    [IsNoetherianRing (𝒜 0)]
    (hgen : ∃ (r : ℕ) (f : Fin r → S),
      (∀ i : Fin r, f i ∈ 𝒜 1) ∧ Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    IsNoetherian (Proj 𝒜) ∧
    ∀ (F : (Proj 𝒜).Modules), Scheme.Modules.IsQuasiCoherentFiniteType F →
    ∃ m : Module S (⨁ n : ℕ, Γ(F ⊗ twist 𝒜 (n : ℤ), ⊤)),
      (∀ (e n : ℕ) (s : S) (hs : s ∈ 𝒜 e)
        (t : Γ(F ⊗ twist 𝒜 (n : ℤ), ⊤)),
        @SMul.smul S (⨁ k : ℕ, Γ(F ⊗ twist 𝒜 (k : ℤ), ⊤)) m.toSMul s
            (DirectSum.of (fun k : ℕ ↦ Γ(F ⊗ twist 𝒜 (k : ℤ), ⊤)) n t) =
          DirectSum.of (fun k : ℕ ↦ Γ(F ⊗ twist 𝒜 (k : ℤ), ⊤)) (n + e)
            (Hom.app ((F ◁ twistMul (n : ℤ) hs) ≫
              eqToHom (congrArg (fun z : ℤ ↦ F ⊗ twist 𝒜 z)
                (Int.natCast_add n e).symm)) ⊤ t)) ∧
      @Module.Finite S (⨁ n : ℕ, Γ(F ⊗ twist 𝒜 (n : ℤ), ⊤)) _ _ m := by
  sorry

end AlgebraicGeometry.Proj
