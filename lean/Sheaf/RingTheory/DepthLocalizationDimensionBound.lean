module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.DepthExt
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.DepthQuotSMulTop

/-!
# Depth under localization and the quotient dimension

Source: Stacks Project, Algebra, Tag 0FCC, `lemma-depth-localization`
(blueprint: lem-sfb-depth-localization-dimension-bound).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- The depth of a finite module over a Noetherian local ring is at most the depth of
its localization at a prime plus the Krull dimension of the quotient by that prime.
Both depths use the maximal ideals of the respective local rings. The coercions to
`WithBot ℕ∞` retain infinity and its addition; the quotient by a prime is nonzero,
so its dimension is never bottom. Zero modules and zero localizations are included.
Source: Stacks Project, Algebra, Tag 0FCC, `lemma-depth-localization`
(blueprint: lem-sfb-depth-localization-dimension-bound).

Proof, following the node's expanded proof of Stacks Tag 0FCC:
1. If the localization is zero, its depth is infinity and the inequality holds.
   Otherwise both modules are nonzero. The localized ring is local and Noetherian
   (def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian).
   Localized generators generate the localized module. The depth-Ext theorem
   (lem-weil-pbc-depth-ext) makes both depths finite. Put d = dim(R/p); it is
   nonnegative, and if it is infinite the inequality is automatic.
2. Induct strongly on depth_R(N), uniformly over finite modules N with nonzero
   localization. If depth_R(N) ≤ d, nonnegativity proves the claim.
3. Otherwise no associated prime q of N contains p: the associated-prime bound
   (lem-weil-pbc-depth-le-dim-associated-prime) gives depth_R(N) ≤ dim(R/q),
   whereas pulling prime chains back along R/p → R/q gives dim(R/q) ≤ d.
4. Associated primes are finite (lem-weil-pbc-noetherian-associated-primes-finite)
   and nonempty, since zero is a zerodivisor on N. Prime avoidance
   (lem-weil-pbc-prime-avoidance) chooses x in p outside all associated primes.
   The zerodivisor characterization
   (lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes) makes x
   injective on N.
5. Set Q = N/xN. It is finite. Localization exactness
   (lem-weil-pbc-localization-module-exact) identifies Q_p with N_p/xN_p and
   makes x/1 injective on N_p. This linear isomorphism preserves depth by
   transporting regular sequences and their successive quotients.
6. Since x lies in p and hence in the maximal ideal of R, the depth-drop theorem
   (lem-weil-pbc-depth-drops-by-one) gives Q nonzero with depth one less. Over R_p,
   x/1 is also in the maximal ideal, so the same theorem gives Q_p nonzero with
   depth one less than that of N_p.
7. Apply induction to Q and add one to the resulting inequality of finite natural
   numbers. This proves the induction step and the assertion for M; step 1 already
   treated all zero and infinite cases. -/
theorem depth_le_depth_localizedModule_add_ringKrullDim_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] :
    (depth (R := R) M : WithBot ℕ∞) ≤
      (depth (R := Localization.AtPrime p) (LocalizedModule p.primeCompl M) : WithBot ℕ∞) +
        ringKrullDim (R ⧸ p) := by
  sorry

end IsLocalRing
