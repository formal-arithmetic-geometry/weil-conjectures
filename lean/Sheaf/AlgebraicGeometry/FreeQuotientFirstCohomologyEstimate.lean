module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Floor
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # First cohomology of a coherent free quotient

Source: Stacks Project, varieties.tex, Tag 08AG, lemma-bound-quotients-free,
final numerical paragraph, at a positive twist
(blueprint: lem-sfb-free-quotient-first-cohomology-estimate).

The helpers specialize the recorded right-derived module cohomology and Euler
characteristic to twists on projective space; they introduce no new cohomology theory.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

/-- Right-derived module cohomology of `E(d)` on projective n-space, with scalars
restricted along its canonical structure map to the field.
Source: Stacks Project, Tags 01EO and 08AG, final numerical paragraph
(blueprint: lem-sfb-free-quotient-first-cohomology-estimate). -/
noncomputable def freeQuotientTwistCohomology (k : Type u) [Field k] (n : ℕ)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).Modules)
    (d : ℤ) (q : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    (Scheme.globalSectionsRingHom k
      (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))))).obj
    ((RingedSpace.moduleCohomology
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).toRingedSpace q).obj
        (E ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of k)) d :
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).Modules))

/-- The recorded Euler characteristic of `E(d)` on projective n-space over k.
Source: Stacks Project, Tags 08AE and 08AG, final numerical paragraph
(blueprint: lem-sfb-free-quotient-first-cohomology-estimate). -/
noncomputable def freeQuotientTwistEuler (k : Type u) [Field k] (n : ℕ)
    (E : (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).Modules)
    (d : ℤ) : ℤ :=
  (E ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of k)) d).eulerChar k

/-- Euler and first-cohomology estimates for a coherent quotient of a finite free sheaf.
Source: Stacks Project, varieties.tex, Tag 08AG, lemma-bound-quotients-free,
final numerical paragraph, at b >= 1
(blueprint: lem-sfb-free-quotient-first-cohomology-estimate).

Proof:
1. The twist L = O(b) is locally free of rank one. Tensor exactness
   (lem-sc-ext-tensor-exact) and symmetry give 0 -> K(b) -> L^r -> F(b) -> 0.
   The middle identification sends (a_i) tensor s to (a_i s); its inverse sends
   (s_i) to the sum of e_i tensor s_i. Bilinearity proves both inverse identities,
   and the maps commute with restriction. On a trivializing open, twisting leaves
   finite generation and finite generation of all finite-free kernels unchanged,
   so all three terms remain coherent. Projective properness
   (lemma-nagata-projective-space-base-change-proper) and proper coherent finiteness
   (lem-pc-euler-characteristic-well-defined) make all Euler sums finite.
2. The monomial computation (lem-pc-projective-space-twist-cohomology) gives
   h^0(L) = chi(L) = C = binomial(n+b,n), with no positive cohomology. Count the
   monomials by placing n separators among b+n positions. Coordinatewise copies of
   this basis give h^0(L^r) = r*C. Each L^j, j <= r, is coherent: finite generation
   descends under projection, and its finite-free kernels are those after composing
   with the split inclusion into L^r. Thus Euler additivity (lem-pc-euler-additive)
   for 0 -> L^j -> L^(j+1) -> L -> 0, starting at the zero sheaf, gives chi(L^r)=r*C.
3. Euler additivity in the twisted quotient sequence gives chi(K(b))=r*C-chi(F(b)).
   The initial long exact cohomology sequence (pqf-def-cohomology) injects sections
   of K(b) into those of L^r, whence h^0(K(b)) <= r*C by linear independence.
4. Vanishing in degrees at least two reduces the finite Euler sum to h^0-h^1.
   Rearrange to get h^1=h^0-chi(K(b)) <= chi(F(b)); dimensions are nonnegative.
5. If P represents every twisted Euler value, substitute at b. Then P(b) >= 0,
   and the defining ceiling inequality gives P(b) <= max(0,ceil(P(b))). -/
theorem freeQuotient_firstCohomology_estimate (k : Type u) [Field k]
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (b : ℤ) (hb : 1 ≤ b)
    (K F : (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).Modules)
    (i : K ⟶ SheafOfModules.free
      (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).ringCatSheaf)
      (ULift.{u} (Fin r)))
    (q : SheafOfModules.free
      (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).ringCatSheaf)
      (ULift.{u} (Fin r)) ⟶ F)
    (w : i ≫ q = 0) (hseq : (ShortComplex.mk i q w).ShortExact)
    (hK : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).toRingedSpace K)
    (hF : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).toRingedSpace F)
    (hvan : ∀ j : ℕ, 2 ≤ j →
      IsZero (freeQuotientTwistCohomology k n K b j)) :
    freeQuotientTwistEuler k n K b =
      (r * (n + b.toNat).choose n : ℕ) - freeQuotientTwistEuler k n F b ∧
    (Module.finrank k (freeQuotientTwistCohomology k n K b 0) : ℤ) ≤
      (r * (n + b.toNat).choose n : ℕ) ∧
    0 ≤ (Module.finrank k (freeQuotientTwistCohomology k n K b 1) : ℤ) ∧
    (Module.finrank k (freeQuotientTwistCohomology k n K b 1) : ℤ) =
      (Module.finrank k (freeQuotientTwistCohomology k n K b 0) : ℤ) -
        freeQuotientTwistEuler k n K b ∧
    (Module.finrank k (freeQuotientTwistCohomology k n K b 1) : ℤ) ≤
      freeQuotientTwistEuler k n F b ∧
    ∀ P : Polynomial ℚ,
      (∀ d : ℤ, (freeQuotientTwistEuler k n F d : ℚ) = P.eval (d : ℚ)) →
      0 ≤ (Module.finrank k (freeQuotientTwistCohomology k n K b 1) : ℚ) ∧
      (Module.finrank k (freeQuotientTwistCohomology k n K b 1) : ℚ) ≤ P.eval (b : ℚ) ∧
      P.eval (b : ℚ) ≤ (max 0 ⌈P.eval (b : ℚ)⌉ : ℤ) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
