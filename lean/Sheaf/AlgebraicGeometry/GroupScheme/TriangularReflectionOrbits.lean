module

public import Sheaf.AlgebraicGeometry.GroupScheme.TriangularReflectionData
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality

/-! # Signed reflection orbits from triangular group coordinates

Source: Milne, Algebraic Groups (2017), Theorem 23.31 and Remark 23.33, p.494;
the explicit triangular-coordinate supporting assertion and proof in the DAG
(blueprint: lem-sfb-triangular-reflection-orbits).

No reductivity or exhaustion of the adjoint weights is assumed. Root systems live
on their rational span. The equalities of conjugate subgroup functors quantify over
all commutative algebras, and over every word lifting a character automorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.TriangularReflection

/-- Triangular coordinates give a finite reduced crystallographic root system with
simple base D, well-defined signed root subgroups, and a word interchanging U and V.
Source: Milne, Theorem 23.31 and Remark 23.33, p.494; the explicit supporting
assertion in the DAG (blueprint: lem-sfb-triangular-reflection-orbits).

Proof plan, following the node's ten steps:
1. lem-sfb-torus-normalizer-components makes N_G(T)(F)/C_G(T)(F) finite. Its action
   on characters contains all specified reflections, hence W and WD are finite.
2. lem-sfb-multiplicative-character-antiduality identifies the split character and
   cocharacter lattices perfectly. The reflections preserve L = sum Z alpha.
   Extend each D-coefficient functional rationally and clear denominators to obtain
   a cocharacter positive on that one simple character and zero on the others.
3. A word-conjugated additive line has character rho = w alpha. Its cocharacter
   action is z maps to t^<rho,nu> z on every algebra. Positive or negative lambda
   height puts it in U or V. Zero height would put the additive line in T, impossible
   since every unit in F[z] is constant and a group map preserves the identity.
4. Restrict each nonnegative cocharacter's monoid action to the line in U. Pulling
   back its lifted coordinate gives a polynomial with localization t^k z. Thus k
   cannot be negative. Apply the coefficient cocharacters from step 2 to get all
   coefficients nonnegative; apply this to -rho for a negative-height line.
5. If tau = q rho, conjugate rho and tau back to simple roots in L. Their respective
   simple coordinates show q and its inverse integral, hence q is 1 or -1.
6. Average a positive definite form over finite W on the real span of L. For
   rho = w alpha, conjugating the specified reflection gives x maps to x-d(x)rho.
   Orthogonality identifies d(x) with 2 B(x,rho)/B(rho,rho), independently of its word.
7. These root reflections preserve R, and their Cartan pairings are integral by
   the lattice formula. Finiteness, spanning, reducedness and signed expansions
   give the reduced crystallographic root system with base D, on its rational span.
8. Any equivariant additive closed line of simple character alpha lies in U and
   is fixed by eta_alpha; hence it lies in Ua. A closed immersion Ga into Ga is an
   isomorphism: surjectivity of F[x] to F[z] forces its parameter polynomial to have
   degree one. Conjugate back to obtain word and simple-root independence for rho.
9. lem-sfb-root-chamber-simple-transitivity applied to this root system gives an
   element sending the base chamber to its opposite, hence w0 D = -D. Lift it to
   a word in the specified representatives and their inverses.
10. Step 8 identifies the word's conjugate of each Ua with the corresponding Va.
    Closed generation gives conjugation of U onto V. Apply the same argument to
    negative simple roots to get conjugation of V onto U. -/
theorem triangular_reflection_orbits {F : Type u} [Field F] [IsAlgClosed F]
    (d : Data F) :
    Finite d.weyl ∧ d.roots.Finite ∧
    (∃ (P : RootPairing d.roots ℚ d.rootSpace (Module.Dual ℚ d.rootSpace)) (b : P.Base),
      P.IsRootSystem ∧ P.IsReduced ∧ P.IsCrystallographic ∧
      (∀ (x : d.rootSpace) (f : Module.Dual ℚ d.rootSpace), P.toLinearMap x f = f x) ∧
      (∀ rho : d.roots, (P.root rho).val = (1 : ℚ) ⊗ₜ[ℤ] rho.val) ∧
      (∀ rho : d.roots, rho ∈ b.support ↔ rho.val ∈ d.D)) ∧
    (∀ rho : d.roots, ∃ c : d.D → ℤ,
      rho.val = ∑ alpha : d.D, c alpha • alpha.val ∧
        ((∀ alpha : d.D, 0 ≤ c alpha) ∨ (∀ alpha : d.D, c alpha ≤ 0))) ∧
    (∀ (h : d.words) (alpha : d.D),
      d.pairing (h.val.2 alpha.val) d.lam ≠ 0 ∧
      ∀ A : CommAlgCat.{u} F,
        (0 < d.pairing (h.val.2 alpha.val) d.lam →
          conjugatePoints (d.u alpha ≫ d.iU) h.val.1 A ⊆
            RankOneRoots.pointImage d.iU (StandardGroupSchemes.affine F A)) ∧
        (d.pairing (h.val.2 alpha.val) d.lam < 0 →
          conjugatePoints (d.u alpha ≫ d.iU) h.val.1 A ⊆
            RankOneRoots.pointImage d.iV (StandardGroupSchemes.affine F A))) ∧
    (∀ (h k : d.words) (alpha beta : d.D),
      h.val.2 alpha.val = k.val.2 beta.val → ∀ A : CommAlgCat.{u} F,
        conjugatePoints (d.u alpha ≫ d.iU) h.val.1 A =
          conjugatePoints (d.u beta ≫ d.iU) k.val.1 A) ∧
    ∃ h : d.words,
      h.val.2 '' (d.D : Set (TrivialTorusCoherent.Character d.T)) =
        (fun chi : TrivialTorusCoherent.Character d.T ↦ -chi) '' (d.D : Set _) ∧
      ∀ A : CommAlgCat.{u} F,
        conjugatePoints d.iU h.val.1 A =
          (RankOneRoots.pointImage d.iV (StandardGroupSchemes.affine F A) : Set _) ∧
        conjugatePoints d.iV h.val.1 A =
          (RankOneRoots.pointImage d.iU (StandardGroupSchemes.affine F A) : Set _) := by
  sorry

end AlgebraicGeometry.TriangularReflection
