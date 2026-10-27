module

public import Sheaf.CategoryTheory.DgCharacterDualCoordinates

/-!
# Evaluation into shifted DG character duals

Source: literature/stacks-project/dga.tex, Tag 09K4,
lemma-hom-into-shift-dual-free, both natural identifications
(blueprint: lem-sfb-dg-shifted-character-dual-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- Evaluation at 1 identifies maps into the shifted character dual with dual
cycles and identifies their right-linear homotopy classes with dual cohomology.
The families of equivalences are characterized on every map and every quotient
representative, which also specifies their contravariant naturality.

Source: Stacks Project, dga.tex, Tag 09K4, lemma-hom-into-shift-dual-free
(blueprint: lem-sfb-dg-shifted-character-dual-hom).

Proof plan, following the six steps of the node:
1. Leibniz at 1 gives d(1)=0. Signed precomposition squares to zero. The
right action lambda(a b), associativity, and Leibniz give the indicated dual
DG structure; multiplying by (-1)^k gives the unchanged shifted action.
2. In degree t, evaluation has inverse lambda -> (m -> (a -> lambda(m a))).
Associativity proves right linearity and the unit proves both inverse identities.
3. For delta(phi)=d phi-(-1)^t phi d, the d_A terms cancel. Evaluation satisfies
E_(t+1)(delta(phi))=(-1)^k d(E_t(phi)); the d(1) term vanishes.
4. At t=0 this identifies chain maps with cycles, giving the first equivalence.
5. At t=-1 it identifies d h+h d with boundaries, in both directions: a boundary
 d(mu) lifts by h=F_(-1)((-1)^k mu). Thus evaluation descends to inverse maps
of the two quotients. Null maps are closed under addition and negation by
adding or negating their homotopies, so their subgroup closure is the same set.
6. Precomposition by u:N->M commutes with evaluation, since
(phi u)(n)(1)=phi(u(n))(1), and with the inverse since u(n a)=u(n) a.
It preserves both differentials and null-homotopies; therefore the formula on
quotient representatives gives naturality on cohomology as well. All formulas
are degreewise, with no boundedness, finiteness, or acyclicity assumption. -/
theorem shiftedCharacterDualHom (A : Algebra.{u}) (k : ℤ) :
    ∃ (E : ∀ M : RightModule A,
        characterDualMaps A M k ≃+ characterDualCycles ((underlying A).obj M) k)
      (F : ∀ M : RightModule A,
        CharacterDualHomotopyMaps A M k ≃+
          CharacterDualCohomology ((underlying A).obj M) k),
      (∀ (M : RightModule A) (f : characterDualMaps A M k)
          (m : ((underlying A).obj M).X (-k)),
        (E M f).val m = f.val (-k) m
          ((A.X.XIsoOfEq (show (0 : ℤ) = -(-k + k + 0) by omega)).hom
            (characterDualUnit A))) ∧
      (∀ (M : RightModule A) (f : characterDualMaps A M k),
        F M (QuotientAddGroup.mk' (characterDualNullMaps A M k) f) =
          QuotientAddGroup.mk' (characterDualBoundaries ((underlying A).obj M) k)
            (E M f)) ∧
      (∀ (M N : RightModule A) (u : N ⟶ M)
          (f : characterDualMaps A M k) (g : characterDualMaps A N k)
          (_hg : ∀ (p : ℤ) (n : ((underlying A).obj N).X p),
            g.val p n = f.val p ((((underlying A).map u).f p) n))
          (n : ((underlying A).obj N).X (-k)),
        (E N g).val n = (E M f).val ((((underlying A).map u).f (-k)) n)) := by
  sorry

end CategoryTheory.DgAlgebra
