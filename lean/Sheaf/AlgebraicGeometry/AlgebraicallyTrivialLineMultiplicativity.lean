module

public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison
import Sheaf.AlgebraicGeometry.GeneralTheoremOfCube
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Multiplicativity of fibrewise algebraically trivial rigidified lines

Source: Milne, Abelian Varieties, I Proposition 8.4(c), printed p.36 (field case).
The relative algebraic-space assertion for arbitrary parameters is the agent-stated
prerequisite in the DAG, using Stacks Tags 0BF4, 0D28, 0E0S, 0AEJ and 05Z1
(blueprint: lem-sfb-algebraically-trivial-line-multiplicativity).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace.Poincare

/-- Addition on the actual base-changed group space: add the two original coordinates
and retain the common parameter. The pairing is into the existing sheaf fibre product.
Source: Milne I Proposition 8.4(c), base-change construction of its addition map
(blueprint: lem-sfb-algebraically-trivial-line-multiplicativity). -/
def parameterAddition {S : Scheme.{u}} (A : AlgebraicSpace S)
    (g : CommutativeSpaceGroup A) {T : AlgebraicSpace S} (b : T ⟶ groupSpaceBase S) :
    product ((pointedGroup A g).baseChange b).p ((pointedGroup A g).baseChange b).p ⟶
      ((pointedGroup A g).baseChange b).X :=
  pair (baseChangeProductMap (pointedGroup A g) (pointedGroup A g) b ≫ addition A g)
    (fst ((pointedGroup A g).baseChange b).p ((pointedGroup A g).baseChange b).p ≫
      ((pointedGroup A g).baseChange b).p)
    (baseMap_eq _ _)

/-- Every identity-rigidified fibrewise algebraically trivial line is multiplicative,
including over nonreduced and non-Noetherian parameter schemes. This asserts no lifting
of the line to a thickening and no choice of an associative multiplicative structure.
Source: Milne I Proposition 8.4(c), printed p.36, for the field criterion; the relative
prerequisite and proof are agent-stated in the DAG
(blueprint: lem-sfb-algebraically-trivial-line-multiplicativity).

Proof:
1. Smoothness gives flatness (lem-pc-smooth-flat). Proper smooth connected group fibres
   are geometrically integral (lem-sc-abelian-variety-characterization), also after
   residue-field extensions by faithfully flat descent. Apply
   lem-sfb-rigidified-space-picard: the full rigidified Picard space P is separated and
   locally finitely presented, and structure functions come universally from the base.
2. Use lem-trf-scheme-etale-invertible-comparison on geometric scheme fibres. On frames,
   tensor, dual and arbitrary pullback have transition units gh, g⁻¹ and pulled-back g,
   so the comparisons respect all operations needed here.
3. For a family L on C over U form N(L) = m*L ⊗ p₁*L⁻¹ ⊗ p₂*L⁻¹ ⊗ q*e*L.
   Evaluation gives compatible trivializations on both identity axes. This construction
   commutes with base change, respects isomorphisms, and sends the trivial line to itself.
4. Over each algebraically closed geometric field apply lem-sc-general-theorem-of-cube
   to N(F) for each smooth connected parameter family F generating algebraic equivalence.
   Triviality at one endpoint implies triviality at the other, in both directions.
   The finite equivalence chain from the trivial line therefore makes N(M) trivial on
   the whole geometric product fibre.
5. By lem-sfb-rigidified-space-picard, N(M), viewed as a rigidified family on the first
   factor, gives h:C → P_T. The other axis gives he = 0. Its geometric fibres are zero
   maps: normalize each fibre trivialization by its restriction to the first axis.
6. By lem-sfb-space-flat-proper-fp-locality, C → T is proper. The target P_T is separated
   and locally of finite type (lem-sfb-stack-chartwise-smooth-etale-calculus). Apply
   lem-sfb-proper-space-finite-image-neighbourhood to h: near each t there is an affine
   open V and a factorization C_V → Z → P_V with Z finite affine over V.
7. Write a:C_V → Z, s=e_V, p:C_V → V. Universal functions identify p♯ with an
   isomorphism whose inverse is s♯. Thus a♯ = (asp)♯. The bijection
   lem-sfb-space-affine-target-global-functions gives a=asp, so h_V=(h_Vs)p=0.
   This uses the full structure rings, including nilpotents.
8. Sheaf uniqueness for def-trf-algebraic-space glues h_V=0. The rigidified Picard
   classification makes N(M) trivial. The given rigidification trivializes q*e*M;
   tensoring with p₁*M ⊗ p₂*M and cancelling dual pairs yields the asserted iso.
-/
theorem algebraicallyTrivialLine_multiplicativity
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (_hA : IsAbelianFamily (groupSpaceProjection A))
    (T : Over S) (b : schemeSpace T ⟶ groupSpaceBase S)
    (M : ((pointedGroup A g).baseChange b).X.SmallModules)
    (_hM : IsLine ((pointedGroup A g).baseChange b).X M)
    (_htriv : FibrewiseTrivial ((pointedGroup A g).baseChange b).p M)
    (_r : (smallModuleTensorPullback ((pointedGroup A g).baseChange b).e).obj M ≅
      𝟙_ (schemeSpace T).SmallModules) :
    Nonempty ((smallModuleTensorPullback (parameterAddition A g b)).obj M ≅
      (smallModuleTensorPullback
        (fst ((pointedGroup A g).baseChange b).p
          ((pointedGroup A g).baseChange b).p)).obj M ⊗
      (smallModuleTensorPullback
        (snd ((pointedGroup A g).baseChange b).p
          ((pointedGroup A g).baseChange b).p)).obj M) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.Poincare
