module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-!
# A free quotient restricted to a regular hyperplane

Source: Stacks Project, Varieties, Tags 08AG, 08A0, 089Z and 0EGK
(blueprint: lem-sfb-hyperplane-free-quotient-euler-difference).

The short complex on the hyperplane is the image of the given complex under the
recorded tensor pullback. Its middle object is identified with the free module on H.
Twists on H are the pulled-back ambient twists, identified with its standard twists
by the given projective-space identification.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

/-- Restriction of a coherent free quotient to a hyperplane regular on the quotient
is short exact, and its Euler characteristic is the first difference of the ambient one.
The pair `d, 1 + d` in the injectivity assumption runs over all pairs `D - 1, D`.
The base structures on H and the compatibility of i and e express that the fixed
identification is over k. The short-exact conclusion uses the actual pullback maps;
identifying its middle object with the displayed free module gives the asserted row.

Source: Stacks Project, Varieties, Tag 08AG, first paragraph and exact diagram;
Tags 08A0, 089Z and 0EGK
(blueprint: lem-sfb-hyperplane-free-quotient-euler-difference).

Proof:
1. Standard affine charts of X and H are polynomial rings over the field, hence
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian. By
   pqf-lem-coherent-ft-locnoeth, K and F are quasi-coherent of finite type. Pullback
   preserves these properties by lem-weil-pbc-module-pullback-quasi-coherent and
   lem-weil-pbc-module-pullback-finite-type, so their pullbacks are coherent on H.
2. On a chart trivializing O(1), write s = a e. By lem-pc-zero-scheme-properties
   its ideal is (a). The normalized restriction maps are reduction modulo a by
   lem-weil-pbc-closed-immersion-unit-quotient. On the free middle term the tensor
   identification is componentwise b tensor c mapping to bc, inverse c to 1 tensor c.
3. By lem-weil-pbc-module-stalk-exact the original stalk row is exact. If A is its
   kernel in B and multiplication by a is injective on C, then A intersect aB = aA:
   ab in A implies a p(b) = 0, hence p(b) = 0. If p(b) = ac, lift c to b' and
   b - ab' lies in A. Thus 0 to A/aA to B/aB to C/aC to 0 is exact. These are
   the stalks of the canonical restricted maps, proving short exactness on H.
4. Twisting is locally tensoring with a free rank-one module, so preserves coherence
   and exactness for every integer degree. The quotient formula and
   lem-pc-closed-immersion-coherent-cohomology give the sequence
   0 to F(d-1) to F(d) to i_*(i^*F tensor i^*O(d)) to 0.
5. Projective spaces are proper by lem-per-finite-type-graded-proj-proper. The
   closed-immersion cohomology comparison of lem-pc-closed-immersion-coherent-cohomology
   identifies the last term's cohomology with that on H. Apply lem-pc-euler-additive
   and def-pc-euler-characteristic to obtain the asserted integer difference.
6. Substitute the polynomial identities in degrees d and d-1 into that difference.
   This gives the last assertion in rational coefficients for every integer d. -/
theorem hyperplane_free_quotient_euler_difference (k : Type u) [Field k]
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (K F : (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).Modules)
    (hK : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace K)
    (hF : RingedSpace.IsCoherent
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).toRingedSpace F)
    (a : K ⟶ SheafOfModules.free
      (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).ringCatSheaf) (ULift.{u} (Fin r)))
    (b : SheafOfModules.free
      (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).ringCatSheaf) (ULift.{u} (Fin r)) ⟶ F)
    (w : a ≫ b = 0) (hS : (ShortComplex.mk a b w).ShortExact)
    (s : Γ(twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1, ⊤)) (hs : s ≠ 0)
    (hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n F d s))
    (H : Scheme.{u}) [H.Over (Spec (.of k))]
    (i : H ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)))
    [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hH : i.ker = Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection _ s))
    (e : H ≅ ℙ(ULift.{u} (Fin ((n - 1) + 1)); Spec (.of k)))
    [e.hom.IsOver (Spec (.of k))]
    (htwist : ∀ d : ℤ, Nonempty
      ((Scheme.Modules.tensorPullback i).obj
          (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) ≅
        (Scheme.Modules.tensorPullback e.hom).obj
          (twist (ULift.{u} (Fin ((n - 1) + 1))) (Spec (.of k)) d))) :
    RingedSpace.IsCoherent H.toRingedSpace ((Scheme.Modules.tensorPullback i).obj K) ∧
    RingedSpace.IsCoherent H.toRingedSpace ((Scheme.Modules.tensorPullback i).obj F) ∧
    (∃ wH : (Scheme.Modules.tensorPullback i).map a ≫
        (Scheme.Modules.tensorPullback i).map b = 0,
      (ShortComplex.mk ((Scheme.Modules.tensorPullback i).map a)
        ((Scheme.Modules.tensorPullback i).map b) wH).ShortExact) ∧
    Nonempty ((Scheme.Modules.tensorPullback i).obj (SheafOfModules.free
        (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).ringCatSheaf)
        (ULift.{u} (Fin r))) ≅
      SheafOfModules.free (R := H.ringCatSheaf) (ULift.{u} (Fin r))) ∧
    (∀ d : ℤ,
      Scheme.Modules.eulerChar k
          ((Scheme.Modules.tensorPullback i).obj F ⊗
            (Scheme.Modules.tensorPullback i).obj
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) =
        Scheme.Modules.eulerChar k
            (F ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) -
          Scheme.Modules.eulerChar k
            (F ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (d - 1))) ∧
    (∀ P : Polynomial ℚ,
      (∀ d : ℤ, (Scheme.Modules.eulerChar k
        (F ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) : ℚ) = P.eval (d : ℚ)) →
      ∀ d : ℤ, (Scheme.Modules.eulerChar k
        ((Scheme.Modules.tensorPullback i).obj F ⊗
          (Scheme.Modules.tensorPullback i).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) : ℚ) =
        P.eval (d : ℚ) - P.eval ((d : ℚ) - 1)) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
