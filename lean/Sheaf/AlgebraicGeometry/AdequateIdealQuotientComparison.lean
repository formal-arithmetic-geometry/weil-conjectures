module

public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.CategoryTheory.GlobalBaseIdealSheafQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.RingTheory.PolynomialAdequacyNilBaseChange

/-! # Ideal-quotient comparison for an adequately affine stack

Source: Alper, Adequate moduli spaces, Lemma 5.2.1, printed p.507, with
Proposition 3.3.5 and Remark 3.3.2, printed pp.497--498
(blueprint: lem-sfb-adequate-ideal-quotient-comparison).

The base-ring action is structural pullback, and the comparison is the quotient lift
of the map on compatible global section families induced by sheafification's quotient unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w e

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k P : Type u} [Field k] [CommRing P] [Algebra k P]
    {Z : BasedCategory.{v, w} (Over (Spec (.of k)))}
    {hZ : IsFibredInGroupoids Z}
    (f : BasedFunctor Z
      (discreteModuli (yoneda.obj ((Spec (.of P)).asOver (Spec (.of k))))))
    (A : ModuliAlgebraSheaf Z hZ)

/-- The structural P-action on the algebra ring at a single site object, bundled as a
ring homomorphism. Its values pull base functions back along the specified scheme map
and then apply A's structure map. Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
def moduliBaseIdealScalarComponent (x : Z.obj) : P →+* A.right.obj.obj (op x) :=
  (A.hom.hom.app (op x)).hom.comp
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Scheme.Γ.map
        (eqToHom (congrArg (fun T : Over (Spec (.of k)) ↦ T.left) (f.w_obj x)).symm ≫
          (yoneda.preimage (f.obj x).hom).left).op).hom.comp
        (Scheme.ΓSpecIso (.of P)).inv.hom))

/-- Pullbacks of a base function give compatible algebra sections on all site objects.
Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison).
Proof: the based-functor identity identifies the scheme underlying x with the source
of its map to Spec P. Functoriality of scheme pullback and naturality of A's structure
map show compatibility for each arrow, including its specified structural triangle. -/
theorem moduliBaseIdealScalar_compatible (p : P) :
    (fun x : Z.objᵒᵖ ↦
      moduliBaseIdealScalarComponent f A x.unop p) ∈
        RingCat.sectionsSubring (A.right.obj ⋙ forget₂ CommRingCat RingCat) := by
  sorry

/-- The canonical structural map P → Γ(Z,A), with no isomorphism assumption.
Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
def moduliBaseIdealScalarMap : P →+* moduliGlobalSectionsRing A.right :=
  (RingHom.pi (fun x : Z.objᵒᵖ ↦ moduliBaseIdealScalarComponent f A x.unop)).codRestrict
    (RingCat.sectionsSubring (A.right.obj ⋙ forget₂ CommRingCat RingCat))
    (moduliBaseIdealScalar_compatible f A)

/-- G/IG, where G is the existing ring of compatible global algebra sections and IG is
Mathlib's image-generated ideal. Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
abbrev moduliBaseIdealGlobalQuotient (I : Ideal P) :=
  moduliGlobalSectionsRing A.right ⧸ I.map (moduliBaseIdealScalarMap f A)

/-- H = Γ(Z,A/IA), using sheafification of the generated ideal relations.
Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
abbrev moduliBaseIdealQuotientSections (I : Ideal P) :=
  moduliGlobalSectionsRing
    (globalBaseIdealSheafQuotient.{w, v, u + 1, u} A.right (moduliBaseIdealScalarMap f A) I)

/-- The canonical map v : G/IG → H, induced by the actual quotient projection.
Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
def moduliBaseIdealComparison (I : Ideal P) :
    moduliBaseIdealGlobalQuotient f A I →+* moduliBaseIdealQuotientSections f A I :=
  globalBaseIdealSheafComparison.{w, v, u + 1, u} A.right (moduliBaseIdealScalarMap f A) I

/-- H is an algebra over G/IG by the specified canonical comparison v.
Source: Alper, Lemma 5.2.1
(blueprint: lem-sfb-adequate-ideal-quotient-comparison). -/
instance moduliBaseIdealComparisonAlgebra (I : Ideal P) :
    Algebra (moduliBaseIdealGlobalQuotient f A I) (moduliBaseIdealQuotientSections f A I) :=
  (moduliBaseIdealComparison f A I).toAlgebra

/-- For every commutative G/IG-algebra E, the scalar extension of the canonical
ideal-quotient comparison has elementwise nilpotent kernel and lifts positive powers.
The stack is algebraic, the morphism is adequately affine, and A is arbitrary
quasi-coherent; no additional separation, finiteness or flatness assumption is made.
Adequate affineness existentially binds the represented target's algebraicity proof,
as in the landed affine-target base-change interface.

Source: Alper, Lemma 5.2.1, printed p.507; Proposition 3.3.5 and Remark 3.3.2,
printed pp.497--498 (blueprint: lem-sfb-adequate-ideal-quotient-comparison).

Proof:
1. By lem-sfb-stack-polynomial-rees-calculus form J=IA, its powers, A/J, and the Rees
algebra. By lem-sfb-smooth-cover-section-descent, a section b vanishes in H precisely
when its chart restrictions lie in J: the sections bT descend in the Rees algebra.
Thus K=Γ(J) is the kernel of G→H, IG lies in K, and ker(v)=K/IG.
2. Choose all elements of I as generators. Polynomial/Rees calculus gives the graded
surjection A[x_j]→Rees(J), sending x_j to a_j T. The
lem-sfb-affine-target-adequacy-criterion lifts a positive power of bT. Comparing the
degree-N coefficient gives b^N in IG, since each degree-N monomial has a factor a_j.
Consequently every element of ker(v) is nilpotent, with no uniform exponent required.
3. Apply the same criterion and polynomial calculus to A[t_1,...,t_n]→(A/J)[t_1,...,t_n].
Every polynomial in H has a positive power lifting from G, hence from G/IG, since the
coefficient map kills IG. This includes zero variables.
4. Apply lem-sfb-polynomial-adequacy-nil-base-change to v. Its hypotheses are precisely
the nilpotent kernel of step 2 and finite-polynomial power lifting of step 3. It gives
both conclusions for every E, using the canonical tensor inclusion e↦e⊗1. -/
theorem adequatelyAffine_idealQuotient_comparison
    (hAlgZ : IsAlgebraicModuliStack Z)
    (f : BasedFunctor Z
      (discreteModuli (yoneda.obj ((Spec (.of P)).asOver (Spec (.of k))))))
    (hf : ∃ hT : IsAlgebraicModuliStack
      (discreteModuli (yoneda.obj ((Spec (.of P)).asOver (Spec (.of k))))),
      IsAdequatelyAffineMorphism f hAlgZ hT)
    (A : ModuliAlgebraSheaf Z hAlgZ.1.1) (hA : IsQuasicoherentModuliAlgebra A)
    (I : Ideal P) (E : Type e) [CommRing E]
    [Algebra (moduliBaseIdealGlobalQuotient f A I) E] :
    (∀ a : E,
      (Algebra.TensorProduct.includeLeftRingHom : E →+*
        E ⊗[moduliBaseIdealGlobalQuotient f A I] moduliBaseIdealQuotientSections f A I) a = 0 →
      IsNilpotent a) ∧
    (∀ z : E ⊗[moduliBaseIdealGlobalQuotient f A I] moduliBaseIdealQuotientSections f A I,
      ∃ N : ℕ, 0 < N ∧ ∃ a : E,
        (Algebra.TensorProduct.includeLeftRingHom : E →+*
          E ⊗[moduliBaseIdealGlobalQuotient f A I] moduliBaseIdealQuotientSections f A I) a =
            z ^ N) := by
  sorry

end AlgebraicGeometry
