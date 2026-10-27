module

public import Mathlib.Algebra.SkewPolynomial.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Frobenius skew modules and primitive functions

Source: Milne, Algebraic Groups (2017), Section 14(e), equations (96)--(98),
Proposition 14.41 and Remark 14.42, printed pp.292--294.
(blueprint: def-sfb-frobenius-primitive-module-data)
-/

set_option autoImplicit false

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FrobeniusPrimitive

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Iteration of the actual Frobenius endomorphism, including over imperfect fields.
Source: Milne, Section 14(e), p.292
(blueprint: def-sfb-frobenius-primitive-module-data). -/
@[instance_reducible]
def coefficientAction : MulSemiringAction (Multiplicative ℕ) k :=
  MulSemiringAction.compHom k (powersHom (k →+* k) (frobenius k p))

/-- The finite-sum carrier of k_sigma[F], with the skew-polynomial ring structure below.
Source: Milne, Section 14(e), p.292
(blueprint: def-sfb-frobenius-primitive-module-data). -/
def SkewRing (_p : ℕ) : Type u := SkewPolynomial k

/-- Multiplication is (c F^i)(b F^j) = c b^(p^i) F^(i+j).
Source: Milne, Section 14(e), p.292
(blueprint: def-sfb-frobenius-primitive-module-data). -/
noncomputable instance skewRing : Ring (SkewRing k p) :=
  letI := coefficientAction k p
  inferInstanceAs (Ring (SkewPolynomial k))

/-- The action polynomial sum c_i x^(p^i) on a test algebra.
Source: Milne, Section 14(e), p.293
(blueprint: def-sfb-frobenius-primitive-module-data). -/
def actionValue {R : Type u} [CommRing R] [Algebra k R]
    (a : SkewRing k p) (x : R) : R :=
  SkewPolynomial.sum a (fun i c ↦ algebraMap k R c * x ^ (p ^ i))

/-- The displayed action determines a unique module structure on every test algebra.
Source: Milne, Section 14(e), p.293
(blueprint: def-sfb-frobenius-primitive-module-data).

Proof: Frobenius powers are additive in characteristic p; multiplication by coefficients
is additive. Thus each action polynomial is additive, and the action is additive in the
polynomial. The constant polynomial 1 acts identically. On monomials, composition gives
c (b x^(p^j))^(p^i) = c b^(p^i) x^(p^(i+j)), exactly skew multiplication.
Distribute finite sums to obtain the module axioms. The displayed formula fixes scalar
multiplication, and all remaining fields of Module are propositions, proving uniqueness. -/
theorem algebraModule_existsUnique (R : Type u) [CommRing R] [Algebra k R] :
    ∃! h : Module (SkewRing k p) R,
      ∀ (a : SkewRing k p) (x : R), @SMul.smul _ _ h.toSMul a x = actionValue k p a x := by
  sorry

/-- The canonical, uniquely specified Frobenius module on a test algebra.
Source: Milne, Section 14(e), p.293
(blueprint: def-sfb-frobenius-primitive-module-data). -/
noncomputable instance algebraModule (R : Type u) [CommRing R] [Algebra k R] :
    Module (SkewRing k p) R :=
  (algebraModule_existsUnique k p R).exists.choose

/-- The point represented by Spec R on a k-scheme.
Source: Milne, equation (98), p.294
(blueprint: def-sfb-frobenius-primitive-module-data). -/
abbrev Points (G : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R] :=
  StandardGroupSchemes.affine k R ⟶ G

/-- The coordinate value of a point of the existing additive group.
Source: Milne, equation (96), p.292
(blueprint: def-sfb-frobenius-primitive-module-data). -/
noncomputable def additiveValue (R : Type u) [CommRing R] [Algebra k R]
    (x : Points k (StandardGroupSchemes.additive k) R) : R :=
  (Spec.preimage x.left).hom Polynomial.X

/-- Commutativity of the specified additive group law, needed for its Hom group.
Source: Milne, equation (96), p.292
(blueprint: def-sfb-frobenius-primitive-module-data).

Proof: the flip of y tensor 1 + 1 tensor y is the same polynomial by commutativity
of addition. Algebra maps from k[y] agree when they agree on y, so the multiplication
map is invariant under swapping its factors. This is precisely IsCommMonObj. -/
theorem additive_commutative : IsCommMonObj (StandardGroupSchemes.additive k) := by
  sorry

attribute [instance] additive_commutative

/-- P(G) is the actual group-scheme Hom into Ga, with pointwise additive law.
Source: Milne, equation (96), p.292
(blueprint: def-sfb-frobenius-primitive-module-data). -/
abbrev PrimitiveFunctions (G : Grp (Over (Spec (.of k)))) :=
  Additive (G ⟶ Grp.mk (StandardGroupSchemes.additive k))

/-- Evaluation f_R(g), obtained by composing scheme morphisms and reading the coordinate.
Source: Milne, equations (96)--(98), pp.292--294
(blueprint: def-sfb-frobenius-primitive-module-data). -/
noncomputable def primitiveValue (G : Grp (Over (Spec (.of k))))
    (R : Type u) [CommRing R] [Algebra k R]
    (f : PrimitiveFunctions k G) (g : Points k G.X R) : R :=
  additiveValue k R (g ≫ f.toMul.hom.hom)

/-- Pointwise Frobenius and coefficients determine the primitive-function module uniquely.
Source: Milne, equations (96)--(97), pp.292--293
(blueprint: def-sfb-frobenius-primitive-module-data).

Proof: multiplication of Ga by c and its p-th-power map are group homomorphisms.
Postcomposition therefore preserves the group-scheme Hom. Their sums give the displayed
polynomial action. Evaluating on all test algebras gives the module identities by the
same monomial calculation as for algebraModule_existsUnique. Affine test schemes detect
maps to Ga, so the evaluation formula fixes each resulting homomorphism. Consequently
it fixes scalar multiplication, and proof irrelevance gives uniqueness of Module. -/
theorem primitiveModule_existsUnique (G : Grp (Over (Spec (.of k)))) :
    ∃! h : Module (SkewRing k p) (PrimitiveFunctions k G),
      ∀ (a : SkewRing k p) (f : PrimitiveFunctions k G)
        (R : Type u) [CommRing R] [Algebra k R] (g : Points k G.X R),
        primitiveValue k G R (@SMul.smul _ _ h.toSMul a f) g =
          actionValue k p a (primitiveValue k G R f g) := by
  sorry

/-- The module action is selected from its unique pointwise characterization.
Source: Milne, equations (96)--(97), pp.292--293
(blueprint: def-sfb-frobenius-primitive-module-data). -/
noncomputable instance primitiveModule (G : Grp (Over (Spec (.of k)))) :
    Module (SkewRing k p) (PrimitiveFunctions k G) :=
  (primitiveModule_existsUnique k p G).exists.choose

/-- A representing commutative group scheme for Hom_A(M,-), with its natural additive
bijections. The scheme is supplied as real data, rather than chosen from existence.
Source: Milne, Proposition 14.41, p.293
(blueprint: def-sfb-frobenius-primitive-module-data). -/
structure Representation (M : Type v) [AddCommGroup M] [Module (SkewRing k p) M] where
  group : Grp (Over (Spec (.of k)))
  [commutative : IsCommMonObj group.X]
  points : ∀ (R : Type u) [CommRing R] [Algebra k R],
    Additive (Points k group.X R) ≃+ (M →ₗ[SkewRing k p] R)
  naturality : ∀ (R S : Type u) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
    (φ : R →ₐ[k] S) (g : Points k group.X R) (m : M),
    points S (Additive.ofMul (StandardGroupSchemes.map k φ ≫ g)) m =
      φ (points R (Additive.ofMul g) m)

end AlgebraicGeometry.FrobeniusPrimitive
