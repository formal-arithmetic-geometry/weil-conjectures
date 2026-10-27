module

public import Sheaf.AlgebraicGeometry.GroupScheme.EquivariantRightTorsor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Lifting equivariant torsor isomorphisms along the contracting affine line

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Lemma 3.6, proof of (2) implies (1), printed p.6, with Section 2, Claim 3, p.3.
(blueprint: lem-sfb-contracting-line-equivariant-torsor-rigidity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Every specified equivariant isomorphism at zero extends to an equivariant
right H-torsor isomorphism on the weight-one affine line. There is no uniqueness
or triviality hypothesis on either fibre.
Source: Alper--Halpern-Leistner--Heinloth, Lemma 3.6, proof of (2) implies (1),
printed p.6, and Section 2, Claim 3, printed p.3
(blueprint: lem-sfb-contracting-line-equivariant-torsor-rigidity).

Proof:
1. The lemma lem-sfb-smooth-affine-torsor-isom-scheme represents Isom_H(P,Q)
by an affine scheme I smooth over L, compatibly with every base change.
The two left actions give the conjugation action z.alpha = z_Q alpha z_P^(-1).
2. By def-weil-affine-spectrum write L = Spec A, A = k[u], and I = Spec B.
The coaction gives the direct sum grading B = direct_sum B_d by coefficient
comparison in B[z,z^(-1)]. Multiplication adds degrees and u has degree one.
Equivariance is exactly preservation of degrees. The specified fibre isomorphism
gives a graded A-algebra map f_0 : B -> A/(u).
3. Inductively lift f_n to g : B -> A/(u^(n+2)), using smoothness
(def-sbc-smooth-morphisms). The kernel J of this reduction has square zero.
For homogeneous b in degree d retain only the degree-d part of g(b). The discarded
parts lie in J. In the degree-(d+e) component of g(b)g(c), each unwanted pair has
both factors in J and vanishes. Thus this operation gives a graded algebra lift
f_(n+1), fixes A, and preserves the prescribed f_n.
4. Each homogeneous part of A/(u^(n+1)) stabilizes to that of A: it is k.u^d
for d >= 0 and n >= d, and zero for d < 0. The compatible f_n therefore give
a graded map B -> A on each homogeneous part. Extend by finite sums; the ring
laws and the A-algebra condition follow by reduction, since intersection (u^n) = 0.
5. By def-weil-affine-spectrum this map is an equivariant section L -> I.
The representing property of lem-sfb-smooth-affine-torsor-isom-scheme gives the
required H-torsor isomorphism. Its conjugation equivariance is precisely left
equivariance, and its reduction is the prescribed fibre map. The displayed
conclusion expresses this restriction by the two canonical fibre inclusions. -/
theorem exists_equivariantRightTorsorIso_contractingLine
    (k : Type u) [Field k] (H : Grp (Over (Spec (.of k))))
    [Smooth H.X.hom] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (P Q : EquivariantRightTorsor (Grp.mk (StandardGroupSchemes.multiplicative k)) H
      (StandardGroupSchemes.additive k) (ContractingLine.scaling k))
    (α₀ : EquivariantRightTorsor.FibreIso P Q (ContractingLine.origin k)) :
    ∃ α : EquivariantRightTorsor.EquivariantIso P Q,
      pullback.fst P.torsor.projection (ContractingLine.origin k) ≫ α.iso.hom =
        α₀.iso.hom ≫ pullback.fst Q.torsor.projection (ContractingLine.origin k) := by
  sorry

end AlgebraicGeometry
