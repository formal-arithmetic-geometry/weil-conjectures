/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees
import Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.RingTheory.KoszulComplementaryEquivalences
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.TraceFormula.AlgebraicShriekCalculus
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor
import Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.RegularSequenceKoszulRegular
import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction

/-! # Polynomial reduction of diagonal derived Hom

Source: Stacks Project, more-algebra.tex, Tags 068X, 07VI, 0A65, 0A6A and 0DHS;
dualizing.tex, Tag 0BZW. The final reduction is the agent argument recorded in the DAG,
not a verbatim assertion of those tags
(blueprint: lem-trf-polynomial-diagonal-rhom-reduction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The diagonal Hom functor followed by restriction along the first coprojection.
The diagonal is the multiplication module, and extension is the shared K-flat extension.
Source: Stacks 0E2U and the polynomial reduction ring diagram
(blueprint: lem-trf-polynomial-diagonal-rhom-reduction). -/
noncomputable def polynomialDiagonalHom (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))] :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  relativeDualizingDerivedExtension
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom ⋙
    ihom (relativeDualizingModuleDiagonal R A) ⋙
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).mapDerivedCategory

/-- The polynomial dualizing object RHom_P(A,P)[n], with its precomposition A-action.
Coinduction is the already constructed total right derived ordinary coinduction.
Source: Stacks dualizing.tex, Tag 0BZW
(blueprint: lem-trf-polynomial-diagonal-rhom-reduction). -/
noncomputable def polynomialDiagonalDualizing (R A : Type u)
    [CommRing R] [CommRing A] (n : ℕ)
    [HasDerivedCategory.{u} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    (p : MvPolynomial (Fin n) R →+* A) : DerivedCategory (ModuleCat.{u} A) :=
  ((ModuleCat.derivedCoinduction p).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
      (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))⟦(n : ℤ)⟧

/-- Polynomial reduction, as an isomorphism family natural for all morphisms between
pseudo-coherent complexes of finite R-Tor amplitude. No diagonal dualizing hypothesis occurs.
Source: Stacks 068X, 07VI, 0A65, 0A6A, 0DHS and 0BZW, assembled by the DAG argument
(blueprint: lem-trf-polynomial-diagonal-rhom-reduction).

Proof:

1. If A=0, its module category has only the zero object and both sides are zero, naturally in T.
Otherwise distinguish the two copies A_1,A_2 of A. Put S=A_1\otimes_RP=A_1[x_1,\ldots,x_n], let
q:S\twoheadrightarrow B=A_1\otimes_RA_2 be induced by the presentation, and put e=\mu q:S\to A,
where \mu is multiplication. Write a_i for the image of x_i in A. Then e(x_i)=a_i and
e|_{A_1}=1_A. These identities specify every restriction used below: the output A-action will
always be obtained through A_1\to S or p_1:A_1\to B.

2. The rings P and S are Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian], applied
respectively to R and A_1 and their polynomial algebras. The presentation makes R\to A finite
type. By [lem-trf-flat-polynomial-quotient-perfect], A_2 has a bounded finite-projective
P-resolution L. Tensoring it over R with the flat module A_1 preserves its exact augmented
sequence by [lem-weil-pbc-flat-tensor-exact]. Thus S\otimes_PL resolves B. Each term is finite
projective over S: a finite-free retraction presenting a finite-projective term remains a
retraction after scalar extension. Hence B is perfect over S. The same exactness calculation,
using N\otimes_PS=N\otimes_RA_1, proves P\to S flat. Also B is flat over each A_i, since tensoring
an A_i-module with B over A_i is tensoring its underlying R-module with the other, flat, copy of
A.

3. Write D=C_{P\to A_2}(P)=R\operatorname{Hom}_P(A_2,P)\in D(A_2) and
E=C_q(S)=R\operatorname{Hom}_S(B,S)\in D(B), where C denotes derived coinduction with
precomposition action [lem-trf-derived-coinduction-adjunction]. Apply the flat-base-change
comparison (iii) of [lem-trf-algebraic-shriek-calculus] to the finite-type Noetherian map
P\twoheadrightarrow A_2, the flat Noetherian extension P\to S, and the bounded-below input P[0].
Clause (i) identifies both surjective-map shriek functors with coinduction, so this gives E\cong
B\otimes_{A_2}^{\mathbf L}D\quad\hbox{in }D(B). This uses the second coprojection for this one
base change; it does not replace the first coprojection on the output. By
[lem-trf-perfect-complex-derived-biduality], E is perfect as an S-complex and the canonical
S-linear bidual map B\to R\operatorname{Hom}_S(E,S) is invertible.

4. For V\in D(S) let J_E(V)\in D(B) have the meaning of [lem-trf-derived-bimodule-tensor-hom].
There is a natural B-linear comparison \alpha_V:B\otimes_S^{\mathbf L}V\longrightarrow J_E(V). Its
adjunct under that lemma is E\otimes_B^{\mathbf L}(B\otimes_S^{\mathbf L}V)\cong
E\otimes_S^{\mathbf L}V\to V, obtained from the coinduction counit E\to S of
[lem-trf-derived-coinduction-adjunction]. For this rebracketing take a K-flat S-model of V and a
K-flat B-model of E [lem-pc-kflat-resolution]; extension of the former to B is K-flat
[lem-pur-kflat-change-of-rings], so [lem-pc-derived-tensor-second-factor-functor] computes both
sides by the balanced rebracketing: (u\otimes b)\otimes v\mapsto u\otimes bv and its inverse
u\otimes v\mapsto(u\otimes1)\otimes v. Thus it uses no flatness of B over S. After restriction to
S, \alpha_V is the perfect evaluation map B\otimes_S^{\mathbf L}V\to R\operatorname{Hom}_S(E,V):
at V=S it is the canonical bidual map of Step 3; in general tensor that map with V and apply
finite-projective Hom evaluation. On a bounded finite-projective S-model P_E this evaluation is
the signed map \lambda\otimes v\mapsto(z\mapsto(-1)^{rs}\lambda(z)v) for dual degree r and
coefficient degree s, by [lem-pod-projective-hom-evaluation-model]. Its degree maps are the
normalized isomorphisms of [lem-pc-perfect-ring-hom-tensor-degrees];
[lem-pc-perfect-ring-hom-tensor-differential] makes them a chain isomorphism. Hence the actual
evaluation comparison is invertible, not merely isomorphic source and target. Consequently
\alpha_V is invertible in D(B), since restriction is conservative by
[lem-trf-derived-coinduction-adjunction].

5. Choose a K-flat representative F of T over A_1 with flat terms by [lem-pc-kflat-resolution],
and put V=S\otimes_{A_1}^{\mathbf L}T. By [lem-pur-kflat-change-of-rings], S\otimes_{A_1}F is
K-flat over S. The tensor computations of [lem-pc-derived-tensor-second-factor-functor] therefore
give B\otimes_S^{\mathbf L}V\cong B\otimes_{A_1}^{\mathbf L}T as B-objects: on these models the
map is b\otimes(s\otimes t)\mapsto bs\otimes t. These maps are the canonical derived comparisons,
so are natural independently of the resolution. For this V, Step 4 identifies precisely the
induced coefficient complex in the question with J_E(V).

6. The same K-flat computation gives A\otimes_B^{\mathbf L}E\cong D as S-objects through e.
Explicitly choose a K-flat flat-term A_2-representative G of D [lem-pc-kflat-resolution]. By Step
3, E is represented by B\otimes_{A_2}G, which is K-flat over B by [lem-pur-kflat-change-of-rings].
Thus [lem-pc-derived-tensor-second-factor-functor] computes its tensor with A by
A\otimes_B(B\otimes_{A_2}G)\xrightarrow{\sim}G,\qquad c\otimes(b\otimes g)\longmapsto c\mu(b)g.
For s=a\otimes p\in S, its action on the right is a\bar p, exactly e(s). In particular the
S-action is the graph action, not merely the action through P.

7. Apply [lem-trf-derived-bimodule-tensor-hom] with X=A[0]\in D(B), the E of Step 3 and the V of
Step 5. It makes no flatness or finite-Tor assumption on X or E over B. Steps 4--6 give, after
restriction along A_1\to S, a natural isomorphism
\operatorname{Res}_{p_1}R\operatorname{Hom}_B(A,T\otimes_{A_1}^{\mathbf
L}B)\cong\operatorname{Res}_{A_1\to S}R\operatorname{Hom}_S(D,V). This is the actual mixed-ring
adjunction, not the same-ring internal-Hom formula with a changed ring symbol.

8. The kernel of e:S\to A is generated by f_i=x_i-a_i. Successively evaluating x_1,\ldots,x_{i-1}
identifies S/(f_1,\ldots,f_{i-1}) with A[x_i,\ldots,x_n]. Multiplication by x_i-a_i is injective
there: a nonzero polynomial has a highest power of x_i with nonzero coefficient, and the monic
product has that same nonzero coefficient one degree higher. The final quotient is A. Hence
[lem-weil-pbc-regular-sequence-koszul-regular] shows that this sequence is Koszul-regular. The
augmented Koszul complex is therefore a bounded finite-free resolution of A over S, including the
empty sequence when n=0.

9. Let H=C_e(S)\in D(A). The bounded Koszul resolution from Step 8 computes its underlying
S-linear derived Hom by [lem-pod-projective-hom-evaluation-model]. By
[lem-sc-koszul-complementary-equivalences], the dual Koszul complex has cohomology only in degree
n, where it is S/(f_1,\ldots,f_n)=A, with the ordered top-wedge generator. Restricting to A_1\to S
preserves this computation. This restriction is exactly the underlying A-object H, because
e|_{A_1}=1_A: on the coinduction model \operatorname{Hom}_S(A,I), precomposing by a equals
postmultiplication by its lift a\otimes1\in S. Thus H^n(H)\cong A as A-modules and all other
cohomology vanishes. Apply [lem-sf-derived-concentrated-single] in D(A) to obtain H\cong A[-n].
This identifies the object with its A-action, not just an S-linear Ext group.

10. Since Step 8 also makes A perfect over S, [lem-trf-perfect-algebra-coinduction-tensor] applied
to e and V gives C_e(V)\cong V\otimes_S^{\mathbf L}H in D(A). Use Step 9 and the K-flat F from
Step 5: (S\otimes_{A_1}F)\otimes_SA\cong F, by (s\otimes t)\otimes c\mapsto e(s)ct. The tensor
models in [lem-pc-derived-tensor-second-factor-functor] therefore give C_e(V)\cong
T[-n]\quad\hbox{in }D(A), naturally in T. The A-action on this tensor is through the A-valued
factor H; the displayed map identifies it with the original action on T, because e|_{A_1} is the
identity.

11. Use [lem-trf-algebraic-shriek-derived-hom-adjunction] for e:S\to A, X=D\in D(A) with its given
precomposition A-action, and Y=V. It gives
R\operatorname{Hom}_S(D,V)\cong\operatorname{Res}_eR\operatorname{Hom}_A(D,C_e(V)) in D(S).
Restrict along A_1\to S; the composite with e is the identity. Steps 7 and 10 now identify the
required left side with R\operatorname{Hom}_A(D,T[-n])\cong
R\operatorname{Hom}_A(D[n],T)=R\operatorname{Hom}_A(C,T). The shift equality is the usual
Hom-complex shift formula (degree r maps from D[n] are degree r-n maps from D). The graph
orientation was fixed once by the ordered variables; every subsequent comparison is natural in T,
so their composite has the required naturality. The assumptions on T in the question are retained;
the argument in fact required no extra boundedness or Tor condition on it.
-/
theorem polynomial_diagonal_rhom_reduction
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    (hflat : RingHom.Flat (algebraMap R A)) [Algebra.FinitePresentation R A]
    (n : ℕ) (p : MvPolynomial (Fin n) R →ₐ[R] A) (hp : Function.Surjective p)
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))] :
    ∃ e : ∀ (T : DerivedCategory (ModuleCat.{u} A)),
        DerivedCategory.IsPseudoCoherent T →
        (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
          i < a ∨ b < i → IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
              (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj T) ⊗
                (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q))) →
        ((polynomialDiagonalHom R A).obj T ≅
          (ihom (polynomialDiagonalDualizing R A n p.toRingHom)).obj T),
      ∀ (T T' : DerivedCategory (ModuleCat.{u} A))
        (hT : DerivedCategory.IsPseudoCoherent T)
        (hT' : DerivedCategory.IsPseudoCoherent T')
        (hTor : (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
          i < a ∨ b < i → IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
              (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj T) ⊗
                (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q))))
        (hTor' : (∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
          i < a ∨ b < i → IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
              (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj T') ⊗
                (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Q)))) (f : T ⟶ T'),
        (polynomialDiagonalHom R A).map f ≫ (e T' hT' hTor').hom =
          (e T hT hTor).hom ≫
            (ihom (polynomialDiagonalDualizing R A n p.toRingHom)).map f := by
  sorry

end AlgebraicGeometry
