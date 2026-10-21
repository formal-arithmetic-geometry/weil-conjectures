module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Curve.AdelicLocal
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

import WeilConjectures.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Scalar extension and semilocal principal parts on a smooth curve

Source: Stacks Project, Algebra Tags 00DT, 00JB and 034X; the explicit ten-step
semilocal consequence in the DAG node
(blueprint: lem-pc-curve-local-scalar-principal-parts).

The local rings are the existing `Scheme.localSubalgebra`, canonically identified with
stalks by `Scheme.stalkEquivLocalSubalgebra`. Tensors put the scalar field on the left,
using the canonical tensor commutor from the order in the node. Every existential map
below is specified on generators or on quotient representatives, fixing the canonical map.
The finite algebras are actual ideal quotients, without reduction.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits TopologicalSpace TensorProduct
namespace AlgebraicGeometry
namespace CurveLocalScalar

/-- The projection of the scalar extension to the original curve.
Source: Stacks, Schemes Tag 01I4
(blueprint: lem-pc-curve-local-scalar-principal-parts). -/
noncomputable abbrev projection (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] : C.baseChangeField k K ⟶ C :=
  pullback.fst _ _

/-- The actual set of points above a point of the original curve, with its subtype topology.
Source: Stacks, Schemes Tag 01I4
(blueprint: lem-pc-curve-local-scalar-principal-parts). -/
abbrev Points (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] (x : C) :=
  {y : C.baseChangeField k K // projection k K C y = x}

/-- Scalar extension and all semilocal principal-parts comparisons, including nonreduced fibres.
Source: Stacks Project, Algebra Tags 00DT, 00JB, 034X, with 00PD and 00CT;
Schemes Tags 01I4 and 01HV
(blueprint: lem-pc-curve-local-scalar-principal-parts).

Proof plan (the steps are those of the node):
1. $C$ is integral and of dimension one by the definition of a smooth projective curve.
Projectivity gives properness, and properness gives finite type. The field is Noetherian (its
only ideals are $0$ and $k$), so $C$ is Noetherian. Smoothness and properness persist over $K$;
the same argument gives finite type and Noetherianity of $C_K$. Both schemes are regular by
smoothness over a field. The relative-dimension-one base-change lemma, first with
$T=\operatorname{Spec}k$ and then with $T=\operatorname{Spec}K$, gives $\dim_z C=1$ and $\dim_z
C_K=1$ at every point, in the topological local-dimension sense. Geometric connectedness gives
connectedness of $C_K$; its nonemptiness is established in step 3 before invoking the integral
criterion. Uses: def-pc-smooth-projective-curve, lem-pc-projective-proper, pqf-lem-proper-basic,
lem-pc-proper-base-change, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-smooth-scheme-over-field-regular, lem-sc-curve-base-change-relative-dimension-one,
def-pc-geometrically-irreducible.
2. Choose an affine neighbourhood $U=\operatorname{Spec}R$ of $x$, and let $\mathfrak m$ be its
maximal ideal. The affine stalk identification gives $O=R_{\mathfrak m}$ and
$\kappa(x)=R/\mathfrak m$. The closed-point field lemma gives $d=[\kappa(x):k]<\infty$. The
closed-point dimension lemma and step 1 give $\dim O=1$; regularity then gives that $O$ is a
DVR. These arguments use a finite type affine chart, not an arbitrary local ring of a curve.
Uses: lem-weil-pbc-spec-domain-stalks-function-field, lem-kun-closed-point-field,
lem-weil-pbc-closed-point-dimension-local-ring, lem-sc-regular-dim1-dvr.
3. The affine fibre product identifies the fibre over $x$ with $\operatorname{Spec}T_1$, where
$T_1=(R/\mathfrak m)\otimes_kK=\kappa(x)\otimes_kK$: the quotient maps kill precisely the ideal
generated by $\mathfrak m$, by the universal property of tensor products and quotients. A
$k$-basis of $\kappa(x)$ becomes a $K$-basis of $T_1$, so $T_1$ has positive dimension $d$.
Apply the finite-algebra spectrum lemma with base $K$, a local ring whose only prime is $(0)$.
It gives finitely many primes, all maximal, with intersection the nilradical. Thus the
product-of-localizations lemma applies. Its product cannot be empty, since the empty product is
the zero ring and $T_1\ne0$. Therefore $S$ is finite and nonempty. Each point is closed in the
fibre, which is the inverse image of the closed subset $\{x\}$, hence closed in $C_K$. Its
residue field is finite over $K$ by the closed-point field lemma. In particular $C_K$ is
nonempty. Regularity and connectedness from step 1 now imply its integrality. Uses:
lem-weil-pbc-fibre-product-affine-spectra,
lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum,
lem-weil-pbc-product-of-localizations-at-maximal, lem-kun-closed-point-field,
lem-sc-regular-connected-integral.
4. Put $R_K=R\otimes_kK$. The affine chart $U_K$ is nonempty, and its ring $R_K$ is a domain
because $C_K$ is integral. The function-field lemma identifies $F=\operatorname{Frac}R$ and
$L=\operatorname{Frac}R_K$. The localization-tensor comparison identifies $A$ with
$(R\setminus\mathfrak m)^{-1}R_K$ and $V$ with $(R\setminus\{0\})^{-1}R_K$. No nonzero element
of $R$ becomes zero in $R_K$: extend the singleton consisting of that element to a $k$-basis and
tensor that basis with $K$. Hence both localizations inject into $L$, giving the canonical
inclusions $A\subset V\subset L$. A point $y\in S$ corresponds to a prime $\mathfrak q_y$ of
$R_K$ over $\mathfrak m$. Set $\mathfrak p_y=\mathfrak q_y A$. The affine stalk formula and
iterated fractions give $O_y=(R_K)_{\mathfrak q_y}=A_{\mathfrak p_y}$, compatibly inside $L$.
Since $y$ is closed, the closed-point dimension lemma and step 1 give $\dim O_y=1$, and its
regularity makes it a DVR. Localizing a domain does not change its fraction field, so the
fraction fields of $O$ and $O_y$ are $F$ and $L$. Uses:
lem-weil-pbc-fibre-product-affine-spectra, lem-sc-integral-function-field-affine-fraction,
lem-weil-pbc-localization-tensor-over-base, lem-weil-pbc-spec-domain-stalks-function-field,
lem-weil-pbc-closed-point-dimension-local-ring, lem-sc-regular-dim1-dvr.
5. Fix a uniformizer $t$ of $O$. For every $n\ge1$, the map $(O/t^nO)\otimes_kK\to A/t^nA$ sends
$\bar a\otimes c$ to the class of $a\otimes c$. It is an isomorphism: choose a $k$-vector-space
complement to $t^nO$ in $O$; tensoring this direct-sum decomposition identifies the kernel of
$O\otimes_kK\to(O/t^nO)\otimes_kK$ with $(t^nO)\otimes_kK$, whose image is exactly $t^nA$. This
also verifies the asserted canonical map, independently of the chosen complement. The filtration
by $t^iO/t^nO$, $0\le i\le n$, has successive quotients $\kappa(x)$: multiplication by $t^i$
induces $O/tO\simeq t^iO/t^{i+1}O$, since $O$ is a domain. Thus $O/t^nO$ has $k$-dimension $nd$
and $Q_n=A/t^nA$ has $K$-dimension $nd$. In particular $Q_n\ne0$. Uses:
def-sc-discrete-valuation-ring.
6. By step 5, $Q_n=A/t^nA$ is a finite $K$-algebra. Apply the finite-algebra spectrum lemma with
base $K$ to obtain a finite maximal spectrum and a locally nilpotent Jacobson radical. The
product-of-localizations lemma therefore gives its canonical product decomposition. Every prime
of $Q_n$ contains the image of $t$, since $t^n=0$ there, so its primes correspond exactly to
those of $A/tA=T_1$, hence to $S$. Concretely primes of a quotient are inverse images of primes
containing its kernel: both assignments preserve products and properness and are inverse. Each
factor $(Q_n)_{\mathfrak p_y/(t^n)}$ is canonically $A_{\mathfrak p_y}/t^nA_{\mathfrak
p_y}=O_y/t^nO_y$. To check this last equality, send $\bar a/\bar s$ to the class of $a/s$, and
send the class of $a/s$ back to $\bar a/\bar s$, for $s\notin\mathfrak p_y$. Fraction equality
and the relation $t^n=0$ show these maps are well-defined and inverse. Consequently the product
decomposition is precisely the canonical isomorphism $Q_n\simeq\prod_{y\in S}O_y/t^nO_y$. Uses:
lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum,
lem-weil-pbc-product-of-localizations-at-maximal, def-weil-pbc-localization-at-prime.
7. By its definition $A\subset B=\bigcap_y O_y$. The diagonal $B\to\prod_yO_y/t^nO_y$ has kernel
$\bigcap_y t^nO_y=t^nB$: dividing an element of the intersection by the common nonzero element
$t^n$ puts it in every $O_y$. It is surjective, since its restriction to $A$ is surjective by
step 6. Thus $B/t^nB$ maps isomorphically to that product. The composite from $A/t^nA$ is
exactly step 6, so $A/t^nA\to B/t^nB$ is an isomorphism as well. Together with step 5 this
proves every quotient isomorphism in the statement and their finite-dimensionality. All maps
preserve multiplication and the structural image of $K$. Uses: the preceding explicit
calculations.
8. The DVR valuation description gives $F=O[t^{-1}]$: a nonzero fraction is a unit times an
integral power of $t$. Tensoring the displayed fractions, or using the localization-tensor
comparison, gives $V=A[t^{-1}]$. For every $y\in S$, $t$ is nonzero and lies in the maximal
ideal of $O_y$ (its image vanishes in the fibre), so $v_y(t)>0$. For any $f\in L^*$ choose an
integer $n\ge0$ with $n v_y(t)+v_y(f)\ge0$ for every $y$; this is possible since $S$ is finite.
Then $t^nf\in B$, proving $L=B[t^{-1}]$. The same assertion for $f=0$ is immediate. Uses:
def-sc-discrete-valuation-ring, lem-weil-pbc-localization-tensor-over-base.
9. If $v\in V\cap B$, write $v=a/t^n$ with $a\in A$, $n\ge1$ (increase the denominator exponent
if necessary). Then $a\in A\cap t^nB$. The injectivity of $A/t^nA\to B/t^nB$ in step 7 says
$a\in t^nA$, so $v\in A$. Hence $V\cap B=A$, and inclusion induces an injection $V/A\to L/B$.
For surjectivity write $f=b/t^n$ with $b\in B$, $n\ge1$, using step 8. Choose $a\in A$ congruent
to $b$ modulo $t^nB$ by step 7. Then $f-a/t^n\in B$. The representative $a/t^n$ belongs to $V$,
proving surjectivity. Uses: the preceding explicit calculations.
10. The kernel of the diagonal map $L\to\bigoplus_{y\in S}L/O_y$ is $B$ by definition; the
direct sum is the finite product because $S$ is finite. For any tuple of classes choose
representatives $f_y\in L$. Choose a single $n\ge1$ with $t^nf_y\in O_y$ for all $y$, using the
positive valuations in step 8. Step 6 supplies $a\in A$ whose class in $O_y/t^nO_y$ is $t^nf_y$
for every $y$. Consequently $a/t^n-f_y\in O_y$ for every $y$, so $a/t^n\in L$ maps to the given
tuple. This proves the second canonical isomorphism. Both quotient maps are $K$-linear. Every
quotient above is the actual ideal quotient; no nilpotent is discarded at any step. Uses: the
preceding explicit calculations.
-/
theorem principal_parts
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))]
    [Algebra k C.functionField] [Scheme.IsFunctionFieldAlgebra k C]
    (x : C) (hx : IsClosed ({x} : Set C)) :
    IsIntegral C ∧ ∃ (_ : IsIntegral (C.baseChangeField k K)),
      ∀ [Algebra K (C.baseChangeField k K).functionField]
        [Scheme.IsFunctionFieldAlgebra K (C.baseChangeField k K)],
      IsDiscreteValuationRing (C.presheaf.stalk x) ∧
      IsDiscreteValuationRing (Scheme.localSubalgebra k C x) ∧
      FiniteDimensional k (IsLocalRing.ResidueField (Scheme.localSubalgebra k C x)) ∧
      Finite (Points k K C x) ∧ Nonempty (Points k K C x) ∧
      (∀ y : (Points k K C x), IsClosed ({y.1} : Set (C.baseChangeField k K)) ∧
        IsDiscreteValuationRing ((C.baseChangeField k K).presheaf.stalk y.1) ∧
        IsDiscreteValuationRing (Scheme.localSubalgebra K (C.baseChangeField k K) y.1) ∧
        FiniteDimensional K (IsLocalRing.ResidueField (Scheme.localSubalgebra K (C.baseChangeField k
          K) y.1))) ∧
      ∃ (rho : C.functionField →+* (C.baseChangeField k K).functionField)
        (i : K ⊗[k] C.functionField →ₐ[K] (C.baseChangeField k K).functionField)
        (j : K ⊗[k] (Scheme.localSubalgebra k C x) →ₐ[K] (C.baseChangeField k K).functionField)
        (r : ∀ y : (Points k K C x), (Scheme.localSubalgebra k C x) →+* (Scheme.localSubalgebra K
          (C.baseChangeField k K) y.1))
        (s : ∀ y : (Points k K C x), K ⊗[k] IsLocalRing.ResidueField (Scheme.localSubalgebra k C x)
          →+*
          IsLocalRing.ResidueField (Scheme.localSubalgebra K (C.baseChangeField k K) y.1))
        (eS : (Points k K C x) ≃ PrimeSpectrum (K ⊗[k] IsLocalRing.ResidueField
          (Scheme.localSubalgebra k C x)))
        (A V B : Subalgebra K (C.baseChangeField k K).functionField),
        Spec.map (CommRingCat.ofHom rho) ≫ C.fromSpecFunctionField =
          (C.baseChangeField k K).fromSpecFunctionField ≫ projection k K C ∧
        (∀ (c : K) (f : C.functionField), i (c ⊗ₜ[k] f) = c • rho f) ∧
        Function.Injective i ∧
        (∀ (c : K) (a : (Scheme.localSubalgebra k C x)), j (c ⊗ₜ[k] a) = i (c ⊗ₜ[k] (a :
          C.functionField))) ∧
        (∀ (y : (Points k K C x)) (a : (Scheme.localSubalgebra k C x)), (r y a : (C.baseChangeField
          k K).functionField) = rho (a : C.functionField)) ∧
        (∀ (y : (Points k K C x)) (c : K) (a : (Scheme.localSubalgebra k C x)),
          s y (c ⊗ₜ[k] IsLocalRing.residue (Scheme.localSubalgebra k C x) a) =
            algebraMap K (IsLocalRing.ResidueField (Scheme.localSubalgebra K (C.baseChangeField k K)
              y.1)) c *
              IsLocalRing.residue (Scheme.localSubalgebra K (C.baseChangeField k K) y.1) (r y a)) ∧
        (∀ y : (Points k K C x), (eS y).asIdeal = RingHom.ker (s y)) ∧
        A = j.range ∧ V = i.range ∧
        B = ⨅ y : (Points k K C x), Scheme.localSubalgebra K (C.baseChangeField k K) y.1 ∧
        A ≤ V ∧ A ≤ B ∧ V ⊓ B = A ∧
        ∃ (jA : K ⊗[k] (Scheme.localSubalgebra k C x) ≃ₐ[K] A)
          (ab : A →ₐ[K] B)
          (bo : ∀ y : (Points k K C x), B →ₐ[K] (Scheme.localSubalgebra K (C.baseChangeField k K)
            y.1))
          (eVA : (V ⧸ A.toSubmodule.comap V.val.toLinearMap) ≃ₗ[K]
            ((C.baseChangeField k K).functionField ⧸ B.toSubmodule))
          (eLB : ((C.baseChangeField k K).functionField ⧸ B.toSubmodule) ≃ₗ[K]
            (Π₀ y : (Points k K C x), (C.baseChangeField k K).functionField ⧸
              (Scheme.localSubalgebra K (C.baseChangeField k K) y.1).toSubmodule)),
          (∀ z : K ⊗[k] (Scheme.localSubalgebra k C x), (jA z : (C.baseChangeField k
            K).functionField) = j z) ∧
          (∀ a : A, (ab a : (C.baseChangeField k K).functionField) = (a : (C.baseChangeField k
            K).functionField)) ∧
          (∀ (y : (Points k K C x)) (b : B), (bo y b : (C.baseChangeField k K).functionField) = (b :
            (C.baseChangeField k K).functionField)) ∧
          (∀ v : V, eVA (Submodule.Quotient.mk v) =
            Submodule.Quotient.mk (v : (C.baseChangeField k K).functionField)) ∧
          (∀ (f : (C.baseChangeField k K).functionField) (y : (Points k K C x)),
            eLB (Submodule.Quotient.mk f) y = Submodule.Quotient.mk f) ∧
          ∀ t : (Scheme.localSubalgebra k C x), IsLocalRing.maximalIdeal (Scheme.localSubalgebra k C
            x) = Ideal.span {t} →
            (∀ v : V, ∃ (a : A) (m : ℕ),
              (v : (C.baseChangeField k K).functionField) * j (1 ⊗ₜ[k] t) ^ m = (a :
                (C.baseChangeField k K).functionField)) ∧
            (∀ f : (C.baseChangeField k K).functionField, ∃ (b : B) (m : ℕ),
              f * j (1 ⊗ₜ[k] t) ^ m = (b : (C.baseChangeField k K).functionField)) ∧
            ∀ n : ℕ, 1 ≤ n →
              ∃ (tA : A) (tB : B) (ty : ∀ y : (Points k K C x), (Scheme.localSubalgebra K
                (C.baseChangeField k K) y.1))
                (e0 : K ⊗[k] ((Scheme.localSubalgebra k C x) ⧸ Ideal.span {t ^ n}) ≃ₐ[K]
                  (A ⧸ Ideal.span {tA ^ n}))
                (e1 : (A ⧸ Ideal.span {tA ^ n}) ≃ₐ[K]
                  (B ⧸ Ideal.span {tB ^ n}))
                (e2 : (B ⧸ Ideal.span {tB ^ n}) ≃ₐ[K]
                  (∀ y : (Points k K C x), (Scheme.localSubalgebra K (C.baseChangeField k K) y.1) ⧸
                    Ideal.span {ty y ^ n})),
                tA = jA (1 ⊗ₜ[k] t) ∧ tB = ab tA ∧
                (∀ y : (Points k K C x), ty y = bo y tB) ∧
                (∀ (c : K) (a : (Scheme.localSubalgebra k C x)),
                  e0 (c ⊗ₜ[k] Ideal.Quotient.mk (Ideal.span {t ^ n}) a) =
                    Ideal.Quotient.mk (Ideal.span {tA ^ n}) (jA (c ⊗ₜ[k] a))) ∧
                (∀ a : A, e1 (Ideal.Quotient.mk (Ideal.span {tA ^ n}) a) =
                  Ideal.Quotient.mk (Ideal.span {tB ^ n}) (ab a)) ∧
                (∀ (b : B) (y : (Points k K C x)),
                  e2 (Ideal.Quotient.mk (Ideal.span {tB ^ n}) b) y =
                    Ideal.Quotient.mk (Ideal.span {ty y ^ n}) (bo y b)) ∧
                FiniteDimensional K (K ⊗[k] ((Scheme.localSubalgebra k C x) ⧸ Ideal.span {t ^ n})) ∧
                FiniteDimensional K (A ⧸ Ideal.span {tA ^ n}) ∧
                FiniteDimensional K (B ⧸ Ideal.span {tB ^ n}) ∧
                FiniteDimensional K (∀ y : (Points k K C x), (Scheme.localSubalgebra K
                  (C.baseChangeField k K) y.1) ⧸ Ideal.span {ty y ^ n}) := by
  sorry

end CurveLocalScalar
end AlgebraicGeometry
