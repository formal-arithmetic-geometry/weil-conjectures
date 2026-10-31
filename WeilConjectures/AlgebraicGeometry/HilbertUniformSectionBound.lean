/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama

/-!
# Uniform generation and sections of projective ideals

Source: Stacks Project, varieties.tex, Tags 08AG and 08A6--08A8; perfect.tex,
Tags 0B9S and 0B91; Grothendieck, Expose 221, Theorem 2.1 and Lemma 3.3.
(blueprint: lem-sfb-hilbert-uniform-section-bound)

The standard base-change realization of projective space is used. Its twists are
pullbacks of the recorded Proj twists. The middle term is p_*O(d), identified with the
homogeneous polynomial module by the standard monomial map for d nonnegative.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.HilbertSectionBound

noncomputable section

/-- The ambient twist. Source: Stacks, Tag 01MN.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def twist (T : Scheme.{u}) (n : ℕ) (d : ℤ) :
    (ℙ(ULift.{u} (Fin (n + 1)); T)).Modules :=
  ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) T d

/-- The structure morphism of the standard projective space. Source: Stacks, Tag 01NE.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def projection (T : Scheme.{u}) (n : ℕ) : ℙ(ULift.{u} (Fin (n + 1)); T) ⟶ T :=
  ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T

/-- The twisted actual ideal of a closed immersion. Source: Stacks, Tags 01I8 and 08AG.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def idealTwist {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) :
    (ℙ(ULift.{u} (Fin (n + 1)); T)).Modules :=
  i.ker.toModules ⊗ twist T n d

/-- The restriction of the twist to the closed subscheme. Source: Stacks, Tag 01MN.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def closedTwist {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) : Z.Modules :=
  (Scheme.Modules.tensorPullback i).obj (twist T n d)

/-- Sections of the ambient twist, the homogeneous polynomial module in nonnegative degree.
Source: Stacks, Tag 01XT. (blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def polynomialSections (T : Scheme.{u}) (n : ℕ) (d : ℤ) : T.Modules :=
  (Scheme.Modules.pushforward (projection T n)).obj (twist T n d)

/-- The literal degree-d homogeneous polynomial module, free on the degree-d monomials.
Source: Stacks, Tag 01XT. (blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def polynomialModule (T : Scheme.{u}) (n d : ℕ) : T.Modules :=
  SheafOfModules.free (R := T.ringCatSheaf) (RelativeProjectiveSpace.monomials.{u} n d)

/-- The integral degree-d monomial; projection to degree d makes its typing explicit.
The projection fixes this monomial since its exponent sum is d.
Source: Stacks, Tag 01XT. (blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def integralMonomial (n d : ℕ) (a : RelativeProjectiveSpace.monomials.{u} n d) :
    MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) (ULift.{u} ℤ) d :=
  ⟨MvPolynomial.homogeneousComponent d
      (∏ j : ULift.{u} (Fin (n + 1)), MvPolynomial.X j ^ a.down.val j.down),
    MvPolynomial.homogeneousComponent_mem _ _⟩

/-- The actual global monomial section of O(d), pulled back from integral Proj.
Source: Stacks, Tags 01MN and 01XT. (blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def monomialSection (T : Scheme.{u}) (n d : ℕ)
    (a : RelativeProjectiveSpace.monomials.{u} n d) : Γ(twist T n d, ⊤) :=
  letI := MvPolynomial.gradedAlgebra
    (σ := ULift.{u} (Fin (n + 1))) (R := ULift.{u} ℤ)
  Scheme.Modules.pullbackSection (ProjectiveSpace.toProjInt
    (ULift.{u} (Fin (n + 1))) T)
      ((Proj.unitToTwist (integralMonomial n d a).property ≫
        eqToHom (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule
          (ULift.{u} (Fin (n + 1))) (ULift.{u} ℤ))) (zero_add (d : ℤ)))).app ⊤
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule
          (ULift.{u} (Fin (n + 1))) (ULift.{u} ℤ)), ⊤)))

/-- The canonical polynomial-to-section map, sending each monomial basis element to
that actual global section. Source: Stacks, Tag 01XT.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def polynomialMap (T : Scheme.{u}) (n d : ℕ) :
    polynomialModule T n d ⟶ polynomialSections T n d :=
  Sigma.desc fun a ↦ Scheme.Modules.homOfGlobalSection (polynomialSections T n d)
    (monomialSection T n d a)

/-- Sections of the ideal twist. Source: Stacks, Tag 08AG and Expose 221, Theorem 2.1.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def idealSections {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) : T.Modules :=
  (Scheme.Modules.pushforward (projection T n)).obj (idealTwist i d)

/-- Sections on the closed family. Source: Expose 221, Theorem 2.1.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def closedSections {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) : T.Modules :=
  (Scheme.Modules.pushforward (i ≫ projection T n)).obj (closedTwist i d)

/-- The inclusion of the twisted ideal. Source: Stacks, Tag 01I8.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def idealInclusion {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) :
    idealTwist i d ⟶ twist T n d :=
  i.ker.toModulesι ▷ twist T n d ≫ (λ_ (twist T n d)).hom

/-- The left arrow of the canonical section sequence. Source: Expose 221, Theorem 2.1.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def sectionInclusion {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) :
    idealSections i d ⟶ polynomialSections T n d :=
  (Scheme.Modules.pushforward (projection T n)).map (idealInclusion i d)

/-- Restriction of polynomial sections, using the section-normalized unit and composition.
Source: Expose 221, Theorem 2.1. (blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def sectionRestriction {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (d : ℤ) :
    polynomialSections T n d ⟶ closedSections i d :=
  (Scheme.Modules.pushforward (projection T n)).map
      ((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app (twist T n d)) ≫
    (Scheme.Modules.pushforwardComp i (projection T n)).hom.app (closedTwist i d)

/-- Multiplication of an ideal twist by an ambient twist. Source: Stacks, Tag 08A7.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def idealTwistMultiplication {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (a b : ℤ) :
    idealTwist i a ⊗ twist T n b ⟶ idealTwist i (a + b) :=
  (α_ i.ker.toModules (twist T n a) (twist T n b)).hom ≫
    i.ker.toModules ◁ (ProjectiveSpace.twistTensorIso
      (ULift.{u} (Fin (n + 1))) T a b).hom

/-- Evaluation in degree m, untwisted by O(-m). Source: Stacks, Tag 08A8.
(blueprint: lem-sfb-hilbert-uniform-section-bound) -/
def evaluation {T Z : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)) (m : ℤ) :
    (Scheme.Modules.tensorPullback (projection T n)).obj (idealSections i m) ⊗
      twist T n (-m) ⟶ i.ker.toModules :=
  (Scheme.Modules.tensorPullbackSectionAdjunction (projection T n)).counit.app
      (idealTwist i m) ▷ twist T n (-m) ≫
    idealTwistMultiplication i m (-m) ≫
    eqToHom (congrArg (idealTwist i) (add_neg_cancel m)) ≫
    i.ker.toModules ◁ (ProjectiveSpace.unitIsoTwistZero
      (ULift.{u} (Fin (n + 1))) T).inv ≫ (ρ_ i.ker.toModules).hom

/-- Uniform ideal-section bounds with the canonical exact sequence, arbitrary base change,
evaluation and multiplication. Source: Stacks, Tags 08AG, 08A6--08A8, 0B9S, 0B91;
Expose 221, Theorem 2.1 and Lemma 3.3.
(blueprint: lem-sfb-hilbert-uniform-section-bound)

Proof (the eight DAG steps):
1. Put $q=pi$. The conclusion is automatic when $T$ is empty, so suppose $T$ is nonempty.
Projective space is proper over its base; since a closed immersion is proper, $q$ is proper. The
standard projective charts are polynomial algebras on $n$ variables over the base, so $p$ is
finitely presented. Apply the flat-closed-family ideal lemma to $i$: $\mathcal I$ is of finite
type and quasi-coherent, and its ordinary pullback along every base change on $T$ is the
corresponding ideal. Tensoring its exact sequence with the invertible twist preserves exactness.
On the chart $D_+(x_j)$ a twist is trivialized by $x_j^d$, so these exact sequences and the
twist identifications commute with further base change.
Dependencies: lem-sfb-flat-closed-family-ideal-base-change,
lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-fp-permanence.
2. Fix a geometric fibre with field $k$. The ambient projective space and its closed subscheme
are Noetherian: they are finite type over the Noetherian scheme $\operatorname{Spec}k$. Thus the
structure sheaves, being finite-type quasi-coherent, are coherent; closed-immersion coherent
cohomology makes $i_*\mathcal O_Z$ coherent on the fibre, and coherent kernels make its ideal
coherent. Hilbert-polynomial locality identifies the specified homogeneous-coordinate polynomial
with $d\mapsto\chi(Z_k,\mathcal O_{Z_k}(d))$ for every integer $d$. Closed-immersion coherent
cohomology, including its invertible projection formula, identifies this with $\chi(\mathbf
P^n_k,(i_*\mathcal O_{Z_k})(d))$. Apply the free-quotient regularity bound with $r=1$ to get a
single integer $a=a(n,1,P)$ for all geometric fibres. Set $m=\max(1,a)$. Propagation of
regularity makes every geometric-fibre ideal $m$-regular.
Dependencies: lem-sfb-free-quotient-kernel-regularity-bound,
lem-sfb-m-regular-coherent-sheaf-consequences,
lem-sfb-flat-projective-hilbert-polynomial-locality,
lem-pc-closed-immersion-coherent-cohomology, lem-weil-pbc-finite-type-over-noetherian,
pqf-lem-coherent-ft-locnoeth, lem-weil-pbc-coherent-kernel-cokernel-locnoeth.
3. For $d\geq m$, the regularity consequences give $H^j(\mathbf P^n_k,\mathcal I_k(d))=0$ for
every $j>0$. The projective-twist calculation gives $H^j(\mathbf P^n_k,\mathcal O(d))=0$ for
$j>0$ and $H^0(\mathcal O(d))=k[x_0,\ldots,x_n]_d$. Apply the cohomology long exact sequence to
the twisted ideal sequence and use closed-immersion coherent cohomology. It gives a surjection
$k[x_0,\ldots,x_n]_d\to H^0(Z_k,\mathcal O_{Z_k}(d))$ and vanishing $H^j(Z_k,\mathcal
O_{Z_k}(d))=0$ for $j>0$. The Euler polynomial equality therefore gives $\dim_k H^0(Z_k,\mathcal
O_{Z_k}(d))=P(d)$. For $n=0$, the separate $\mathbf P^0$ clause in the twist calculation and the
regularity theorem apply without overlapping degree-zero/top-degree formulas.
Dependencies: lem-sfb-m-regular-coherent-sheaf-consequences,
lem-pc-projective-space-twist-cohomology, lem-pc-closed-immersion-coherent-cohomology,
lem-sfb-flat-projective-hilbert-polynomial-locality, lem-weil-pbc-derived-functor-long-exact.
4. Fix $d\geq m$. The sheaf $\mathcal O_Z(d)$ is invertible, hence finitely presented and flat
over $T$ (locally it is $\mathcal O_Z$, and $q$ is flat). Apply the open-locus theorem to $q$,
this sheaf, degree $0$ and rank $P(d)$. Step 3 says every geometric point factors through that
open locus: over a field its derived image has only degree-zero cohomology, of dimension $P(d)$.
Every point of $T$ is the image of a geometric point; hence this open is all of $T$. Thus
$Rq_*\mathcal O_Z(d)$ is a finite locally free module $E_d$ of rank $P(d)$ in degree zero, and
$E_d=q_*\mathcal O_Z(d)$. The perfect-direct-image base-change theorem supplies the canonical
derived base-change isomorphism for every $T'\to T$. Since a locally free sheaf has no higher
derived pullback, its degree-zero map is exactly $g^*E_d\to q'_*\mathcal O_{Z'}(d)$, which is
therefore an isomorphism. This argument uses no reducedness hypothesis.
Dependencies: lem-pc-flat-rf-open, lem-pc-rf-perfect-base-change.
5. The projective-twist calculation on each affine base open identifies $p_*\mathcal O(d)$ with
$V_d$, freely generated by degree-$d$ monomials; these identifications commute with coefficient
extension. Let $\rho_d:V_d\to E_d$ be restriction. By step 4 its geometric fibres are the
surjections of step 3. The cokernel of $\rho_d$ is locally finitely generated, being a quotient
of the finite locally free $E_d$. At each local ring of $T$ its residue quotient is zero (a
field extension detects zero vector spaces), so Nakayama makes the cokernel zero. The kernel
$K_d$ is finite locally free: locally trivialize $E_d$, lift its finitely many basis elements
through $\rho_d$, and obtain a splitting of $V_d\to E_d$. Thus $K_d$ is a direct summand of a
finite free module. By left exactness of sections, $K_d=p_*\mathcal I(d)$. This proves the
required exact sequence and its ranks.
Dependencies: lem-pc-projective-space-twist-cohomology, lem-weil-pbc-nakayama-local-generators,
lem-weil-pbc-finite-projective-standard-free-cover.
6. The split exact sequence of step 5 stays exact under every pullback, since a splitting pulls
back to a splitting. Its middle term pulls back by coefficient extension, and its last term by
the canonical isomorphism of step 4. Step 1 identifies the pulled-back ideal with the ideal of
$Z_{T'}$. In the commutative diagram of restriction maps, both left terms are the kernels of the
same middle-to-right map. The resulting kernel isomorphism is the canonical base-change map
$g^*p_*\mathcal I(d)\to p'_*\mathcal I_{T'}(d)$: composing either map with its inclusion into
$V'_d$ is restriction of the same polynomial. Thus both direct-image terms and the entire exact
sequence commute with arbitrary base change.
7. At $d=m$, pull the evaluation map $p^*K_m\otimes\mathcal O(-m)\to\mathcal I$ to a geometric
fibre. Steps 1 and 6 identify it with the ordinary global-section evaluation for $\mathcal
I_k(m)$, tensored with $\mathcal O(-m)$. Regularity makes that map surjective. Let $C$ be the
cokernel of the relative evaluation; it is of finite type since $\mathcal I$ is of finite type.
For $x\in\mathbf P^n_T$ over $t$, the geometric-fibre vanishing implies $C_x/\mathfrak m_t
C_x=0$ after (and hence before) the faithfully flat residue-field extension. The ideal
$\mathfrak m_t\mathcal O_{\mathbf P^n_T,x}$ lies in the maximal ideal of this local ring.
Nakayama applied to the finite module $C_x$ gives $C_x=0$. Therefore the evaluation map is
surjective everywhere.
Dependencies: lem-sfb-m-regular-coherent-sheaf-consequences, lem-weil-pbc-nakayama-jacobson.
8. On each geometric fibre, the regularity theorem gives surjective linear multiplication from
degree $b$ to $b+1$ for every $b\geq m$. Induction on $e=d-m$ shows that each section in degree
$d$ is a sum of products of $e$ linear forms and sections in degree $m$. Each product is a
degree-$e$ polynomial, so the composite factors through $V_{d-m,k}\otimes K_{m,k}\to K_{d,k}$
and this map is surjective. For $d=m$ the map is scalar multiplication by $1\in V_0$ and is the
identity. Steps 5--6 identify these maps with the geometric fibres of the required relative
multiplication map. Its cokernel is finitely generated locally on $T$, since $K_d$ is finite
locally free. Applying local Nakayama as in step 5 proves surjectivity on $T$.
Dependencies: lem-sfb-m-regular-coherent-sheaf-consequences,
lem-pc-projective-space-twist-cohomology, lem-weil-pbc-nakayama-local-generators.
-/
theorem exists_uniform_bound (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ z : ℤ, P.eval (d : ℚ) = (z : ℚ)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (T Z : Scheme.{u})
      (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)),
      IsClosedImmersion i → Flat (i ≫ projection T n) →
      LocallyOfFinitePresentation (i ≫ projection T n) →
      QuasiCompact (i ≫ projection T n) → QuasiSeparated (i ≫ projection T n) →
      (∀ t : T, ProjectiveHilbertPolynomial.IsCoordinatePolynomial
        (AlgebraicClosure (T.residueField t)) n
        (ProjectiveHilbertPolynomial.baseChangeEmbedding n i
          (ProjectiveHilbertPolynomial.geometricPoint T t)) P) →
      (∀ d : ℕ, m ≤ d →
        IsIso (polynomialMap T n d) ∧
        (∃ h : sectionInclusion i d ≫ sectionRestriction i d = 0,
          (ShortComplex.mk (sectionInclusion i d) (sectionRestriction i d) h).ShortExact) ∧
        (idealSections i d).IsFiniteLocallyFree ∧
        (polynomialSections T n d).IsFiniteLocallyFree ∧
        (closedSections i d).IsFiniteLocallyFree ∧
        (∀ t : T, ∃ (U : T.Opens) (r : ℕ), t ∈ U ∧ P.eval (d : ℚ) = (r : ℚ) ∧
          Nonempty ((closedSections i d).over U ≅
            SheafOfModules.free (R := T.ringCatSheaf.over U) (ULift.{u} (Fin r)))) ∧
        (∀ (T' : Scheme.{u}) (g : T' ⟶ T),
          IsIso (Scheme.Modules.moduleBaseChangeMap (projection T n)
            (pullback.snd (projection T n) g) g (pullback.fst (projection T n) g)
            pullback.condition (idealTwist i d)) ∧
          IsIso (Scheme.Modules.moduleBaseChangeMap (projection T n)
            (pullback.snd (projection T n) g) g (pullback.fst (projection T n) g)
            pullback.condition (twist T n d)) ∧
          IsIso (Scheme.Modules.moduleBaseChangeMap (i ≫ projection T n)
            (pullback.snd (i ≫ projection T n) g) g
            (pullback.fst (i ≫ projection T n) g) pullback.condition (closedTwist i d)) ∧
          (∃ φ : (Scheme.Modules.tensorPullback
                (pullback.fst (projection T n) g)).obj i.ker.toModules ≅
              (pullback.snd i (pullback.fst (projection T n) g)).ker.toModules,
            φ.hom ≫ (pullback.snd i (pullback.fst (projection T n) g)).ker.toModulesι =
              (Scheme.Modules.tensorPullback (pullback.fst (projection T n) g)).map
                  i.ker.toModulesι ≫
                Scheme.Modules.tensorPullbackObjUnitToUnit
                  (pullback.fst (projection T n) g)) ∧
          (∃ h : (Scheme.Modules.tensorPullback g).map (sectionInclusion i d) ≫
                (Scheme.Modules.tensorPullback g).map (sectionRestriction i d) = 0,
            (ShortComplex.mk
              ((Scheme.Modules.tensorPullback g).map (sectionInclusion i d))
              ((Scheme.Modules.tensorPullback g).map (sectionRestriction i d)) h).ShortExact))) ∧
      Epi (evaluation i (m : ℤ)) ∧
      (∀ e : ℕ, IsIso (polynomialMap T n e) ∧ ∃ μ : polynomialSections T n e ⊗ idealSections i m ⟶
          idealSections i ((m : ℤ) + (e : ℤ)),
        Epi μ ∧ ∀ (U : T.Opens) (s : Γ(twist T n e, projection T n ⁻¹ᵁ U))
          (t : Γ(idealTwist i m, projection T n ⁻¹ᵁ U)),
          μ.app U (Scheme.Modules.tmulSection s t) =
            (idealTwistMultiplication i m e).app (projection T n ⁻¹ᵁ U)
              (Scheme.Modules.tmulSection t s)) := by
  sorry

end

end AlgebraicGeometry.HilbertSectionBound
