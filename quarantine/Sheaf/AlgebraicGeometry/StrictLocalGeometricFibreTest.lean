/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.CohomologyPullbackExactConservative
import Sheaf.AlgebraicGeometry.StrictLocalBaseSections
import Sheaf.AlgebraicGeometry.StrictLocalFibreDerivedUnit

/-! # Testing a strict-local comparison on every geometric strict-local fibre

Source: Stacks Project, Tag 0EZV, with the corrected every-lift formulation
(blueprint: lem-weil-pbc-strict-local-geometric-fibre-test).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Pullback on cohomology with the coefficients identified by inverse-image composition.
Source: Stacks Project, Tags 0EZV and 03Q1
(blueprint: lem-weil-pbc-strict-local-geometric-fibre-test). -/
noncomputable def cohomologyPullbackOver
    {Y E T : Scheme.{u}} (p : Y ⟶ E) (a : E ⟶ T)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} a).obj F) q →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (p ≫ a)).obj F) q :=
  (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} p a).inv.app F) q).comp
    (cohomologyMap p ((upperStar AddCommGrpCat.{u + 1} a).obj F) q)

/-- The map B ×_S T → A ×_S T induced by canonical strict-local functoriality.
Source: Stacks Project, Tag 0EZV
(blueprint: lem-weil-pbc-strict-local-geometric-fibre-test). -/
noncomputable def strictLocalComparisonMorphism
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {K : Type u} [Field K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f)) :
    pullback (Scheme.strictHenselizationStructuralMap x ≫ f)
        (u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)) ⟶
      pullback (Scheme.strictHenselizationStructuralMap (x ≫ f))
        (u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f)) :=
  pullback.map _ _ _ _ (Scheme.strictHenselizationMap f x) (𝟙 _) (𝟙 _)
    (by simpa using (Scheme.strictHenselizationMap_over f x).symm) (by simp)

private theorem bijective_cohomologyPullbackOver_iff
    {Y E T : Scheme.{u}} (p : Y ⟶ E) (a : E ⟶ T)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (cohomologyPullbackOver p a F q) ↔
      Function.Bijective (cohomologyMap p
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) q) := by
  have hcoeff : Function.Bijective
      (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} p a).inv.app F) q) := by
    exact ConcreteCategory.bijective_of_isIso
      ((Sheaf.functorH _ q).map ((upperStarComp AddCommGrpCat.{u + 1} p a).inv.app F))
  rw [cohomologyPullbackOver, AddMonoidHom.coe_comp,
    Function.Bijective.of_comp_iff' hcoeff]
  rfl

/-- The strict-local comparison is invertible iff the comparison for every lift is.
Source: Stacks Project, Tag 0EZV, corrected every-lift formulation
(blueprint: lem-weil-pbc-strict-local-geometric-fibre-test).
Proof step 1: Set $T=\operatorname{Spec}K$, $E=A\times_ST$, $Y=B\times_ST$, $p=h\times_ST:Y\to E$,
and $a:E\to T$. Choose an affine open chart of $S$ containing $\bar s$; $t$ factors through it
because it factors through the local scheme $A$ and any open containing its closed point contains
all its points. In the strict-local limit one can restrict to pointed affine neighbourhoods
mapping into this chart: pull back any neighbourhood along the chart and choose an affine open
containing its distinguished point. By the defining ring colimit for $A$ and the universal
properties of tensor products and colimits, $E=\operatorname{Spec}C$ with $C=\varinjlim_i C_i$,
where $C_i$ are etale $K$-algebras obtained by base change of these affine etale neighbourhoods.
Concretely, a compatible family of maps from their tensors to a $K$-algebra is exactly a
compatible family of maps from the original coordinate rings agreeing on the chart ring. Etale
base change and the finite-separable-product theorem, followed by triviality of finite separable
extensions of $K$, give $C_i\cong K^{I_i}$ for finite sets $I_i$. The limit interpretation is
justified by the small-colimit spectrum theorem. These decompositions are as $K$-algebras, NOT as
$A$-algebras; no claim that different $v$ give the same $A$-fibre is made.

Proof step 2: For every prime $z$ of $C$, its pullback to each finite product $K^{I_i}$ selects a
unique factor, by the finite-product spectrum statement. If $c\in C$ is represented by
$(\lambda_j)_j\in K^{I_i}$ and the selected factor is $j_0$, the corresponding idempotent
$e_{j_0}$ is outside $z$ and kills $c-\lambda_{j_0}$. Consequently every element of $C_z$ is a
scalar in $K$: denominators outside $z$ have nonzero selected scalar and can be inverted in $K$.
The structural map $K\to C_z$ is injective since it is a map from a field to a nonzero local ring.
Thus $C_z\cong K$, compatibly with the structural maps. Every prime is therefore maximal, and the
zero-dimensional spectrum theorem makes $|E|$ profinite. Points of $E$ are exactly $K$-morphisms
$T\to E$, equivalently lifts $v:T\to A$ of $t$, since each residue field is canonically $K$. The
given $u$ supplies one such point, so $E$ is nonempty. Finite stages can have unused factors; no
surjectivity of their transition maps is assumed.

Proof step 3: For each $z\in E$, choose a geometric point $\bar z:\operatorname{Spec}\Omega\to E$
inducing an embedding $K=\kappa(z)\to\Omega$, with $\Omega$ algebraically closed. Clopen pointed
neighbourhoods of $z$ are cofinal among the pointed etale neighbourhoods of $\bar z$. Indeed
choose an affine open $\operatorname{Spec}D$ around the distinguished point of such a
neighbourhood. Its fibre $D\otimes_C K$ is etale over $K$ by etale base change; the finite-
separable-product theorem and separable closedness identify it with a finite product of copies of
$K$. Thus its given map to $\Omega$ selects a factor and comes from a $K$-point: the pointed map
$D\to\Omega$ factors through $D\to K=C_z$. By the affine-etale ring criterion, $D$ is a finitely
presented $C$-algebra. Write the finitely many generator images in $C_z$ as fractions and invert
the product of their denominators, all outside $z$. Each defining relation vanishes in $C_z$, so
invert one further element outside $z$ annihilating it, for each of the finitely many relations.
This produces a $C$-map $D\to C_s$, $s\notin z$, hence a section over $D(s)$ through the
prescribed point. The clopen basis supplies $z\in W\subseteq D(s)$, and restriction gives a
pointed map $W\to\operatorname{Spec}D$. By the clopen-idempotent theorem, each such $W$ is
$D(e)=\operatorname{Spec}C_e$ for an idempotent $e$ of $C$, so it is an affine etale
neighbourhood. Two such clopen refinements have common refinement their intersection. To equalize
two pointed maps from a clopen into a neighbourhood, first shrink around $z$ into an affine open
of that neighbourhood containing their common distinguished point. On its finitely many algebra
generators the two maps have differences zero in $C_z$; invert finitely many annihilators outside
$z$ and take a smaller clopen. The maps then agree, since they agree on every generator. This
proves cofinality, including the equalization condition, for every choice of $\Omega$ and
embedding $K\to\Omega$. Hence the stalk of any abelian sheaf at $\bar z$ is computed on the same
clopen system, independently of $\Omega$. A germ has a representative on a clopen $W$; gluing it
with the zero section on the disjoint open complement gives a global section with that germ.
Therefore $\Gamma(E,G)=0$ implies that every geometric stalk of $G$ vanishes, and geometric-stalk
conservativity gives $G=0$. The argument also applies to $T=\operatorname{Spec}K$; its clopen
neighbourhood system has the single nonempty object $T$, so for every geometric point of $T$ the
germ map $F(T)\to F_{\bar t}$ is an isomorphism.

Proof step 4: Every point of the affine scheme $E$ is closed and every residue field is the
separably closed field $K$, by step 2. Apply the affine closed-point acyclicity theorem to EVERY
abelian sheaf on $E$: all positive right derived functors of $\Gamma(E,-)$ vanish. The category of
abelian etale sheaves has enough injectives by [lem-weil-pbc-module-sheaves-enough-injectives];
global sections is additive and left exact since evaluation preserves kernels. Apply [lem-weil-
pbc-derived-functor-long-exact] to a short exact sequence: its segment
$\Gamma(E,G_1)\to\Gamma(E,G_2)\to\Gamma(E,G_3)\to H^1(E,G_1)=0$ therefore says $\Gamma(E,-)$ is
exact. Combined with the zero-detection argument of step 3, it reflects isomorphisms: a sheaf
morphism has invertible global sections precisely when its kernel and cokernel have zero global
sections, precisely when both vanish. The same acyclicity theorem applies to $T$, so $H^q(T,F)=0$
for $q>0$.

Proof step 5: Put $G=a^{-1}F$. The map $p$ is affine: both $E$ and $Y$ are affine schemes, and $p$
is induced by their coordinate-ring homomorphism. Hence it is quasi-compact and quasi-separated.
The canonical Leray comparison for $p$, with the explicit derived-unit description of cohomology
pullback, identifies $H^q(Y,p^{-1}G)$ with $\Gamma(E,R^qp_*p^{-1}G)$, because exactness of
$\Gamma(E,-)$ lets it commute with kernels, images and cokernels of a representing complex. For
$q=0$ the first comparison in the statement is $\Gamma(E,\eta)$ for the unit $\eta:G\to
p_*p^{-1}G$. It is invertible iff $\eta$ is an isomorphism by step 4. For $q>0$ its source
vanishes and it is invertible iff $\Gamma(E,R^qp_*p^{-1}G)=0$, iff $R^qp_*p^{-1}G=0$. Composition
of inverse images identifies $p^{-1}G$ with the coefficient sheaf pulled back from $T$ to $Y$.
Thus we have reduced the first comparison to a sheaf isomorphism in degree zero or a sheaf
vanishing in positive degree, without any torsion assumption.

Proof step 6: Fix $z\in E$, equivalently a lift $v:T\to A$, and a geometric point $\bar
z:\operatorname{Spec}\Omega\to E$ over it as in step 3. Cofinality of the clopen neighbourhoods
from step 3 identifies the strict localization of $E$ at $\bar z$ with $\operatorname{Spec}C_z=T$:
the clopen-idempotent theorem writes each affine clopen as $D(e)=\operatorname{Spec}C_e$. The ring
colimit of these $C_e$ is the ordinary localization $C_z$: its natural map to $C_z$ is surjective
since every fraction $c/s$ is defined on a clopen inside $D(s)$, and is injective since a section
zero in $C_z$ is annihilated by some element outside $z$ and becomes zero on a smaller clopen
inside its basic open. Thus the ring colimit over pointed etale neighbourhoods is $C_z$, since
every denominator outside $z$ is inverted on a clopen neighbourhood contained in its basic open,
and step 2 identifies that localization with $K$. The unrestricted strict-henselization stalk
theorem applies to the affine, hence qcqs, morphism $p$ and the abelian sheaf $p^{-1}G$. It gives
$(R^qp_*p^{-1}G)_{\bar z}\cong H^q(Y\times_E T,F)$. Fibre-product associativity, checked by their
projections, identifies $Y\times_E T$ with $B\times_{A,v}T$. By the inverse-image stalk-and-germ
theorem for $a:E\to T$, the source stalk $G_{\bar z}$ is $F_{a\bar z}$; step 3 on $T$ identifies
this canonically with $F(T)=H^0(T,F)$. For $q=0$ the stalk of $\eta$ is the section-pullback unit
$H^0(T,F)\to H^0(B\times_{A,v}T,F)$: a clopen representative of a germ restricts along the section
in step 3, and its unit image restricts along the base-changed section, giving exactly the fibre
pullback. For $q>0$, $H^q(T,F)=0$ by step 4, so the fibre comparison is invertible exactly when
this higher-direct-image stalk vanishes. The clopen system is independent of the chosen $\Omega$
by step 3, so these identifications hold for every geometric point over $z$. This identifies the
actual canonical maps, not just abstract groups.

Proof step 7: For $q=0$, geometric-stalk conservativity says that the unit in step 5 is an
isomorphism iff its stalk map at EVERY geometric point of $E$ is an isomorphism. For $q>0$ apply
the same statement to $0\to R^qp_*p^{-1}G$, so vanishing is equivalent to vanishing at EVERY
geometric stalk. By steps 2, 3 and 6 these conditions are precisely the comparisons for every lift
$v:T\to A$ over $t$. This proves the corrected equivalence and, by taking $v=u$, the one-way
implication needed by the existing smooth-local-acyclicity citer. The original assertion for only
one selected lift is false; the inherited stage-1 correction records the invalid $A$-linear
identification in the source.
-/
theorem strictLocalGeometricFibreTest
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (K : Type u) [Field K] [IsSepClosed K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (cohomologyPullbackOver (strictLocalComparisonMorphism f x u)
      (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f))
        (u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f))) F q) ↔
    ∀ v : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (x ≫ f),
      v ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
        u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) →
      Function.Bijective (cohomologyMap
        (pullback.snd (Scheme.strictHenselizationMap f x) v) F q) := by
  obtain ⟨hΓ, hconservative⟩ :=
    strictLocalBase_sections_exact_conservative (x ≫ f) K u
  have := hΓ
  have := hconservative
  let p := strictLocalComparisonMorphism f x u
  let a := pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f))
    (u ≫ Scheme.strictHenselizationStructuralMap (x ≫ f))
  apply (bijective_cohomologyPullbackOver_iff p a F q).trans
  exact (bijective_cohomologyMap_iff_isIso_derivedPullbackUnitHomology p
    ((upperStar AddCommGrpCat.{u + 1} a).obj F) q).trans
      (strictLocalFibre_derivedUnit_iff f x K u F q)

end AlgebraicGeometry.Etale
