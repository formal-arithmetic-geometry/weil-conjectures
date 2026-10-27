/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.SectionRingProjOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Connected.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-! # Extending square-condition translations to Proj neighborhoods

Source: Guo, Divisors on coherent schemes and homogeneous spaces, sections 5.6 and 6.1,
Proposition 6.2, first assertion before (i)--(iii), printed pages 14--15
(blueprint: lem-sfb-square-action-proj-translation-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.SchemeAction

open Scheme.Modules

/-- Each translation extends to a B-isomorphism of two open neighborhoods of the canonical
section-ring Proj image. The two pullback projections uniquely characterize r_B as the
base change of r.
The two open factorization equations express containment of its entire image in both opens.
The next equation says that the isomorphism is over B, and the last
one is σ_g r_B = r_B τ_g after factorization. All square-condition isomorphisms occur under
Nonempty: neither choices nor coherence are assumptions or conclusions.

Source: Guo, sections 5.6 and 6.1, Proposition 6.2, first assertion before (i)--(iii)
(blueprint: lem-sfb-square-action-proj-translation-extension).

Proof:
1. Fix a smooth affine $B\to S$. It is flat by [lem-pc-smooth-flat]. The finite-presentation
hypothesis includes quasi-compactness. By [lem-pc-quasi-compact-base-change] and
[lem-weil-pbc-separated-base-change], $q:Y=X_B\to B$ is quasi-compact and separated. Since $B$ is
affine, [lem-weil-pbc-qcqs-over-affine] makes $Y$ quasi-compact and quasi-separated. Put
$R=\Gamma(S,\mathcal O_S)$ and $T=\Gamma(B,\mathcal O_B)$. Applying
[lem-pc-flat-base-change-cohom] in degree zero to $M^{\otimes n}$ gives $\Gamma(Y,M_B^{\otimes
n})=\Gamma(X,M^{\otimes n})\otimes_R T$. The maps send $s\otimes b$ to $b\,s_B$; their product on
two pure tensors is $(s\otimes b)(t\otimes c)=st\otimes bc$, so they form a graded $T$-algebra
isomorphism. By [lem-nagata-affine-proj-scalar-extension], $P_B$ identifies with
$P_L=\operatorname{Proj}\Gamma_*(Y,L)$ for $L=M_B$. Under this identification $r_B=r_L$: on the
pulled-back standard charts both maps have the fraction formula $t/s^k\mapsto t_B/s_B^k$ of
[lem-sc-ample-proj-canonical-map]. These charts cover by the scalar-extension node. The original
section opens pull back to a cover of $Y$, so $r_L$ is defined everywhere. To form $r_B$,
first check $p r=f$: the normalized fraction formula in degree zero sends each coefficient
from $S$ to its pullback along $f$, so maps into affine $S$ agree on functions. The pullback
universal property then gives $r_B$ with projections $r\circ\mathrm{pr}_X$ and $\mathrm{pr}_B$;
these two equations uniquely determine it.

2. Fix $g\in H(B)$ and write $\tau=\tau_g:Y\to Y$. The action identities give the inverse
$\tau_{g^{-1}}$. Put $K=\tau^*L$, $J=\tau_{g^{-1}}^*L$ and $D=\tau_{g^2}^*L$. They are invertible
by the local rank-one description [def-sc-invertible-module]. Every translate is covered by its
positive-power section opens: pull back the covering for $L$ along the corresponding automorphism.
Applying the assumed square identity to $(g,g^{-1})$, and then pulling that identity back by
$\tau$, using that $\tau^*$ carries tensor products to tensor products
[lem-pc-scheme-pullback-monoidal-existing], gives invertible modules $N_0,N_1$ on $B$ and
isomorphisms $L^{\otimes2}\cong K\otimes J\otimes q^*N_0$ and $K^{\otimes2}\cong D\otimes L\otimes
q^*N_1$. In the second formula use $\tau_{g^{-1}}\circ\tau_g=\mathrm{id}$,
$\tau_g\circ\tau_g=\tau_{g^2}$ and $q\tau=q$.

3. Let $t\in\Gamma(Y,K^{\otimes n})$, $n>0$, and $y\in Y_t$. Since positive-power section opens
for $J$ cover, choose $m>0$ and $u\in\Gamma(Y,J^{\otimes m})$ nonzero at $y$. The first identity
of Step 2 identifies $t^{\otimes m}\otimes u^{\otimes n}\otimes q^*v$ with a section $s$ of
$L^{\otimes2nm}$, for any $v\in\Gamma(B,N_0^{\otimes nm})$. The module $N_0^{\otimes nm}$ is
invertible and thus quasi-coherent of finite type;
[lem-weil-pbc-affine-finite-type-generating-sections] gives a global generator family. At $q(y)$
some member $v$ has nonzero residue. Then $s(y)\ne0$ and $Y_s\subseteq Y_t$. Indeed, in a local
frame $s$ has coefficient $a^m b^n c$, where $a,b,c$ are the coefficients of $t,u,q^*v$. A product
in the residue field is nonzero exactly when every factor is nonzero. Thus each $K$-section open
is refined at every point by an $L$-section open.

4. Conversely, let $s\in\Gamma(Y,L^{\otimes d})$, $d>0$, and $y\in Y_s$. Choose $e>0$ and
$u\in\Gamma(Y,D^{\otimes e})$ nonzero at $y$. Apply
[lem-weil-pbc-affine-finite-type-generating-sections] on the affine $B$ to $N_1^{\otimes de}$ and
choose a global section $v$ nonzero at $q(y)$. The second identity of Step 2 carries $u^{\otimes
d}\otimes s^{\otimes e}\otimes q^*v$ to $t\in\Gamma(Y,K^{\otimes2de})$. Its residue at $y$ is
nonzero and $Y_t\subseteq Y_s$, since its local coefficient is the product of those of
$u^d,s^e,q^*v$. This proves the other refinement condition. No base twist was assumed globally
trivial.

5. Apply [lem-sfb-cofinal-section-opens-proj-neighborhood] to $Y/B,L,K$, with the two covers of
Step 2 and the refinements of Steps 3--4. It gives $\theta:V_L\simeq V_K$ with $\theta r_L=r_K$.
Pullback along $\tau$ gives a graded $T$-algebra isomorphism
$\alpha:\Gamma_*(Y,L)\simeq\Gamma_*(Y,K)$: on each degree it is pullback of sections, inverse to
pullback by $\tau^{-1}$ with the canonical line identifications, and it preserves multiplication
of tensor sections. By [prop-nagata-relative-proj-functoriality] it induces $F:P_K\simeq P_L$.
Concretely, [lem-nagata-affine-proj-scalar-extension] applied to both rings equal to $T$ with the
identity map, the graded rings $\Gamma_*(Y,L)$, $\Gamma_*(Y,K)$ and the graded isomorphism
$\alpha$ (after $T\otimes_T\Gamma_*(Y,L)=\Gamma_*(Y,L)$) gives $F$ as the morphism cartesian over
$\operatorname{Spec}(\mathrm{id}_T)$, with $F^{-1}(D_+(s))=D_+(\tau^*s)$ and the chart ring map
$t/s^k\mapsto\tau^*t/(\tau^*s)^k$. The canonical-map formula [lem-sc-ample-proj-canonical-map]
gives $F r_K=r_L\tau$: over $D_+(s)$ both composites are defined on
$r_K^{-1}D_+(\tau^*s)=\tau^{-1}(Y_s)$ and induce $t/s^k\mapsto\tau^*t/(\tau^*s)^k=\tau^*(t/s^k)$
on global sections, and $D_+(s)$ is affine. Set $U_g=V_L$, $U'_g=F(V_K)$ and $\sigma_g=F\theta$,
transported through $P_L=P_B$ from Step 1. Both opens contain $r_B(Y)$, since
$F(r_K(Y))=r_L(\tau(Y))=r_L(Y)$. Finally $\sigma_g r_B=F r_K=r_B\tau_g$, as required.
-/
theorem exists_proj_translation_neighborhood
    (S : Scheme.{u}) [IsAffine S]
    (H X : Over S) [GrpObj H] [ModObj H X]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFinitePresentation H.hom]
    [QuasiCompact H.hom]
    (hH : ∀ s : S, ConnectedSpace (H.hom.fiber s))
    [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom]
    (M : X.left.Modules) [M.IsInvertible]
    (hsquare : ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((tensorPullback ((lift ((snd X B ≫ (g * h)) • fst X B) (snd X B)).left)).obj
              ((tensorPullback (fst X B).left).obj M) ⊗
            (tensorPullback (fst X B).left).obj M) ≅
           (((tensorPullback ((lift ((snd X B ≫ g) • fst X B) (snd X B)).left)).obj
               ((tensorPullback (fst X B).left).obj M) ⊗
             (tensorPullback ((lift ((snd X B ≫ h) • fst X B) (snd X B)).left)).obj
               ((tensorPullback (fst X B).left).obj M)) ⊗
            (tensorPullback (snd X B).left).obj N)))
    (hcover : ∀ x : X.left, ∃ (d : ℕ) (s : sectionRingGrade M d),
      0 < d ∧ x ∈ nonvanishingLocus (M.tensorPow d) (s.val d)) :
    ∀ (B : Over S) [IsAffine B.left] [Smooth B.hom] (g : B ⟶ H),
      ∃ rB : (X ⊗ B).left ⟶
          Limits.pullback (sectionRingProjStructure X.hom M) B.hom,
        rB ≫ Limits.pullback.fst (sectionRingProjStructure X.hom M) B.hom =
          (fst X B).left ≫ sectionRingProjMap M hcover ∧
        rB ≫ Limits.pullback.snd (sectionRingProjStructure X.hom M) B.hom =
          (snd X B).left ∧
      ∃ (U U' : (Limits.pullback (sectionRingProjStructure X.hom M) B.hom).Opens)
        (σ : U.toScheme ≅ U'.toScheme)
        (rU : (X ⊗ B).left ⟶ U.toScheme) (rU' : (X ⊗ B).left ⟶ U'.toScheme),
        rU ≫ U.ι = rB ∧
        rU' ≫ U'.ι = rB ∧
        σ.hom ≫ U'.ι ≫ Limits.pullback.snd (sectionRingProjStructure X.hom M) B.hom =
          U.ι ≫ Limits.pullback.snd (sectionRingProjStructure X.hom M) B.hom ∧
        rU ≫ σ.hom = (lift ((snd X B ≫ g) • fst X B) (snd X B)).left ≫ rU' := by
  sorry

end AlgebraicGeometry.SchemeAction
