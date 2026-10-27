/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.SmoothPurityTowerP1Data
import Sheaf.Paper.TowerP1ComparisonsWithLine
import Sheaf.Paper.TowerP1KernelScalarNormalization
import Sheaf.Paper.TowerP1TriangleFactorization
import Sheaf.Paper.TowerP1ProjectionTraceIdentification
import Sheaf.Paper.TowerP1FiniteAdjunctionAssembly
import Sheaf.Paper.TowerP1UniformPresentation

/-! # The projective-line adjunction on ordinary coefficient towers

Source: blueprint main-20261015, sec-smooth-purity,
`sk-prop-sp-tower-geometric-p1.md` (blueprint: det-sp-tower-p1-adjunction).
The domain is bounded below with etale-origin levels. No normalization is imposed.
All natural-number indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The projective-line tower adjunction with its specified diagonal unit and splitting trace
counit, all positive finite levels, and its constructible finite-Tor restriction.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.md and its proof
(blueprint: det-sp-tower-p1-adjunction).

Proof plan, in the order of the DAG:

1. Put $P=\mathbf P^1_S$, $W=P\times_SP$, $A_T=\mathcal O_{E,T}/\ell^\bullet$, $F=Rq_{*,\bullet}$
and $G=q_\bullet^*(-)(1)[2]$. By [sk-lem-sp-tower-levels], these direct images are bounded below
and evaluate to the finite direct images. The canonical comparison
[lem-weil-pbc-comparison-direct-image-canonical-mate] applies to $q,p_1,p_2,\Delta$, which are
quasi-compact and quasi-separated, and therefore their direct images preserve etale-origin levels.
Pullback preserves such levels by [lem-weil-pbc-comparison-pullback]. The finite twist is a
locally free rank-one sheaf, compatible with pullback, by [lem-asd-etale-finite-twist-pullback]
with $N=\ell^n$ and $A=\mathcal O_E/\ell^n$. Thus $F,G$ preserve the stated bounded-below
etale-origin domains.

2. Each of $q,p_1,p_2$ is a projective-line projection, hence proper by
[lemma-nagata-projective-space-base-change-proper]. The diagonal is a closed Cartier divisor by
[det-sp-tower-classes], hence proper by [lem-weil-pbc-closed-immersion-proper](a). Its
complementary open is quasi-compact: over each affine open of $W$, finitely many principal opens
trivialize the invertible ideal, and the complement on each is one more principal open. Thus
[lem-exc-proetale-closed-exact] makes $\Delta_*$ exact at every finite level. Exactness on towers
is levelwise by [det-sp-coefficient-towers-abelian], so $R\Delta_{*,\bullet}=\Delta_*$, justifying
the notation in the unit formula.

3. Form the canonical tensor, projection, composition and exchange maps on the simultaneous
section models [lem-coef-semilinear-derived-sections]. These exist in the ambient unbounded
derived category and evaluate to their finite maps. At level $n$, put $B=\mathcal O_E/\ell^n$. On
the ordinary etale site, [lem-kun-0f0g] makes the projection maps for $q,p_1,p_2,\Delta$
invertible for these coefficients and arbitrary derived inputs. For the present etale-origin
inputs, [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applied to $\nu^*$ transports tensor,
and [lem-weil-pbc-comparison-direct-image-canonical-mate] transports the direct images of the
bounded-below arguments. The canonical comparisons transport the projection map itself: both maps
are the transpose of the same counit tensored with identity, so the normalization in the
direct-image comparison identifies their transposes. The finite etale projection identities also
show that the tensors occurring here are bounded below: their targets are respectively
$Rq_*q^{-1}K(1)[2]$, $R\Delta_*M$, or $Rp_{i*}p_i^{-1}M(1)[2]$. For the last two projection
reorderings, $Rp_{i*}B_W(1)[2]$ is a sum of two shifted flat lines by
[lem-sp-tower-p1-arbitrary-base-integrals], so its tensor with $M$ is bounded below. Proper
exchange is invertible by [lem-kun-proper-base-change-torsion-ring], and the same counit-mate
normalization transports its actual map. Hence every evaluated projection and exchange map used
here is invertible. Tower evaluation detects isomorphisms by [det-sp-tower-shriek-levels](3), so
the actual tower maps are invertible. This avoids applying that node's restricted finite-Tor
projection clause outside its hypotheses.

4. The projection isomorphism for $\Delta$, with $\Delta^*p_1^*M=M$, identifies $\Delta_*M$ with
$\Delta_*A_P\otimes^Lp_1^*M$. Exchange identifies $Rp_{2*,\bullet}p_1^*M$ with $q_\bullet^*FM$,
and the projection formula for $q$ identifies $FGK$ with $K\otimes^LRq_{*,\bullet}A_P(1)[2]$, as
in step 3. Composing with the actual diagonal class and trace of [det-sp-tower-classes] gives
precisely the displayed natural $\eta$ and $\varepsilon$. Their naturality and evaluations follow
from [lem-coef-semilinear-derived-sections]. Write $t_i=\operatorname{Tr}_{p_i,\bullet}$. Under
exchange $t_i$ is the base change of the trace for $q$: the splitting components are the unit and
$c_1(\mathcal O(1))$; pullback preserves the unit, pulls back $\mathcal O(1)$, and commutes with
the Kummer boundary. It therefore carries the splitting, its inverse, and its second projection to
those on the base change. This is an identity of the actual tower constructions, not an inference
of equality from evaluation.

5. *The two scalar endomorphisms and detection.* Let
$\alpha_i:A_P\xrightarrow{\sim}Rp_{i*,\bullet}\Delta_*A_P$ be the composition identification for
$p_i\Delta=1_P$, and put $c_i=t_i\circ Rp_{i*,\bullet}(\delta_\bullet)\circ\alpha_i$. These are
endomorphisms of $A_P[0]$. Apply [lem-weil-pbc-derived-single-fully-faithful] to the abelian tower
category of [det-sp-coefficient-towers-abelian]: each $c_i$ is a unique compatible family of
module-sheaf maps. If all evaluated $c_i$ are identities, their underlying families equal the
identity family, so $c_i=1$. This uses equality detection only between these degree-zero objects.
The composition identification is the canonical derived-direct-image comparison supplied on tower
section models by [lem-coef-semilinear-derived-sections].

6. Fix $n\geq1$ and put $N=\ell^n$, $B=\mathcal O_E/\ell^n$. This is a finite torsion ring and $N$
is invertible on $S$. Exact evaluation and the canonical direct-image comparison identify the
level of $c_i$ from step 5 with the pro-etale image of the finite etale composite $t_P\circ
Rp_{i*}(\delta_B)\circ\alpha_i$: [sk-lem-sp-tower-levels] and
[lem-coef-semilinear-derived-sections] identify the actual direct-image and composition maps,
[lem-weil-pbc-comparison-direct-image-canonical-mate] specifies the comparison, and
[det-sp-tower-classes] identifies the evaluated splitting, trace and supported class. The finite
identity is exactly [lem-sp-tower-p1-arbitrary-base-integrals], which assumes neither a Noetherian
nor a finite-type base. Applying $\nu_P^*$ gives $(c_i)_n=1$ for both $i$. Step 5 now gives
$c_1=c_2=1$ in the ordinary derived category of towers.

7. *First triangle, integrating along $p_1$.* Expand $F\eta_M$ using its definition, replace
$qp_2$ by $qp_1$, and then apply $\varepsilon_{FM}$. With the canonical direct-image composition
maps and the projection formula established in step 3 this gives
$$FM=R(qp_1)_{*,\bullet}\Delta_*M\longrightarrow R(qp_1)_{*,\bullet}p_1^*M(1)[2]\simeq
F\bigl(M\otimes^LRp_{1*,\bullet}A_W(1)[2]\bigr)\xrightarrow{F(1_M\otimes t_1)}FM.$$ Here $t_1$ is
the base-changed trace identified in step 4. The first arrow is $\delta_\bullet\otimes p_1^*M$.
Naturality of the projection comparison identifies its pushforward along $p_1$, including the
source identification $\Delta^*p_1^*M=M$, with $1_M\otimes Rp_{1*,\bullet}\delta_\bullet$. The
exchange and projection reordering is the equality in
[lem-weil-pbc-ringed-exchange-tensor-coherence] on the tower-topos ring object $A_\bullet$;
[lem-coef-semilinear-derived-sections] supplies the specified composition comparisons on this
model. Thus the entire composite is $F(1_M\otimes c_1)=1_{FM}$ by step 6, rather than merely a map
which becomes an identity on evaluation.

8. *Second triangle, integrating along $p_2$.* Put $M=GK$. On $W$ both $p_1^*M$ and $p_2^*M$ equal
$(qp_1)^*K(1)[2]$, since $qp_1=qp_2$ and the twist pulls back from $S$. Factor $p_2^*M$ out of
$Rp_{2*,\bullet}(A_W\otimes^Lp_2^*M)(1)[2]$ using the projection formula established in step 3.
The arrow induced by $\delta_\bullet$ becomes $1_M\otimes Rp_{2*,\bullet}\delta_\bullet$, with
source $M\otimes A_P$. Under proper exchange, $G\varepsilon_K$ contracts the remaining factor
$Rp_{2*,\bullet}A_W(1)[2]$ by $t_2$, by step 4. The exchange/projection compatibility
[lem-weil-pbc-ringed-exchange-tensor-coherence] on the same tower ringed topos verifies these are
the canonical maps. Hence $G\varepsilon_K\circ\eta_{GK}=1_{GK}\otimes c_2=1_{GK}$. Only even
shifts have been moved past tensor factors, so their Koszul signs are $(-1)^{2j}=1$. The
interchange of the two unshifted twist lines is also the identity: locally choose a generator $e$;
the symmetry sends $ae\otimes be$ to $be\otimes ae=ab(e\otimes e)$ over the commutative
coefficient ring. These local equalities give the stated canonical symmetry globally.

9. *Adjunction from the two triangles.* For a tower map $u:FM\to K$ define
$\Phi(u)=G(u)\circ\eta_M$, and for $v:M\to GK$ define $\Psi(v)=\varepsilon_K\circ F(v)$.
Naturality and step 7 give $\Psi\Phi(u)=u\circ\varepsilon_{FM}\circ F\eta_M=u$. Naturality and
step 8 give $\Phi\Psi(v)=G\varepsilon_K\circ\eta_{GK}\circ v=v$. These operations are natural in
$M,K$, so they are the Hom bijection exhibiting $F\dashv G$ with the specified unit and counit.

10. *Evaluation and restriction.* For each $n\geq1$, exact evaluation sends $A_\bullet$ to
$(\mathcal O_E/\ell^n)_T$, sends $\delta_\bullet$ to the finite supported diagonal class, and
sends the splitting inverse followed by its second projection to the finite trace, by
[det-sp-tower-classes]. The specified tensor, direct-image, exchange and projection comparisons
evaluate to their finite comparisons by the section models [lem-coef-semilinear-derived-sections]
and the maps constructed in step 3; shifts and inverse image are termwise. Substituting these in
the displayed formulas gives the finite diagonal-defined unit and splitting-trace-defined counit
with the actual coefficients $B=\mathcal O_E/\ell^n$.

11. Here is an explicit verification that these maps form the finite adjunction on bounded-below
etale-origin levels. Given a bounded-below complex $L$ of etale $B$-module sheaves on a scheme
$T$, put $\nu_T^*L$ at level $n$ and the zero complex at every other level, with every transition
zero. This is a bounded-below complex of towers by the componentwise definition
[sk-def-sp-coefficient-towers], and is in $\mathscr C^+(T)$. Denote its derived object by $J_nL$.
Write $F_n=Rq_{*,B}$ and $G_n=q^{-1}(-)(1)[2]$ on the finite etale categories. Evaluate the first
tower triangle of step 7 on $J_nM$, for arbitrary $M\in D^+(P_{\mathrm{et}},B)$: the specified
comparisons give $$\nu_S^*\bigl(\varepsilon_{n,F_nM}\circ F_n(\eta_{n,M})\bigr)=1_{\nu_S^*F_nM}.$$
Evaluate the second tower triangle of step 8 on $J_nK$, for arbitrary $K\in
D^+(S_{\mathrm{et}},B)$: they give
$$\nu_P^*\bigl(G_n(\varepsilon_{n,K})\circ\eta_{n,G_nK}\bigr)=1_{\nu_P^*G_nK}.$$ Full faithfulness
[sk-prop-sf-comparison] removes $\nu^*$ from both equalities. Thus the finite maps satisfy both
triangles for every finite bounded-below input. Explicitly the inverse Hom operations are
$u\mapsto G_n(u)\eta_{n,M}$ and $v\mapsto\varepsilon_{n,K}F_n(v)$, whose composites are
$u\varepsilon_{n,F_nM}F_n\eta_{n,M}=u$ and $G_n\varepsilon_{n,K}\eta_{n,G_nK}v=v$. This proves the
finite adjunction over the arbitrary base using the evaluated maps.

12. Now assume the standing setting [sk-def-sfb-dc-setting]: $S$ is separated and of finite type
over a field of characteristic $p>0$, with $p\ne\ell$. To see that the full uniformly bounded
constructible finite-Tor subcategories lie in $\mathscr C^+$, use
[sk-thm-pe-constructible-comparison] locally on affine $U$ and
[det-pe-classical-derived-equivalence] with [sk-prop-sf-comparison]: the classical cohomology
condition is local, so the bounded-below equivalence gives a global etale-origin witness for each
bounded constructible level. Uniform cohomological bounds give a bounded-below tower because tower
cohomology and vanishing are levelwise [det-sp-coefficient-towers-abelian].

13. [sk-lem-sp-tower-bound], with $f=q$, preserves uniformly bounded constructible finite-Tor
towers under $F$. The map $q$ is a separated finite-type morphism of the standing schemes, smooth
of relative dimension one, so this application satisfies the hypotheses of
[sk-lem-sp-tower-bound].

14. For $G$ the bounds can be checked locally over each affine open $U\subseteq S$, where both $U$
and $\mathbf P^1_U$ are quasi-compact and quasi-separated. With $B=\mathcal O_E/\ell^n$, the
constructible comparison [sk-thm-pe-constructible-comparison] gives a bounded constructible etale
representative $L_n$ of $K_n|_U$. The same fixed Tor interval $[a,b]$ holds for $L_n$ by
[lem-exc-comparison-tor-interval]. Choose its flat representative supported in $[a,b]$ using
[lem-sf-etale-flat-model]. A bounded complex of flat sheaves is K-flat: tensoring each flat term
with an acyclic complex is acyclic, and the finite filtration by shifted terms gives the assertion
for the complex. The termwise pullback along $q$ is K-flat with flat terms by
[lem-weil-pbc-ringed-topos-kflat-pullback], and remains supported in $[a,b]$. Tensor with the
locally free rank-one twist of [lem-asd-finite-etale-twist-line] and shift by $[2]$ gives a flat
complex supported in $[a-2,b-2]$; its tensor with any degree-zero test sheaf has no other terms,
so this is its Tor interval. Transfer the interval back to the pro-etale site by
[lem-exc-comparison-tor-interval]. Exact inverse image preserves the cohomological interval, and
inverse-image strata and their pulled-back finite constant trivializations show constructibility.
These bounds hold for every $n$ and every $U$; vanishing is local, so they hold globally, with the
shift moving both bounds by $-2$. Hence both functors preserve the full tower subcategories
[sk-def-sp-normalized-towers], and the same Hom bijection restricts to them.
-/
theorem exists_towerP1Adjunction (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ p : Presentation l E S hS, ∃ d : Maps l E p, Nonempty (AdjunctionData l E d) := by
  intro p
  obtain ⟨d, h⟩ := towerP1EtaleOriginComparisonsWithLine l E S hS p
  obtain ⟨k, hk⟩ := towerP1KernelScalarNormalization l E S hS p
  have traces := towerP1_projectionTrace_eq l E p d h k hk
  have scalars (a : Bool) : diagonalScalar l E h a = 𝟙 _ := by
    unfold diagonalScalar
    rw [traces a]
    exact hk.scalar_identity a
  have contract (M : SpTowerShriek.D l E (ProjectiveLine S)) :
      scalarContraction l E p M (𝟙 _) = 𝟙 M := by
    unfold scalarContraction
    rw [show Prod.mkHom (𝟙 M) (𝟙 (unit (ProjectiveLine S)
      (Arings l E (ProjectiveLine S)))) = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id]
  obtain ⟨hf, hg, _⟩ := towerP1TriangleFactorization l E p d h
  have ht : (∀ M : C l E p.classes.base (ProjectiveLine S),
      (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
        𝟙 ((p.F l E).obj M.obj)) ∧
      (∀ K : C l E p.classes.base S,
        eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
          𝟙 ((p.G l E).obj K.obj)) := by
    constructor
    · intro M
      rw [hf M, scalars false, contract, CategoryTheory.Functor.map_id]
    · intro K
      rw [hg K, scalars true, contract]
  let adj : left l E d ⊣ rightRestricted l E d :=
    { unit := etaTransformation l E h.toEtaleOriginComparisons
      counit := epsilonTransformation l E h.toEtaleOriginComparisons
      left_triangle_components M := ObjectProperty.hom_ext _ (ht.1 M)
      right_triangle_components K := ObjectProperty.hom_ext _ (ht.2 K) }
  have finite_data := towerP1_finite_adjunction_assembly l E p d
    h.toEtaleOriginComparisons ht
  choose fm fa hu hc using finite_data
  refine ⟨d, ⟨{
    adjunction := adj
    unit_eq := ?_
    counit_eq := ?_
    finiteMaps := fm
    finiteAdjunction := fa
    finite_unit := hu
    finite_counit := hc
    constructible_restriction := towerP1_uniform_in_presentation l E p }⟩⟩
  · intro M
    rfl
  · intro K
    rfl

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
