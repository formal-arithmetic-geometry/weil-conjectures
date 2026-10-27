/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N5, G7
-/
module

public import Sheaf.Paper.IntegrationExponentTransposeData
import Sheaf.Paper.IntegrationProjectiveExponentSquare
import Sheaf.Paper.IntegrationAffineExponentTransport
import Sheaf.Paper.IntegrationCoefficientProjectionNaturality
import Sheaf.Paper.VectorIntegrationSiteComparison

/-! # Exponent transport of integration and its bounded transposes

Source: main-20261015, thm-amb-vector-bundle-purity.proof.md, paragraphs 1--2;
Stacks Tags 03PK, 099R and 0B65.
(blueprint: lem-pur-integration-exponent-transpose-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private theorem decomposition_of_square {C : Type*} [Category C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {Lr Ls U Rr Rs : C} (e : Ls ⟶ Lr) (q : Rs ⟶ Rr)
    (br : (Lr ⊞ U) ≅ Rr) (bs : (Ls ⊞ U) ≅ Rs)
    (h : IntegrationDecompositionSquare e q br bs) :
    IntegrationDecompositionEquations e q br bs := by
  change bs.hom ≫ q = biprod.map e (𝟙 U) ≫ br.hom at h
  have hi : q ≫ br.inv = bs.inv ≫ biprod.map e (𝟙 U) := by
    calc
      q ≫ br.inv = bs.inv ≫ (bs.hom ≫ q) ≫ br.inv := by simp
      _ = bs.inv ≫ (biprod.map e (𝟙 U) ≫ br.hom) ≫ br.inv := by rw [h]
      _ = bs.inv ≫ biprod.map e (𝟙 U) := by simp
  refine ⟨h, hi, ?_⟩
  rw [← Category.assoc, hi]
  simp only [Category.assoc, biprod.map_snd, Category.comp_id]

private theorem inverse_transition {C : Type*} [Category C]
    {X Y Z : C} (i : X ≅ Y) (e : Y ≅ Z) (e' : X ≅ Z)
    (h : i.hom ≫ e.hom = e'.hom) : e.inv ≫ i.inv = e'.inv := by
  have hi : i ≪≫ e = e' := by
    apply Iso.ext
    exact h
  exact congrArg (fun z : X ≅ Z ↦ z.inv) hi

private theorem projective_equations (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    IntegrationProjectiveEquations l E n S hS r s hrs hr hs := by
  obtain ⟨he, br, bs, hbr, hbs, hp⟩ :=
    integrationProjectiveExponentSquare l E n S hS r s hrs hr hs
  exact ⟨decomposition_of_square _ _ _ _ he,
    br, bs, hbr, hbs, decomposition_of_square _ _ _ _ hp⟩

private theorem trace_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y U : C} {X' Y' : D}
    (i : X ⟶ Y) (j : X' ⟶ Y') (b : F.obj Y ⟶ Y') (b' : F.obj X ⟶ X')
    (t : Y ⟶ U) (t' : X ⟶ U) (u : Y' ⟶ F.obj U) (u' : X' ⟶ F.obj U)
    (hn : F.map i ≫ b = b' ≫ j) (ht : b ≫ u = F.map t)
    (ht' : b' ≫ u' = F.map t') (hp : j ≫ u = u') :
    F.map (i ≫ t) = F.map t' := by
  rw [F.map_comp, ← ht, ← ht', ← Category.assoc, hn, Category.assoc, hp]

private theorem tensor_trace_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D ⥤ D) {X Y : C} {U V W Z : D}
    (i : X ⟶ Y) (j : U ⟶ V) (tr : V ⟶ W) (ts : U ⟶ W)
    (p : F.obj Y ⟶ T.obj V) (q : F.obj X ⟶ T.obj U) (u : T.obj W ⟶ Z)
    (hp : F.map i ≫ p = q ≫ T.map j) (ht : j ≫ tr = ts) :
    F.map i ≫ (p ≫ T.map tr ≫ u) = q ≫ T.map ts ≫ u := by
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← T.map_comp_assoc, ht]

private theorem vector_equations (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf)
    [F.IsFiniteLocallyFreeOfRank d]
    (ht : IntegrationTraceComparison l E n S hS d F) :
    IntegrationVectorEquations l E n S hS r s hrs hr hs d F := by
  let A := Scheme.finiteTateCoefficient l E n
  let i := integrationVectorTransition l E n S hS r s hrs hr hs d F
  have hp : (integrationProLower A S d F).map ((comparison A _).map i.hom) ≫
      vectorIntegration l E n S r hr d F hS = vectorIntegration l E n S s hs d F hS := by
    exact vectorExponentIndependence l E n S hS r s hrs hr hs d F
  refine ⟨?_, hp⟩
  have hn : (comparison A S).map ((integrationLower A S d F).map i.hom) ≫
      (vectorSite l E n S r hr d F hS).inv =
      (vectorSite l E n S s hs d F hS).inv ≫
        (integrationProLower A S d F).map ((comparison A _).map i.hom) := by
    let b : (⟨Etale.vectorIntegrationCoefficient A (l ^ (s + 1)) hs S d F,
        vectorCoefficient_plus l E n S s hs d F hS⟩ : DerivedCategory.Plus _) ⟶
      ⟨Etale.vectorIntegrationCoefficient A (l ^ (r + 1)) hr S d F,
        vectorCoefficient_plus l E n S r hr d F hS⟩ := ObjectProperty.homMk i.hom
    unfold vectorSite
    with_unfolding_all
      exact (compactSupportSiteComparison A
        (Etale.vectorBundlePurityCompactification S d F)).inv.naturality b
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) (X := S) _
      (Etale.ordinaryFiniteUnit A S) ⟨0, inferInstance⟩).1
  exact trace_transport (comparison A S)
    ((integrationLower A S d F).map i.hom)
    ((integrationProLower A S d F).map ((comparison A _).map i.hom))
    (vectorSite l E n S r hr d F hS).inv (vectorSite l E n S s hs d F hS).inv
    _ _ _ _ hn (ht r hr) (ht s hs) hp

private theorem transpose_data (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf)
    [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K) :
    Nonempty (IntegrationTransposeData (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hr S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F K
      (vectorIntegration l E n S r hr d F hS) (vectorSite l E n S r hr d F hS)) := by
  obtain ⟨D⟩ := vectorTensorComparison l E n S hS r hr d F K hK
  have := D.ordinary_purity
  let etaE := asIso ((Etale.vectorBundlePurityAdjunction
    (Scheme.finiteTateCoefficient l E n) S d F).homEquiv _ K D.ae)
  have hplus : DerivedCategory.TStructure.t.plus K := hK.1.1.1
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K hplus
  have : IsIso (boundedSiteRho (Scheme.finiteTateCoefficient l E n)
      (genericVectorExceptional (Scheme.finiteTateCoefficient l E n) S d F) K) := by
    unfold boundedSiteRho
    infer_instance
  let rho := asIso (boundedSiteRho (Scheme.finiteTateCoefficient l E n)
    (genericVectorExceptional (Scheme.finiteTateCoefficient l E n) S d F) K)
  let etaP := (comparison (Scheme.finiteTateCoefficient l E n) _).mapIso etaE ≪≫ rho
  exact ⟨{
    data := D
    right_plus := DerivedCategory.TStructure.t.plus.prop_of_iso etaE D.hM
    etaE := etaE
    rho := rho
    etaP := etaP
    etaE_formula := rfl
    rho_formula := rfl
    etaP_formula := (eq_of_heq D.transpose_square).symm
    transpose := rfl
    inverse := rfl }⟩

private theorem tensor_equations (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf)
    [F.IsFiniteLocallyFreeOfRank d]
    (hv : IntegrationVectorEquations l E n S hS r s hrs hr hs d F)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K) :
    IntegrationTensorEquations l E n S hS r s hrs hr hs d F K := by
  obtain ⟨D⟩ := transpose_data l E n S hS r hr d F K hK
  obtain ⟨D'⟩ := transpose_data l E n S hS s hs d F K hK
  let i := integrationTensorTransition l E n S hS r s hrs hr hs d F K
  obtain ⟨hpe, hpp⟩ :=
    integrationCoefficientProjectionNaturality l E n S hS r s hrs hr hs d F K D D'
  have ha : (integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map i.hom ≫
      D.data.ae = D'.data.ae := by
    have hf := eq_of_heq D.data.ordinary_formula
    have hf' := eq_of_heq D'.data.ordinary_formula
    unfold ordinaryTensorIntegrate at hf hf'
    exact (congrArg (fun a ↦
      (integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map i.hom ≫ a) hf).trans
        ((tensor_trace_transport
          (integrationLower (Scheme.finiteTateCoefficient l E n) S d F)
          ((Etale.derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S).obj K)
          i.hom ((integrationLower (Scheme.finiteTateCoefficient l E n) S d F).map
            (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom)
          _ _ D.data.pe.hom D'.data.pe.hom _ hpe hv.1).trans hf'.symm)
  have hb : (integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
      ((comparison (Scheme.finiteTateCoefficient l E n) _).map i.hom) ≫
        D.data.ap = D'.data.ap := by
    have hf := eq_of_heq D.data.pro_formula
    have hf' := eq_of_heq D'.data.pro_formula
    unfold proTensorIntegrate at hf hf'
    exact (congrArg (fun a ↦
      (integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
        ((comparison (Scheme.finiteTateCoefficient l E n) _).map i.hom) ≫ a) hf).trans
        ((tensor_trace_transport
          (integrationProLower (Scheme.finiteTateCoefficient l E n) S d F)
          ((derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S).obj
            ((comparison (Scheme.finiteTateCoefficient l E n) S).obj K))
          ((comparison (Scheme.finiteTateCoefficient l E n) _).map i.hom)
          ((integrationProLower (Scheme.finiteTateCoefficient l E n) S d F).map
            ((comparison (Scheme.finiteTateCoefficient l E n) _).map
              (integrationVectorTransition l E n S hS r s hrs hr hs d F).hom))
          _ _ D.data.pp.hom D'.data.pp.hom _ hpp hv.2).trans hf'.symm)
  have he : i.hom ≫ D.etaE.hom = D'.etaE.hom := by
    rw [D.etaE_formula, D'.etaE_formula]
    exact ((Etale.vectorBundlePurityAdjunction
      (Scheme.finiteTateCoefficient l E n) S d F).homEquiv_naturality_left
      i.hom D.data.ae).symm.trans
        (congrArg ((Etale.vectorBundlePurityAdjunction
          (Scheme.finiteTateCoefficient l E n) S d F).homEquiv _ K) ha)
  have hp : (comparison (Scheme.finiteTateCoefficient l E n) _).map i.hom ≫
      D.etaP.hom = D'.etaP.hom := by
    rw [D.transpose, D'.transpose, ← Category.assoc, ← Functor.map_comp, he,
      D.rho_formula, D'.rho_formula]
  exact ⟨D, D', ha, hb, he, hp,
    inverse_transition i D.etaE D'.etaE he,
    inverse_transition ((comparison (Scheme.finiteTateCoefficient l E n) _).mapIso i)
      D.etaP D'.etaP hp⟩

/-- Exponent transport of actual normalized integration and its bounded transposes.
Source: main-20261015, thm-amb-vector-bundle-purity.proof.md, paragraphs 1--2;
Stacks Tags 03PK, 099R and 0B65.
(blueprint: lem-pur-integration-exponent-transpose-transport).

Proof (the accepted DAG split):

1. The finite-type hypothesis makes $S$ Noetherian by [lem-weil-pbc-finite-type-over-
noetherian], applied over the spectrum of the field $k$. Use the projective completion of [lem-
amb-vector-projective-completion]; its middle scheme and $V$ are Noetherian and finite type over
$k$, even when $S$ is not separated over $k$. By [lem-cbc-compactification-geometry-fibre-
bound], applied over $\operatorname{Spec}k$ (dimension zero), the middle scheme has finite
topological dimension, so choose a nonnegative integer bound $D$. By [lem-asd-finite-etale-
twist-line], $W_r=L_{V,r}^{\otimes d}[2d]$ is a shifted locally constant finite rank-one
$A$-module. If $K$ has cohomology in $[a,b]$, exact inverse image [prop-weil-pbc-inverse-image-
modules-exact] and exact tensor by this line give $J_r$ cohomology in $[a-2d,b-2d]$. In
particular $J_r$ is an ordinary bounded etale witness; $W_r$ is bounded constructible and $K$
has the finite Tor amplitude stipulated in the statement.

2. Let $P_r^e:K\otimes F_\pi^eW_r\to F_\pi^eJ_r$ and $P_r^p:C_SK\otimes F_\pi^pC_VW_r\to
F_\pi^pC_VJ_r$ be the coefficient-first projections. [lem-weil-finite-compact-projection-
formula] makes both invertible: $W_r$ is bounded constructible and $K$ is bounded constructible
with finite Tor amplitude. Apply [lem-pur-projection-comparison-etale-origin] to $f=\pi$,
$M=W_r$, $H=K$, at the projective completion of Step 1. It assumes no absolute separatedness.
Its comparison $C_M:F_\pi^pC_VM\to C_SF_\pi^eM$ is the ambient comparison whose inverse, by the
specified composite of [def-sf-compact-support-site-comparison-construction], is exactly
$B_{\pi,M}=R\overline\pi_{p,*}(e_j)\beta_{\overline\pi,j_!M}$. Thus $C_M=B_{\pi,M}^{-1}$.
Substitute this in the cited projection equation, compose with $B_{\pi,M\otimes\pi^*K}$ on the
left and $B_{\pi,M}\otimes1$ on the right, and cancel the adjacent inverses. This gives the
right-coefficient projection comparison. Conjugating by the two natural signed tensor symmetries
specified in [def-pur-finite-site-tensor-projection] gives, with the source tensorators
understood, $B_{\pi,J_r}C_S(P_r^e)=P_r^p(1\otimes B_{\pi,W_r})$. This is an equality of the
actual projection arrows, not a counit or smooth-purity theorem.

3. Invert the projection equation of Step 2 to get $(P_r^p)^{-1}B_{\pi,J_r}=(1\otimes
B_{\pi,W_r})C_S((P_r^e)^{-1})$. Multiply on the left by the comparison right unitor after
$1\otimes t_{\pi,r}^p$. The assumed equality $t_{\pi,r}^pB_{\pi,W_r}=C_S(t_{\pi,r}^e)$ and the
unitor normalization in [def-pur-finite-site-tensor-projection] turn the resulting composite
into $C_S$ of the right unitor after $(1\otimes t_{\pi,r}^e)(P_r^e)^{-1}$. This is exactly
$a_{C_SK,r}^pB_{\pi,J_r}=C_S(a_{K,r}^e)$, by the defining formulas for the two integration
arrows.

4. Apply [thm-amb-vector-bundle-purity] over the Noetherian base $S$, with the same finite
coefficient ring and the ordinary integration of the statement. It says that the ordinary
adjunct $\eta_{K,r}^e:J_r\to\pi^{\times,e}K$ is invertible, for this exact coefficient-first
inverse-projection trace. Hence $\pi^{\times,e}K$ is bounded, since it is isomorphic to the
bounded $J_r$ of Step 1. Now [lem-pur-bounded-site-adjunction-transpose] applies with the
projective compactification, the dimension bound $D$ of Step 1, $J=J_r$, and $K$. Its Hom-chain
is the one in [def-pur-bounded-site-transpose-arrows]; in particular its right comparison is the
stated comparison-unit map $\rho_K$, not a freely chosen right-adjoint isomorphism. Substituting
Step 3 in that lemma's last equation gives $\eta_{C_SK,r}^p=\rho_K C_V(\eta_{K,r}^e)$. This uses
bounded-below etale witnesses for both $J_r$ and $\pi^{\times,e}K$.

5. The inverse of the last composite is $C_V((\eta_{K,r}^e)^{-1})\rho_K^{-1}$: multiplying in
either order cancels the two adjacent inverse pairs. Thus the pro-etale transpose is invertible
and its inverse is the transported ordinary inverse. The normalization of [def-pur-vector-
purity-normalization] determines the ordinary inverse-purity family by the very inverse-
projection/counit equation used in Step 3; the Hom bijection makes its component unique. If its
source is written twist-first, insert the canonical signed symmetry of [lem-kun-tensor-sym].
Consequently the displayed maps give the integration-normalized purity identification, rather
than an unspecified isomorphism between the same objects.

6. Fix $s\ge r$ with $\ell^rA=0$. By [lem-amb-finite-tate-site-descent] the root-power
transition $e_{T,sr}:L_{T,s}\to L_{T,r}$ is invertible, compatible with pullback and tensor
powers, and satisfies $\tau_{T,r}C_T(e_{T,sr})=\tau_{T,s}$. The supported Cartier class of [lem-
amb-cartier-kummer-map], applied to the infinity divisor of $P=\mathbf P^1_T$, is independent of
the chosen killing exponent; the same is true of its composite with $A_P\to i_*A_T$. Thus in the
common pro-etale Tate coordinates the actual Chern arrows $h_s^p,h_r^p$ agree. The other
component $u^p$ is the adjunction unit with the line pullback comparison, so is unchanged under
$e_{T,sr}$ by naturality of that unit. With $b^p=[u^p,h^p]$ of [def-pur-supported-projective-
site-arrows], equality of both components proves equality of the projective decomposition maps.
No assertion about a trace is inferred merely from an isomorphism of its source objects.

7. Write $Q_{sr}=Rq_*(e_{P,sr}[2])$ and $D_{sr}=e_{T,sr}[2]\oplus1$. On the ordinary site the
analogous decomposition identity is $Q_{sr}b_s^e=b_r^eD_{sr}$. Indeed [lem-pur-p1-kummer-trace-
site-transport] identifies each of its two compared sides with the pro-etale decomposition
equality of Step 6, while naturality of the proper comparison moves $Q_{sr}$ across it. Full
faithfulness in [thm-weil-pbc-site-comparison] reflects equality here: the source is a bounded
sum of two shifted sheaves and the target is bounded by its projective decomposition. All
decompositions are invertible. Rearranging gives $(b_r^e)^{-1}Q_{sr}=D_{sr}(b_s^e)^{-1}$, and
second projection yields $t_{q,r}^eQ_{sr}=t_{q,s}^e$, since
$\operatorname{pr}_2D_{sr}=\operatorname{pr}_2$. The same cancellation on the pro-etale side
proves the equality of its actual inverse traces.

8. The affine trace is the projective trace precomposed with $Rq_*$ of the open counit on the
twist. The last assertion of [lem-pur-p1-kummer-trace-site-transport] identifies these actual
counit composites on the two sites. Naturality of that counit in the coefficient map
$e_{P,sr}[2]$ gives a commutative square between their sources; composing this square with the
trace equality of Step 7 proves that the restricted affine-line traces agree at $s$ and $r$. For
coefficient inputs, naturality of each canonical projection gives $F(1\otimes e)P_s=P_r(1\otimes
F(e))$. Both projections are invertible on the finite-Tor inputs by [lem-weil-finite-compact-
projection-formula]. Cancelling their inverses and using the affine trace equality proves
equality of the inverse-projection coefficient arrows as well.

9. Use the recursive ordered integration of [def-pur-proetale-ordered-integration]. Induct on
tower length $d$. At $d=0$ the coefficient, transition and counit are identities. For the
induction step the ordered counit is the previous counit composed with the previous left functor
applied to the last affine-line coefficient counit. The last coefficient counits agree by Step
8, and the previous counits agree by induction. Applying a functor preserves their equality and
then composing proves equality at length $d+1$. The compact-support compositors and Tate
reassociations are natural in the coefficient maps and independent of the killing exponent, so
inserting those same source identifications preserves this equality. This proves equality of the
actual ordered affine traces, on both sites, with no change of coordinate order or omitted
permutation sign.

10. Use the same projective completion $V\xrightarrow{j}\overline V\xrightarrow{\overline\pi}S$
as in Step 1, supplied by [lem-amb-vector-projective-completion]; its chart identifications
commute with restriction and changes of linear frame. The line comparison needed by [lem-pur-
affine-tower-integration-site-transport] is supplied by [lem-pur-p1-kummer-trace-site-
transport]. Thus the former gives invertible ordered traces, compatibility with open restriction
and projective completion, and their ordinary comparison at each exponent. [lem-pur-compact-
support-site-coherence] supplies the refinement, composition and restriction identities required
by the frame-descent lemma. The frame prefix of [def-pur-proetale-frame-integration] consists of
inverse-frame exchange, Tate pullback and compact-support composition comparisons. These are
natural in the line coefficient, so Step 9 gives equal local integrations in the same frame
after the root transition. Apply [lem-pur-vector-frame-integration-site-descent]: the ordinary
and pro-etale compact-support sources are concentrated in degree zero, the frame traces glue
uniquely, and the result is independent of cover and frames, also on non-affine overlaps. The
equality part of [lem-pur-degree-zero-derived-map-gluing] therefore turns these local equalities
into equality of the global vector traces at $s$ and $r$. This checks derived concentration
before testing equality on an open cover. For ordinary integration it is the unique map with
these local traces; the pro-etale glued map is the prescribed independently constructed map.

11. Put $i_{sr}=1_{\pi^*K}\otimes e_{V,sr}^{\otimes d}[2d]:J_s\to J_r$. Projection naturality
and the global trace equality of Step 10 give $a_{K,s}^e=a_{K,r}^eF_\pi^e(i_{sr})$ and
$a_{C_SK,s}^p=a_{C_SK,r}^pF_\pi^p(C_Vi_{sr})$. Naturality of adjunction transposition in the
source, with the fixed ordinary compact-support adjunction [thm-amb-etale-exceptional-adjoint],
yields $\eta_{K,s}^e=\eta_{K,r}^e i_{sr}$. The bounded transpose identity and its naturality
from [lem-pur-bounded-site-adjunction-transpose] give $\eta_{C_SK,s}^p=\eta_{C_SK,r}^p
C_Vi_{sr}$. Therefore $(\eta_{K,s}^e)^{-1}=i_{sr}^{-1}(\eta_{K,r}^e)^{-1}$, and the pro-etale
inverse has the identical formula after comparison. Naturality of $B$ and the fact that $\rho_K$
has no exponent parameter identify every comparison square at the two exponents. These are
equalities of arrows after the canonical root transition, as claimed.

12. At rank zero the projective compactification is the identity by [lem-amb-vector-projective-
completion], and the recursive integration starts at the identity; the zero tensor power has
identity exponent transition. All displayed projection and transpose formulas reduce to the unit
constraints and the identity adjunction. For empty $S$, also $V$ and its projective completion
are empty, all module sheaves are zero, and the unique morphisms satisfy the same identities and
are invertible. Throughout, root sheaves are locally free over their own $\mathbf Z/\ell^r$ and
the extended Tate lines are locally free over $A$ [lem-asd-finite-etale-twist-line]; no flatness
of $A$ over $\mathbf Z/\ell^r$ has been used. The root comparison explicitly permits arbitrary
$n$ [lem-amb-finite-tate-site-descent]. Thus no ramification-index divisibility is introduced,
and Step 4 stays entirely within the bounded etale-origin adjunction.
-/
theorem integrationExponentTransposeTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    IntegrationExponentTransposeConclusion P S aS d F := by
  have : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  have hS : IsUnit (P.coefficients.l : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk S aS x
  refine ⟨hS, ?_⟩
  intro ht r s hrs hr hs
  have hp := projective_equations P.coefficients.l P.extension (P.level - 1)
    S hS r s hrs hr hs
  have ha := integrationAffineExponentTransport P.coefficients.l P.extension (P.level - 1)
    S hS r s hrs hr hs (fun T _ hT ↦
      projective_equations P.coefficients.l P.extension (P.level - 1)
        T hT r s hrs hr hs)
  have hv := vector_equations P.coefficients.l P.extension (P.level - 1)
    S hS r s hrs hr hs d F ht
  exact ⟨hp, ha, hv, tensor_equations P.coefficients.l P.extension (P.level - 1)
    S hS r s hrs hr hs d F hv⟩

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
