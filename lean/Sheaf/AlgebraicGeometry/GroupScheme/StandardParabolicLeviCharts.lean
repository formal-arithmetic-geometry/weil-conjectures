/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.TorusCentralizerBorelIntersection
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.TransverseSubgroupProductOpen
import Mathlib.Topology.Defs.Filter
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Standard parabolic Levi root data and finite Zariski torsor charts

Source: Milne, Algebraic Groups (2017), Notation 21.89, Proposition 21.90,
Theorem 21.91 and Corollary 21.92, pp.453--455; Theorem 17.16, p.356;
Theorem 25.9(a), p.546, and Theorem 13.33(d), pp.265--266; Section 18c, p.390.
(blueprint: lem-sfb-standard-parabolic-levi-charts)

Subgroups and generated subgroups are specified by inclusions and universal properties.
The two multiplication isomorphisms have product underlying schemes; normality gives
exactly the conjugation semidirect-product law. The quotient represents sheafification
of the right-coset presheaf on the recorded fppf site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Standard parabolic geometry for every subset of the simple roots, including the
empty subset and the whole base, in arbitrary characteristic and without a simply
connectedness hypothesis. The character and cocharacter lattices are the actual Hom
groups of the chosen torus. The root datum, positive system and root subgroups in the
hypotheses are precisely those supplied by the recorded Borel-pair and root-subgroup
statements. No quotient or subgroup representative is chosen from an existence theorem.

Source: Milne, Notation 21.89, Proposition 21.90, Theorem 21.91, Corollary 21.92,
pp.453--455; Theorem 17.16, p.356; Theorem 25.9(a), p.546; Theorem 13.33(d),
pp.265--266; Section 18c, p.390.
(blueprint: lem-sfb-standard-parabolic-levi-charts)

Proof plan, following the node step by step:
1. The semisimple group $G$ is reductive by [lem-sfb-reductive-borel-pair-structure]. By
   [lem-sfb-semisimple-roots-span] and [lem-sfb-root-base-rational-integral-spans], $\Delta_0$ is
   a basis of $X\otimes\mathbf Q$. Take its rational dual vectors $\eta_\beta\in X_*\otimes\mathbf
   Q$ and clear denominators in $\sum_{\beta\notin I}\eta_\beta$. This gives an actual cocharacter
   $\lambda:\mathbf G_m\to T$ and an integer $d>0$ with $\langle\beta,\lambda\rangle=0$ on $I$ and
   $d$ on $\Delta_0\setminus I$. If $I=\Delta_0$, take $\lambda=0$ and $d=1$. Writing a root
   $\gamma=\sum c_\beta\beta$, the coefficients have one sign, so $\langle\gamma,\lambda\rangle=0$
   exactly when $\gamma\in\Phi_I$; positive roots outside $\Phi_I$ have strictly positive pairing.
2. Write $M=\mathbf Z I\subseteq X$ and $M^{\mathrm{sat}}=X\cap(M\otimes\mathbf Q)$. The character
   antiduality of [lem-sfb-multiplicative-character-antiduality] describes $D=\bigcap_{\beta\in
   I}\ker\beta$ as the diagonalizable group with character group $X/M$: in $F[X]$ its equations
   are $e_\beta=1$. Its subgroup with character quotient $X/M^{\mathrm{sat}}$ is a torus. Every
   subtorus of $D$ factors through it, because a map from $X/M$ to a free abelian character group
   kills torsion. It is therefore the largest subtorus $T_I$ of
   [lem-sfb-multiplicative-type-largest-subtorus]. Thus $\gamma|_{T_I}=1$ if and only if
   $\gamma\in M\otimes\mathbf Q$, which for roots is equivalent to $\gamma\in\Phi_I$ by uniqueness
   of the integral simple-root coordinates. Also $\lambda$ factors through $T_I$: the map on
   characters kills $M$, hence its saturation, since $\mathbf Z$ is torsion free.
3. Apply [lem-sfb-reductive-torus-fixed-subgroup] to $T_I\subseteq G$. It gives a reductive smooth
   connected closed subgroup $L=C_G(T_I)$. The inclusion $T\subseteq L$ follows because $T$ is
   commutative; it is maximal in $L$ because it was maximal in $G$. The centralizer equation on
   dual numbers says exactly that $\operatorname{Lie}(L)=\operatorname{Lie}(G)^{T_I}$. The
   character weight decomposition of [lem-sfb-reductive-rank-one-reflections] and step 2 therefore
   give $$\operatorname{Lie}(L)=\operatorname{Lie}(T)\oplus\bigoplus_{\gamma\in\Phi_I}\mathfrak
   g_\gamma.$$ Here invariance uses torus characters on all algebras, not their derivatives. For
   $\gamma\in\Phi_I$ the root-subgroup conjugation formula of
   [lem-sfb-reductive-root-subgroup-parametrizations] shows $U_\gamma\subseteq L$. Applying the
   same node to the reductive pair $(L,T)$ identifies its root subgroup with this $U_\gamma$, by
   the stated uniqueness for its tangent space.
4. The character and cocharacter lattices of $(L,T)$ are $X,X_*$ because the torus has not
   changed. For $\gamma\in\Phi_I$ let $T_\gamma$ be the largest subtorus of $\ker\gamma$. Since
   $\gamma|_{T_I}=1$, $T_I\subseteq T_\gamma$, hence $G_\gamma=C_G(T_\gamma)\subseteq L$. The
   rank-one subgroup for $\gamma$ computed inside $L$ is consequently $C_L(T_\gamma)=G_\gamma$.
   The rank-one construction and uniqueness in [lem-sfb-reductive-rank-one-reflections], applied
   in both groups, give the same cocharacter $\gamma^\vee$: it is the diagonal-torus map of the
   same rank-one $\operatorname{SL}_2$ homomorphism. This proves the entire asserted root datum,
   including the ambient coroots, rather than merely equality of root sets.
5. By [lem-sfb-torus-centralizer-borel-intersection], $B_I=B_0\cap L$ is a Borel subgroup of $L$.
   Its tangent space is the intersection of the two tangent spaces (evaluate their fibre product
   on dual numbers). By [lem-sfb-borel-opposite-root-dichotomy] and step 3 its positive roots are
   exactly $\Phi_I\cap\Phi_0^+$. Their simple-root base is $I$: each of these positive roots has
   nonnegative integral coefficients supported in $I$, and the elements of $I$ are linearly
   independent and cannot be sums of two positive roots. Thus the simple-root generation statement
   of [lem-sfb-simple-root-generation-mixed-commutation] applies to $L$ with this base.
6. Apply [lem-sfb-cocharacter-limit-smooth-structure] to $\lambda$ and denote its groups by
   $P_\lambda,U_\lambda,Z_\lambda$. They are smooth connected closed subgroups and
   $P_\lambda=U_\lambda\rtimes Z_\lambda$. Since $\lambda$ factors through $T_I$, $L\subseteq
   Z_\lambda$. By the cocharacter tangent formula, step 1 and
   [lem-sfb-reductive-rank-one-reflections], $\operatorname{Lie}(Z_\lambda)$ is spanned by
   $\operatorname{Lie}(T)$ and the $\mathfrak g_\gamma$ with $\gamma\in\Phi_I$. The smooth
   connected subgroups $T$ and $U_\gamma$ lie in $L$ and their tangent spaces span this space.
   Apply [lem-sfb-smooth-subgroup-tangent-generation] in $Z_\lambda$ with closed subgroup $L$. It
   yields $L=Z_\lambda$, as subgroup schemes.
7. Put $S=\Phi_0^+\setminus\Phi_I$. For $\gamma\in S$, the conjugation formula in
   [lem-sfb-reductive-root-subgroup-parametrizations] is
   $\lambda(t)u_\gamma(a)\lambda(t)^{-1}=u_\gamma(t^{\langle\gamma,\lambda\rangle}a)$; its
   exponent is positive. Thus $U_\gamma\subseteq U_\lambda$ as functors on all algebras. For any
   ordering of $S$, multiplication $\prod_{\gamma\in S}U_\gamma\to U_\lambda$ is
   $\lambda$-equivariant. Its differential is the direct sum of the one-dimensional root spaces,
   hence an isomorphism by [lem-sfb-reductive-rank-one-reflections] and the tangent formula of
   [lem-sfb-cocharacter-limit-smooth-structure]. Source and target are smooth connected affine
   schemes with strictly positive integer tangent weights. Apply
   [lem-sfb-positive-weight-equivariant-inverse]; multiplication is an isomorphism. In particular
   $U_\lambda$ is generated by exactly these root subgroups, and $S=\varnothing$ gives
   $U_\lambda=1$.
8. Every positive root has nonnegative pairing with $\lambda$, so its root subgroup is in
   $P_\lambda$ by the same explicit extension formula; $T\subseteq Z_\lambda$. By
   [lem-sfb-borel-root-product-coordinates] and the decomposition $B_0=R_u(B_0)\rtimes T$ in
   [lem-sfb-reductive-borel-pair-structure], this proves $B_0\subseteq P_\lambda$. Order the
   positive roots outside $\Phi_I$ first, followed by those inside. Apply the root-product node in
   $G$ and in the reductive group $L$ with Borel $B_I$. Together with step 7 these product
   coordinates identify $U_\lambda\times_F B_I\to B_0$ with an isomorphism of schemes. Since
   $U_\lambda$ is normal in $P_\lambda$ and $B_I\subseteq L$, its group law is the displayed
   conjugation semidirect-product law. Hence $B_0=U_\lambda\rtimes B_I$.
9. Let $K$ be any closed subgroup containing $B_0$ and every $U_{-\beta}$ for $\beta\in I$. It
   contains $T$ and $U_{\pm\beta}$ for $\beta\in I$, so $K\cap L=L$ by
   [lem-sfb-simple-root-generation-mixed-commutation] applied to $(L,T,B_I)$. It also contains
   $U_\lambda$ by step 8. Therefore the isomorphism $U_\lambda\rtimes L\simeq P_\lambda$ of
   [lem-sfb-cocharacter-limit-smooth-structure] factors through $K$. Conversely $P_\lambda$
   contains $B_0$ and each $U_{-\beta}$ for $\beta\in I$ (the latter lies in $L$ by step 3). This
   is precisely the universal property of the closed subgroup generated in the question, so
   $P_I=P_\lambda$. In particular $P_I$ is smooth and connected.
10. The group $U_\lambda$ is smooth connected normal and unipotent by
   [lem-sfb-cocharacter-limit-smooth-structure]. To show it is the full unipotent radical, let $N$
   be any smooth connected normal unipotent subgroup of $P_I$. The projection
   $f:P_I=U_\lambda\rtimes L\to L$ is faithfully flat: factor it by
   [lem-sfb-affine-homomorphism-flat-image]; its closed image is all of $L$ because $f$ has the
   section $L\hookrightarrow P_I$. Factor $f|_N$ by the same node. By
   [lem-sfb-unipotent-normal-quotient-image], its closed image in $L$ is smooth connected normal
   and unipotent. Since $L$ is reductive, that image is trivial. Thus $N\subseteq\ker
   f=U_\lambda$. This proves $R_I=U_\lambda$, so steps 6--8 give both claimed semidirect products
   and the claimed radical generators.
11. Apply [lem-sfb-homogeneous-orbit-quotient-geometry] to the smooth connected affine group $G$
   and closed subgroup $P_I$. It represents the fppf right-coset sheaf by a separated finite-type
   $F$-scheme $Q=G/P_I$, and gives $G\times_FP_I\simeq G\times_QG$ by $(g,p)\mapsto(g,gp)$ and a
   faithfully flat quotient map $q$. The quotient construction of
   [lem-sfb-algebraic-group-homogeneous-quotient] also gives finite presentation of this map. Its
   coset-fibre and local-lifting characterization identifies its representing scheme canonically
   with $Q$ (it is itself an fppf cover, so the local lifts are fppf). Thus $q$ is faithfully flat
   of finite presentation and is the asserted right $P_I$-torsor.
12. The inclusion $B_0\subseteq P_I$ gives $a:G/B_0\to Q$ by the quotient sheaf universal
   property, sending $gB_0$ to $gP_I$. It is universally surjective: after every base change, any
   point of $Q$ lifts fppf locally to $G$ and hence to $G/B_0$. By
   [lem-sfb-reductive-borel-pair-structure], $G/B_0$ is proper over $F$. For any $F$-scheme $S$
   and closed subset $Z\subseteq Q\times_FS$, its inverse image under $a_S$ is closed in
   $(G/B_0)\times_FS$ and has the same image in $S$ as $Z$, by surjectivity. That image is closed
   by properness of $G/B_0$. Thus $Q\to\operatorname{Spec}F$ is universally closed; it is
   separated and finite type by step 11. The definition [def-weil-proper-morphism] therefore makes
   $Q$ proper.
13. Put $H=U_{-\lambda}$, using [lem-sfb-cocharacter-limit-smooth-structure] for $-\lambda$. We
   verify the hypotheses of [lem-sfb-transverse-subgroup-product-open] for $H,P_\lambda\subseteq
   G$. Their tangent spaces are respectively the negative and nonnegative $\lambda$-weight spaces,
   and hence sum directly to $\operatorname{Lie}(G)$. Their intersection is trivial on every
   algebra: for $g\in H(A)\cap P_\lambda(A)$, the orbit $\lambda(t)g\lambda(t)^{-1}$ extends at
   $0$ and at infinity, and its value at infinity is $1$. For each affine coordinate of $G$, its
   Laurent polynomial lies in $A[t]\cap A[t^{-1}]=A$. Thus the orbit is constant, equal to $1$,
   whence $g=1$. Both groups are smooth closed subgroups, so the transverse-product node makes
   $m:H\times_F P_I\to G$, $(h,p)\mapsto hp$, an open immersion.
14. Consider $j:H\to Q$, $h\mapsto q(h)$. The torsor identity in
   [lem-sfb-homogeneous-orbit-quotient-geometry] identifies its base change along $q:G\to Q$ with
   $H\times_FP_I\to G$, $(h,p)\mapsto hp$: the fibre product is parametrized by $(h,hp)$. This is
   the open immersion of step 13. Since $q$ is a surjective flat finitely presented cover, the
   open-immersion descent statement of [lem-sfb-representable-fppf-etale-open-descent] applies
   (schemes are algebraic spaces). It follows that $j$ is an open immersion. Write $C=j(H)$. Its
   inverse $C\to H$, followed by $H\hookrightarrow G$, is a regular section $s:C\to G$ of $q$. The
   open $C$ contains the identity coset.
15. For every $g\in G(F)$, left translation gives the open $gC\subseteq Q$ and the section
   $x\mapsto g\,s(g^{-1}x)$. Every closed point of $Q$ is an $F$-point by
   [lem-weil-pbc-closed-point-residue-field-base], and every such point lifts to $g\in G(F)$ by
   [lem-sfb-homogeneous-orbit-quotient-geometry]. It then lies in $gC$. By
   [lem-sc-lft-over-field-jacobson-space], a nonempty closed complement would contain a closed
   point; thus these translates cover $Q$. Finally $Q$ is quasi-compact because its structure
   morphism is finite type [def-weil-finite-type-morphism]. The definition
   [def-weil-pbc-quasi-compact-scheme] supplies a finite subcover. All constructions allow empty
   root sets and $\lambda=0$, so no rank, characteristic or simply connectedness restriction was
   added.
-/
theorem standard_parabolic_levi_charts
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (D : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : D.Base) (hred : D.IsReduced)
    (hroot : ∀ α : Φ, D.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (D.toLinearMap χ ν))
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (U : Φ → Grp (Over (Spec (.of F)))) (iU : ∀ α : Φ, U α ⟶ G)
    (hU : ∀ α : Φ,
      IsClosedSubgroupScheme (iU α).hom.hom ∧ Smooth (U α).X.hom ∧
      ConnectedSpace (U α).X.left ∧ @TorusCharacterTangent.IsStable F _ T G aG _ (iU α) ∧
      (GrpObj.differential (iU α).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)
    (I : Set Φ) (hI : I ⊆ (b.support : Set Φ)) :
    ∃ (TI L BI P R : Grp (Over (Spec (.of F))))
      (s : TI ⟶ T) (iL : L ⟶ G) (tL : T ⟶ L)
      (bB : BI ⟶ B) (bL : BI ⟶ L) (tBI : T ⟶ BI)
      (iP : P ⟶ G) (bP : B ⟶ P) (lP : L ⟶ P) (rP : R ⟶ P) (rB : R ⟶ B),
      IsClosedSubgroupScheme s.hom.hom ∧ MultiplicativeType.IsTorus TI ∧
      (∀ α ∈ I, s ≫ α.val.toMul = 1) ∧
      (∀ (S : Grp (Over (Spec (.of F)))) (k : S ⟶ T),
        IsClosedSubgroupScheme k.hom.hom → MultiplicativeType.IsTorus S →
        (∀ α ∈ I, k ≫ α.val.toMul = 1) → ∃ f : S ⟶ TI, f ≫ s = k) ∧
      IsClosedSubgroupScheme iL.hom.hom ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A],
        ReductiveTorusCentralizer.centralizerPoints (s ≫ iT) A =
          Set.range (fun x : StandardGroupSchemes.affine F A ⟶ L.X ↦ x ≫ iL.hom.hom)) ∧
      ReductiveTorusCentralizer.IsReductive L ∧
      tL ≫ iL = iT ∧ ReductiveTorusCentralizer.IsMaximalTorus tL ∧
      IsPullback bB.hom.hom bL.hom.hom iB.hom.hom iL.hom.hom ∧
      IsBorelGroupScheme bL.hom.hom ∧ tBI ≫ bB = j ∧ tBI ≫ bL = tL ∧
      (∃ (aL : ModObj T.X L.X) (aBI : ModObj T.X BI.X)
        (DL : RootDatum {α : Φ // D.root α ∈ Submodule.span ℤ (D.root '' I)}
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T))),
        aL.smul = (tL.hom.hom ⊗ₘ 𝟙 L.X) ≫ GrpObj.conj L.X ∧
        aBI.smul = (tBI.hom.hom ⊗ₘ 𝟙 BI.X) ≫ GrpObj.conj BI.X ∧
        DL.toLinearMap = D.toLinearMap ∧
        (∀ α, DL.root α = D.root α.val ∧ DL.coroot α = D.coroot α.val) ∧
        (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          (χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T L aL χ.toMul ≠ ⊥) ↔
            χ ∈ Φ ∧ χ ∈ Submodule.span ℤ (D.root '' I)) ∧
        (∀ α : Φ,
          (@TorusCharacterTangent.weightSpace F _ T BI aBI α.val.toMul ≠ ⊥) ↔
            D.root α ∈ Submodule.span ℤ (D.root '' I) ∧ b.IsPos α)) ∧
      IsClosedSubgroupScheme iP.hom.hom ∧ bP ≫ iP = iB ∧ lP ≫ iP = iL ∧
      (∀ α : Φ, (∃ β ∈ I, α.val = -β.val) → ∃ f : U α ⟶ P, f ≫ iP = iU α) ∧
      (∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
        IsClosedSubgroupScheme k.hom.hom → (∃ f : B ⟶ K, f ≫ k = iB) →
        (∀ α : Φ, (∃ β ∈ I, α.val = -β.val) → ∃ f : U α ⟶ K, f ≫ k = iU α) →
        ∃ f : P ⟶ K, f ≫ k = iP) ∧
      Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧
      IsClosedSubgroupScheme rP.hom.hom ∧ IsNormalSubgroupScheme rP.hom.hom ∧
      Smooth R.X.hom ∧ ConnectedSpace R.X.left ∧ SolvableGroupStructure.IsUnipotent R ∧
      (∀ (N : Grp (Over (Spec (.of F)))) (n : N ⟶ P),
        IsClosedSubgroupScheme n.hom.hom → IsNormalSubgroupScheme n.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ R, f ≫ rP = n) ∧
      (∀ α : Φ, b.IsPos α → D.root α ∉ Submodule.span ℤ (D.root '' I) →
        ∃ f : U α ⟶ R, f ≫ rP ≫ iP = iU α) ∧
      (∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
        IsClosedSubgroupScheme k.hom.hom →
        (∀ α : Φ, b.IsPos α → D.root α ∉ Submodule.span ℤ (D.root '' I) →
          ∃ f : U α ⟶ K, f ≫ k = iU α) →
        ∃ f : R ⟶ K, f ≫ k = rP ≫ iP) ∧
      rB ≫ bP = rP ∧
      IsIso ((fst R.X L.X ≫ rP.hom.hom) * (snd R.X L.X ≫ lP.hom.hom)) ∧
      IsIso ((fst R.X BI.X ≫ rB.hom.hom) * (snd R.X BI.X ≫ bB.hom.hom)) ∧
      ∃ (Q : Over (Spec (.of F))) (q : G.X ⟶ Q),
        IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
        Flat q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left ∧
        QuasiCompact q.left ∧ QuasiSeparated q.left ∧
        (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom)) ≫ q = fst G.X P.X ≫ q ∧
        IsPullback (fst G.X P.X)
          (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom)) q q ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q) ∧
        (∃ ηq : coequalizer (yoneda.map (fst G.X P.X))
            (yoneda.map (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom))) ⟶ yoneda.obj Q,
          coequalizer.π _ _ ≫ ηq = yoneda.map q ∧
          ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
            Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) ∧
        ∃ (m : ℕ) (V : Fin m → Over (Spec (.of F)))
          (v : ∀ k, V k ⟶ Q) (σ : ∀ k, V k ⟶ G.X),
          (∀ k, IsOpenImmersion (v k).left ∧ σ k ≫ q = v k) ∧
          ∀ x : Q.left, ∃ k, x ∈ Set.range (v k).left := by
  sorry

end AlgebraicGeometry
