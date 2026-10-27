/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.FlagLinearFixedInterfaces
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Torus-fixed flags and a dominant separating one-parameter action

Source: Milne, Algebraic Groups (2017), Theorem 4.27, Theorem 17.9, Section 18c,
Summary 21.41, Lemma 13.51, the paragraphs preceding Proposition 21.70 (p.446),
and the tangent calculation in the proof of Theorem 21.73 (p.447).
(blueprint: lem-sfb-flag-torus-fixed-geometry)

Fixed subschemes are characterized by their algebra-valued points after every
extension. The constant fixed scheme is exhibited as a coproduct of copies of Spec F,
with the prescribed inclusions n_w B. Tangent characters are actual torus characters.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- The smooth projective flag quotient, its finite reduced fixed flags, tangent
weights, and a dominant cocharacter separating the weights of a projective embedding.
Source: Milne, Theorems 4.27 and 17.9; Summary 21.41; Lemma 13.51; paragraphs before
Proposition 21.70, p.446; proof of Theorem 21.73, p.447.
(blueprint: lem-sfb-flag-torus-fixed-geometry)

Proof plan:
1. The quotient and torsor in the hypotheses satisfy the quotient condition of [lem-sfb-borel-
   quotient-proper-geometry]: two lifts have the same image precisely when their ratio lies in
   $B$, and the faithfully flat torsor supplies local lifts. Apply that node with $H=B$. It
   gives that $Q$ is smooth, geometrically integral, proper and Noetherian, and that $\pi$ is
   smooth. In particular $Q$ is connected. Here $B$ is smooth and connected by its Borel
   definition, so this application has no inseparable-stabilizer exception. Uses: lem-sfb-
   reductive-borel-pair-structure, lem-sfb-borel-quotient-proper-geometry.
2. Apply [lem-sfb-chevalley-scheme-line-stabilizer] to $B\subset G$, obtaining $(E,D)$ with
   stabilizer exactly $B$ on every test algebra. The orbit map $g\mapsto gD$ is invariant under
   right $B$. Its values on the torsor kernel pair agree; [lem-weil-pbc-fpqc-representable-
   descent] therefore gives a $G$-equivariant map $i:Q\to\mathbf P(E)$. This is a monomorphism:
   for two test-scheme points with equal images choose common fpqc-local lifts $g,h$ to $G$;
   equality of lines implies $g^{-1}h\in B$, whence equality in $Q$, and descent detects that
   equality globally. Projective space is separated by [lem-weil-pbc-projective-space-proj-
   separated]. Since $Q$ is proper, [lem-weil-pbc-proper-over-separated] makes $i$ proper; [lem-
   pc-proper-monomorphism-closed] makes it a closed immersion. Choosing a basis of nonzero $E$
   identifies its projective space of lines with an ordinary projective space, proving
   projectivity of $Q$. Uses: lem-sfb-chevalley-scheme-line-stabilizer, lem-weil-pbc-fpqc-
   representable-descent, lem-weil-pbc-projective-space-proj-separated, lem-weil-pbc-proper-
   over-separated, lem-pc-proper-monomorphism-closed.
3. Choose $T\simeq\mathbf G_m^r$. Apply [lem-sfb-gm-representation-weight-basis] to its first
   factor on $E$. Each resulting eigenspace is stable under the other factors: their actions
   commute, so applying another factor to $t^av$ again gives $t^a$ times that vector. Apply the
   same node to the second factor on each eigenspace, and continue for the finite number $r$ of
   factors. This gives $E=\bigoplus_{\chi\in S}E_\chi$ for a finite set $S$ of distinct
   characters, with an eigenbasis. These are group-scheme identities on all test algebras. For
   $r=0$ this is the single trivial weight (since $E\ne0$). Let $U_i=Q\cap D_+(x_i)$ for this
   eigenbasis. By [lem-weil-pbc-projective-space-standard-charts] these are affine opens
   covering $Q$, and $T$ preserves them because it multiplies each $x_i$ by a character. On
   $D_+(x_i)$, its action on the point-coordinate $u_j=x_j/x_i$ is multiplication by
   $\chi_j\chi_i^{-1}$. Thus the fixed subfunctor is the closed subscheme obtained by setting
   $u_j=0$ whenever $\chi_j\ne\chi_i$: in the Laurent polynomial coaction equation
   $(\chi_j\chi_i^{-1}-1)u_j=0$, distinct monomials have coefficients $u_j$ and $-u_j$. The same
   equations on $U_i$ agree on overlaps and represent $Q^T$. Uses: lem-sfb-gm-representation-
   weight-basis, lem-weil-pbc-projective-space-standard-charts.
4. For any $q\in Q(F)$ the fibre of $\pi$ is nonempty and smooth by [lem-sfb-borel-quotient-
   proper-geometry]. By [lem-pc-dense-separable-points] it has a point with residue field finite
   separable over $F$, hence an $F$-point. Write $q=gB$. Its scheme stabilizer is $gBg^{-1}$ by
   the torsor identity; consequently it is fixed by $T$ exactly when $T\subset gBg^{-1}$. In
   that case [lem-sfb-torus-normalizer-borel-transitivity] gives $n\in N_G(T)(F)$ with
   $nBn^{-1}=gBg^{-1}$. Then $n^{-1}g$ normalizes $B$, so lies in $B$ by [lem-sfb-borel-scheme-
   normalizer]; hence $q=nB$. Conversely every $nB$ with $n\in N_G(T)(F)$ is fixed. For
   injectivity, if $a\in N_G(T)(F)\cap B(F)$, apply the projection $p:B\to T$ from [lem-sfb-
   reductive-borel-pair-structure] to $ata^{-1}$, after arbitrary scalar extension. Since
   $ata^{-1}\in T$ and $T$ is commutative, $ata^{-1}=p(a)t p(a)^{-1}=t$. Thus $a\in
   C_G(T)(F)=T(F)$ by [lem-sfb-reductive-torus-self-centralizer]. The cosets $e_w$ are therefore
   indexed without repetition by $W$. This group is finite by [lem-sfb-reductive-rank-one-
   reflections]. Uses: lem-sfb-borel-quotient-proper-geometry, lem-pc-dense-separable-points,
   lem-sfb-torus-normalizer-borel-transitivity, lem-sfb-borel-scheme-normalizer, lem-sfb-
   reductive-borel-pair-structure, lem-sfb-reductive-torus-self-centralizer, lem-sfb-reductive-
   rank-one-reflections.
5. Write $\mathfrak g=T_1G$ and $\mathfrak b=T_1B$, with tangent spaces defined by [def-sc-
   scheme-tangent-space]. The differential of $\pi$ at $1$ is surjective: given a dual-number
   tangent vector to $Q$ at $B$, regard $F[\epsilon]/(\epsilon^2)$ as an $\mathcal
   O_{Q,B}$-algebra; formal smoothness of $\mathcal O_{G,1}$ over that stalk, supplied by [lem-
   sfb-smooth-stalk-formally-smooth], lifts the residue map $\mathcal O_{G,1}\to F$. This lift
   gives the required tangent vector to $G$ at $1$. The kernel consists precisely of the dual-
   number points in the fibre $B$, so is $\mathfrak b$. At $e_w$, apply the same argument to
   $g\mapsto gn_wB$, whose fibre at $1$ is $n_wBn_w^{-1}$. This map intertwines conjugation by
   $T$ on $G$ with the left action on $Q$, since $tgn_wB=(tgt^{-1})n_wB$. Hence it identifies
   $T_{e_w}Q$ with $\mathfrak g/\operatorname{Ad}(n_w)\mathfrak b$ as a $T$-representation. By
   [lem-sfb-reductive-rank-one-reflections], $\mathfrak
   g=\operatorname{Lie}(T)\oplus\bigoplus_{\alpha\in\Phi}\mathfrak g_\alpha$, each root summand
   one-dimensional. By [lem-sfb-reductive-borel-pair-structure], $\mathfrak b$ contains exactly
   the positive-root summands and $\operatorname{Lie}(T)$. Conjugation by $n_w$ carries weight
   $\alpha$ to $w\alpha$ because $t(n_wvn_w^{-1})=n_w((n_w^{-1}tn_w)v)n_w^{-1}$. Taking the
   quotient leaves exactly $\Phi\setminus w\Phi^+$, each once. This uses characters, never
   differentials of characters. Uses: def-sc-scheme-tangent-space, lem-sfb-smooth-stalk-
   formally-smooth, lem-sfb-reductive-rank-one-reflections, lem-sfb-reductive-borel-pair-
   structure.
6. Each $U_i$ of step 3 is affine, finite type and smooth over $F$. Its represented closed fixed
   subscheme is smooth by [lem-sfb-torus-fixed-scheme-smooth], so these opens make $Q^T$ smooth.
   Apply [lem-pc-dense-separable-points] to $Q^T$: its rational points are dense because $F$ is
   algebraically closed. By step 4 those points are a finite list. Each is closed (on an affine
   neighbourhood its residue map to $F$ has maximal kernel), so their finite union is closed and
   dense, and equals the entire underlying space. Every point is therefore open and closed. By
   [lem-weil-pbc-smooth-scheme-over-field-regular], its local ring is regular of dimension zero;
   the defining regularity condition says its maximal ideal has zero generators, so the local
   ring is a field. Its residue field is $F$ by [lem-weil-pbc-closed-point-residue-field-base].
   A singleton open scheme has an affine neighbourhood equal to itself and thus is
   $\operatorname{Spec}F$. Hence $Q^T=\coprod_{w\in W}\{e_w\}$ as schemes, including
   reducedness. Uses: lem-sfb-torus-fixed-scheme-smooth, lem-pc-dense-separable-points, lem-
   weil-pbc-smooth-scheme-over-field-regular, lem-weil-pbc-closed-point-residue-field-base.
7. By [lem-sfb-regular-cocharacter-borel-description] choose a regular $\lambda_0$ with
   $B=P(\lambda_0)$. Comparing its Lie description with the positive-root summands in
   $\operatorname{Lie}(B)$ gives $\langle\alpha,\lambda_0\rangle>0$ for every $\alpha\in\Phi^+$.
   Identify $X_*(T)$ with $\mathbf Z^r$ using $T\simeq\mathbf G_m^r$, and let $e_1,\ldots,e_r$
   be the coordinate cocharacters. For a positive integer $N$ put
   $\lambda(N)=N^{r+1}\lambda_0+\sum_{i=1}^rN^i e_i$. For each positive root its pairing with
   this cocharacter is a polynomial in $N$ with positive leading coefficient, so is positive for
   all sufficiently large $N$. For each distinct $\chi,\psi\in S$, its pairing with $\chi-\psi$
   is a nonzero polynomial: the coordinate coefficients $\langle\chi-\psi,e_i\rangle$ are not
   all zero and occur in different degrees below $r+1$. Such a polynomial has only finitely many
   integer roots. Choose $N$ large enough for all inequalities and outside all these finite
   sets. Then $\lambda=\lambda(N)$ is dominant and separates all distinct weights of $E$. If
   $\Phi$ is empty there are no positivity inequalities. If $r=0$, there are no distinct
   weights, and $\lambda=0$ already works. Uses: lem-sfb-regular-cocharacter-borel-description,
   lem-sfb-reductive-borel-pair-structure.
8. On every eigenbasis chart $D_+(x_i)$ from step 3, the fixed scheme for $\lambda$ is cut out
   by $u_j=0$ whenever $\langle\chi_j-\chi_i,\lambda\rangle\ne0$. Indeed, invariance is the
   identity $(z^{\langle\chi_j-\chi_i,\lambda\rangle}-1)u_j=0$ in $A[z,z^{-1}]$, whose
   coefficients force $u_j=0$ for a nonzero exponent over any test algebra $A$. This remains
   true when that integer is divisible by the characteristic. Separation makes this exactly the
   condition $\chi_j\ne\chi_i$, so its fixed ideal equals the torus fixed ideal on every chart.
   Thus $\mathbf P(E)^{\lambda(\mathbf G_m)}=\mathbf P(E)^T$ as schemes. Finally, because
   $i:Q\hookrightarrow\mathbf P(E)$ is equivariant and a monomorphism, a test-scheme point of
   $Q$ is fixed precisely when its image is fixed, after every algebra extension. Pulling back
   the two equal fixed subfunctors proves $Q^{\lambda(\mathbf G_m)}=Q^T$. Uses: lem-weil-pbc-
   projective-space-standard-charts.
The Laurent-polynomial coefficient argument works in every characteristic, even
when an exponent is divisible by the characteristic. Empty roots and rank zero
are included: the flag scheme is a point and the trivial cocharacter suffices. -/
theorem flag_torus_fixed_geometry
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (aB : ModObj T.X B.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φplus : Finset (RankOneRoots.Character T))
    (hΦplus : ∀ χ : RankOneRoots.Character T, χ ∈ Φplus ↔
      χ.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥) :
    Smooth Q.hom ∧ IsProjective Q.hom ∧ ConnectedSpace Q.left ∧
    Finite (RankOneRoots.Weyl iT) ∧
    ∃ (aQ : ModObj G.X Q),
      (𝟙 G.X ⊗ₘ π) ≫ aQ.smul = μ[G.X] ≫ π ∧
    ∃ (n : ℕ) (ρ : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin (n + 1))) F)
      (_ : IsMonHom ρ) (aP : ModObj G.X (DiagonalProjectiveAction.space F n))
      (embedding : Q ⟶ DiagonalProjectiveAction.space F n),
      FlagGeometry.IsLinearProjectiveAction G n ρ aP ∧ IsClosedImmersion embedding.left ∧
      aQ.smul ≫ embedding = (G.X ◁ embedding) ≫ aP.smul ∧
    ∃ (act : RankOneRoots.Weyl iT →* Aut T),
      (∀ (nw : RankOneRoots.normalizer iT) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ T.X),
        t ≫ (act (QuotientGroup.mk nw)).hom.hom.hom ≫ iT.hom.hom =
          (toUnit (StandardGroupSchemes.affine F A) ≫ nw.val) * (t ≫ iT.hom.hom) *
            (toUnit (StandardGroupSchemes.affine F A) ≫ nw.val)⁻¹) ∧
      (∀ (nw : RankOneRoots.Weyl iT → RankOneRoots.normalizer iT),
        (∀ w, QuotientGroup.mk (nw w) = w) →
        ∃ (Z : Over (Spec (.of F))) (z : Z ⟶ Q)
          (e : RankOneRoots.Weyl iT → (𝟙_ (Over (Spec (.of F))) ⟶ Z)),
          IsClosedImmersion z.left ∧
          Nonempty (IsColimit (Cofan.mk Z e)) ∧
          (∀ w, e w ≫ z = (nw w).val ≫ π) ∧
          (∀ (A : CommAlgCat.{u} F) (q : (algSpec (.of F)).obj (op A) ⟶ Q),
            (∃ q' : (algSpec (.of F)).obj (op A) ⟶ Z, q' ≫ z = q) ↔
              FlagGeometry.IsFixed iT Q aQ A q) ∧
          ∀ w, FlagGeometry.HasTangentWeightBasis iT Q aQ ((nw w).val ≫ π)
            ({χ : RankOneRoots.Character T | χ ∈ Φplus ∨
                ∃ α ∈ Φplus, χ.hom.hom = α.hom.hom⁻¹} \
              Set.image (fun χ : RankOneRoots.Character T ↦ (act w).inv ≫ χ)
                (Φplus : Set _))) ∧
      ∃ (cochar : RankOneRoots.Cocharacter T) (pairing : RankOneRoots.Character T → ℤ),
        (∀ χ, cochar.hom.hom ≫ χ.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ pairing χ) ∧
        (∀ α ∈ Φplus, 0 < pairing α) ∧
        (∀ (A : CommAlgCat.{u} F)
          (x : (algSpec (.of F)).obj (op A) ⟶ DiagonalProjectiveAction.space F n),
          FlagGeometry.IsFixed (cochar ≫ iT) (DiagonalProjectiveAction.space F n) aP A x ↔
            FlagGeometry.IsFixed iT (DiagonalProjectiveAction.space F n) aP A x) ∧
        ∀ (A : CommAlgCat.{u} F) (q : (algSpec (.of F)).obj (op A) ⟶ Q),
          FlagGeometry.IsFixed (cochar ≫ iT) Q aQ A q ↔ FlagGeometry.IsFixed iT Q aQ A q := by
  sorry

end AlgebraicGeometry
