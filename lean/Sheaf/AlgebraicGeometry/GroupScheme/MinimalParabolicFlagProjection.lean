module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Monoidal.Grp
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Minimal parabolic flag projections and rank-one coordinates

Source: Brion--Kumar, Frobenius Splitting Methods, Section 2.1, pp.62--63,
and Section 2.2.1, diagram (D), pp.66--67; Milne, Algebraic Groups (2017),
21.11, 21.19 and 21.89--21.91.
(blueprint: lem-sfb-minimal-parabolic-flag-projection)

Quotients are arbitrary presentations with their faithfully flat torsor kernel pairs.
The multiplication chart is specified by its formula in G and a cartesian square;
thus it identifies the full scheme-theoretic inverse image, including nilpotents.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The minimal-parabolic projection and its root coordinate, in every characteristic.
Source: Brion--Kumar 2.1, pp.62--63, and 2.2.1 diagram (D), pp.66--67;
Milne 21.11, 21.19 and 21.89--21.91.
(blueprint: lem-sfb-minimal-parabolic-flag-projection)

The hypotheses unpack the Borel pair, its actual character root datum and root
subgroups, the reflection's normalizer class, the generated closed subgroup P,
and the quotient presentations from the recorded dependencies. The additive group
scheme is the affine line Spec F[X]. The base point B is the identity section
followed by p. Sections together with the displayed right-action kernel pair are
exactly Zariski local trivializations of the B-torsor.

Proof plan (the twelve steps of the DAG node):
1. Put $P=P_\alpha$, $L=C_G(T_\alpha)$, $D=B\cap L$ and $R=R_u(P)$. Apply the standard-parabolic
lemma with $I=\{\alpha\}$: it gives $P=R\rtimes L$, $B=R\rtimes D$, with $D$ a Borel of $L$
containing $T$. The rank-one-reflection lemma identifies this same centralizer $L$ as reductive of
semisimple rank one. Thus its rank-one classification applies. These are subgroup-scheme
decompositions, so they can be used over arbitrary $F$-algebras, including nonreduced ones.
2. Choose the isomorphism of pairs $(L,T)$ given by the split-rank-one classification. It
identifies them with a split torus factor times $J$, with diagonal maximal torus, where $J$ is
$\operatorname{SL}_2$, $\operatorname{GL}_2$, or $\operatorname{PGL}_2$. We may interchange the
two matrix axes so that $\alpha$ is the upper-root character. To identify $D$
scheme-theoretically, write $D=P(\lambda)$ using the regular-cocharacter Borel lemma. Its
Lie-algebra formula and the positive root $\alpha$ of $D$ give $\langle\alpha,\lambda\rangle>0$.
Conjugation multiplies the upper matrix entry by a positive power of the parameter and the lower
entry by its negative power. The limit exists exactly when the lower entry is zero; this is a
coefficient identity over any algebra. The central torus factor acts trivially. Consequently $D$
is the torus factor times the upper-triangular subgroup $D_J$ of $J$. For $\operatorname{PGL}_2$
this calculation is checked after fppf lifting to invertible matrices and descends, since scalar
matrices preserve both the limit condition and upper triangularity.
3. Here is the quotient calculation in these matrix models. Send a matrix $M$ to its first-column
line $[M_{11}:M_{21}]$. On the two standard affine charts of $\mathbf P^1$, regular lifts are
$$S_0(z)=I_2+zE_{21},\qquad S_1(a)=aE_{11}-E_{12}+E_{21}.$$ Here $E_{ij}$ is the $2\times2$ matrix
unit and $I_2$ is the identity matrix. Both have determinant one and first-column lines $[1:z]$
and $[a:1]$. On either chart every matrix over it factors uniquely as $S_iD_J$: its second factor
is $S_i^{-1}M$, which is upper triangular because its first column spans the first coordinate
line. This gives inverse regular maps between the inverse image of the chart and the chart times
$D_J$. For $\operatorname{PGL}_2$, the same formula on matrix lifts is independent of their scalar
ambiguity; it therefore holds as an identity of fppf sheaves. The unused split torus factor is
contained in $D$ and cancels from right cosets. These explicit sections and factorizations
identify the represented right-coset sheaf $L/D$ with $\mathbf P^1_F$, with a Zariski locally
trivial right $D$-torsor $L\to L/D$. The identity coset is $[1:0]$ and its complement is the chart
$[a:1]$.
4. The semidirect-product formulas give an isomorphism of fppf coset sheaves $P/B\simeq L/D$: send
the class of $(r,l)$ to $lD$, with inverse induced by $L\hookrightarrow P$. Indeed $R\subseteq B$
and $r l=l(l^{-1}rl)$, so $(r,l)B=lB$; and two $L$-points differ by $B$ precisely when they differ
by $D=B\cap L$. These formulas hold locally for the fppf topology and hence on the quotient
sheaves. In particular $P/B$ is represented by the projective line just constructed. The sections
$S_i$ lifted to $P$ trivialize $P\to P/B$: for a lift $s_i$ the mutually inverse maps are
$(x,b)\mapsto s_i(x)b$ and $p\mapsto(\bar p,s_i(\bar p)^{-1}p)$. This proves the right $B$-torsor
assertion with actual Zariski sections.
5. In the matrix model let $w=E_{21}-E_{12}$. It normalizes the diagonal torus and exchanges the
two root spaces, so its class in $N_L(T)/T$ is the unique nonidentity class of the
rank-one-reflection lemma. Its image $n_0$ therefore represents $s_\alpha$ in $N_G(T)/T$. The
chosen representative is $n_s=n_0t_0$ for some $t_0\in T(F)$; hence $n_s\in L(F)\subseteq P(F)$
and $n_sB=n_0B$. The upper-root subgroup of $L$ is the matrix upper-unitriangular subgroup: in the
matrix models this is a smooth connected $T$-normalized subgroup with the prescribed root tangent
space, so the uniqueness assertion of the root-subgroup lemma identifies it with $U_\alpha$. The
chosen group coordinate $u_\alpha$ thus has matrix coordinate $x\mapsto cx$, $c\in F^\times$.
Indeed an automorphism of $\mathbf G_a$ as an algebraic group is an invertible polynomial fixing
zero, and the degree of its polynomial inverse forces degree one. Therefore $u_\alpha(a)n_sB$
corresponds to $[ca:1]$, an isomorphism from $\mathbf A^1$ to the complement of $B$.
6. The inverse image in $P$ of this affine chart is exactly $Bn_sB$, with its locally closed
scheme structure: its points have the unique expression $u_\alpha(a)n_sb$. More precisely, the
inverse to the asserted multiplication map is $$p\longmapsto\bigl(a(\bar p),(u_\alpha(a(\bar
p))n_s)^{-1}p\bigr),$$ where $a$ is the regular coordinate of the preceding step. The second
component belongs to $B$ by equality in the quotient sheaf; this is the torsor identity, not a
test only on field points. Thus both maps are regular scheme morphisms. The other fibre of the
two-stratum decomposition is $B$ itself. For every algebraically closed extension $K/F$, every
point above $[a:1]$ lies in $B(K)n_sB(K)$ by this formula, and every point above $[1:0]$ lies in
$B(K)$. The images in $P/B$ are disjoint. This gives the stated disjoint decomposition of $P(K)$.
7. For $t\in T(A)$ use the root conjugation identity and the fact that $n_s$ normalizes $T$: $$t
u_\alpha(a)n_s=u_\alpha(\alpha(t)a)n_s(n_s^{-1}tn_s).$$ The final factor is in $T(A)\subseteq
B(A)$, so it disappears on taking right cosets. This proves the asserted left $T$-action
$a\mapsto\alpha(t)a$ over every commutative $F$-algebra $A$. No differential of $\alpha$, nor
division by the characteristic, occurs.
8. Since $B\subseteq P$, the coset map $gB\mapsto gP$ is well defined on fppf quotient sheaves and
thus gives the morphism $q_\alpha:Q\to H_\alpha$. Take the finite Zariski covering $V_i$ of
$H_\alpha$ with sections $s_i:V_i\to G$ from the standard-parabolic lemma. Its torsor identity
identifies $G|_{V_i}$ with $V_i\times P$ by $(x,p)\mapsto s_i(x)p$. Dividing by the right action
of $B$ gives inverse morphisms $$V_i\times(P/B)\longleftrightarrow q_\alpha^{-1}(V_i),\quad
(x,pB)\mapsto s_i(x)pB,$$ whose inverse is $gB\mapsto(gP,s_i(gP)^{-1}gB)$. The quotient-sheaf
meaning makes these formulas valid also when $g$ or $p$ exists only fppf locally. Together with
step 4 this proves the required Zariski local triviality with fibre $\mathbf P^1_F$.
9. The fibre of $q_\alpha$ at the identity coset $o=P$ is $P/B$ scheme-theoretically: after fppf
lifting a point to $g\in G$, the equality $gP=P$ is exactly the condition $g\in P$. The point
$o:\operatorname{Spec}F\to H_\alpha$ is a closed immersion: it is a section of the separated
structure morphism of the proper scheme $H_\alpha$, hence a pullback of its closed diagonal.
Closed immersions are preserved by base change, so $Q\times_{H_\alpha}\operatorname{Spec}F\to Q$
is a closed immersion. This identifies the stated fibre as the closed subscheme $P/B\subseteq Q$,
with the quotient structure already used above.
10. Refine the local products of step 8 by the two affine charts of $\mathbf P^1$. Each resulting
open subscheme $W\subseteq Q$ is identified with $\mathbf A^1_{V_i}=V_i\times_F\mathbf A^1_F$, and
$q_\alpha|_W$ is the projection to $V_i$ followed by the inclusion $V_i\hookrightarrow H_\alpha$.
Since $V_i$ is open in $H_\alpha$, the scheme $\mathbf A^1_{V_i}$ is the open subscheme of
$\mathbf A^1_{H_\alpha}$ lying over $V_i$, so the same map is the composite $\mathbf
A^1_{V_i}\hookrightarrow\mathbf A^1_{H_\alpha}\to H_\alpha$ of an open immersion with the
projection. The projection is smooth by affine-space smoothness, hence the composite is smooth by
the open-immersion composition lemma. These open subschemes $W$ cover $Q$ and smoothness is local
on the source, so $q_\alpha$ is smooth.
11. For projectivity first identify $Q$ with the projective Borel variety $X=\mathcal B(G)$
supplied by the general-Borel-flag lemma. The point $b_B$ has scheme-theoretic stabilizer $B$, so
the homogeneous-orbit lemma identifies its reduced locally closed orbit $O$ with $G/B=Q$. The
action is transitive on $X(F)$, so $O$ contains every $F$-point of $X$. Because $X$ is finite type
over the algebraically closed field, its closed points are $F$-points and are dense in every
closed subset. Thus the closure of $O$ is $X$. A dense locally closed orbit is open. Its closed
complement has no closed points, so is empty. An open subset with full underlying space is the
whole open subscheme. Since $X$ is smooth over $F$, smooth geometric reducedness makes it reduced,
so its reduced orbit structure agrees with that open subscheme. Consequently $Q\simeq X$ and $Q$
is projective over $F$.
12. The standard-parabolic lemma makes $H_\alpha$ proper over $F$, hence separated over $F$. Apply
the finite-constant projective-graph lemma with $k=F$ and the trivial extension $F/F$, $R=Q$,
which embeds in a finite projective space over $F$ by step 11, $S=H_\alpha$ and $c=q_\alpha$. It
gives $N\geq0$ and a closed immersion $i:Q\hookrightarrow\mathbf P^N_F$ such that
$(i,q_\alpha):Q\hookrightarrow\mathbf P^N_F\times_F H_\alpha=\mathbf P^N_{H_\alpha}$ is a closed
immersion over $H_\alpha$, and it also gives that $q_\alpha$ is proper, hence of finite type and
quasi-compact. Thus $q_\alpha$ is H-projective and quasi-compact, which is projectivity in
precisely the convention of the item. All constructions used matrices of determinant one,
group-scheme isomorphisms, and the stated characteristic-free structural lemmas. They apply
without exception in characteristic two; the sign $-1$ simply equals $1$ there.
-/
theorem minimalParabolic_flag_projection
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
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
    (base : D.Base) (hred : D.IsReduced)
    (hroot : ∀ α : Φ, D.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (D.toLinearMap χ ν))
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      base.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (U : Φ → Grp (Over (Spec (.of F)))) (iU : ∀ α : Φ, U α ⟶ G)
    (hU : ∀ α : Φ,
      IsClosedSubgroupScheme (iU α).hom.hom ∧ Smooth (U α).X.hom ∧
      ConnectedSpace (U α).X.left ∧ @TorusCharacterTangent.IsStable F _ T G aG _ (iU α) ∧
      (GrpObj.differential (iU α).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)
    (α : base.support)
    (coord : Grp.mk (StandardGroupSchemes.additive F) ≅ U α.val)
    (act : RankOneRoots.Weyl iT →* Aut T)
    (hact : ∀ (n : RankOneRoots.normalizer iT) (A : CommAlgCat.{u} F)
      (t : StandardGroupSchemes.affine F A ⟶ T.X),
      t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
        (toUnit _ ≫ n.val) * (t ≫ iT.hom.hom) * (toUnit _ ≫ n.val)⁻¹)
    (s : RankOneRoots.Weyl iT)
    (hs : ∀ χ : RankOneRoots.Character T,
      (act s).inv ≫ χ = (D.reflection α.val (Additive.ofMul χ)).toMul)
    (n : RankOneRoots.normalizer iT) (hn : QuotientGroup.mk n = s)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hQ : IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (P : Grp (Over (Spec (.of F)))) (iP : P ⟶ G) (bP : B ⟶ P)
    (hP : IsClosedSubgroupScheme iP.hom.hom) (hbP : bP ≫ iP = iB)
    (hneg : ∀ β : Φ, β.val = -α.val.val → ∃ f : U β ⟶ P, f ≫ iP = iU β)
    (hgen : ∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
      IsClosedSubgroupScheme k.hom.hom → (∃ f : B ⟶ K, f ≫ k = iB) →
      (∀ β : Φ, β.val = -α.val.val → ∃ f : U β ⟶ K, f ≫ k = iU β) →
      ∃ f : P ⟶ K, f ≫ k = iP)
    (H : Over (Spec (.of F))) (ρ : G.X ⟶ H)
    (hH : IsProper H.hom ∧ LocallyOfFiniteType H.hom ∧ QuasiCompact H.hom)
    (hρlfp : LocallyOfFinitePresentation ρ.left)
    (hρqc : QuasiCompact ρ.left) (hρqs : QuasiSeparated ρ.left)
    (hρflat : Flat ρ.left) (hρsurj : Surjective ρ.left)
    (hρinv : (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom)) ≫ ρ = fst G.X P.X ≫ ρ)
    (hρtorsor : IsPullback (fst G.X P.X)
      (fst G.X P.X * (snd G.X P.X ≫ iP.hom.hom)) ρ ρ) :
    (∃ nP : 𝟙_ (Over (Spec (.of F))) ⟶ P.X, nP ≫ iP.hom.hom = n.val) ∧
    (∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K],
      (RankOneRoots.pointImage iP (StandardGroupSchemes.affine F K) : Set _) =
        (RankOneRoots.pointImage iB (StandardGroupSchemes.affine F K) : Set _) ∪
        {g | ∃ b c : StandardGroupSchemes.affine F K ⟶ B.X,
          g = (b ≫ iB.hom.hom) * (toUnit _ ≫ n.val) * (c ≫ iB.hom.hom)} ∧
      Disjoint (RankOneRoots.pointImage iB (StandardGroupSchemes.affine F K) : Set _)
        {g | ∃ b c : StandardGroupSchemes.affine F K ⟶ B.X,
          g = (b ≫ iB.hom.hom) * (toUnit _ ≫ n.val) * (c ≫ iB.hom.hom)}) ∧
    ∃ (q : Q ⟶ H) (C : Over (Spec (.of F))) (p : P.X ⟶ C)
      (inc : C ⟶ Q) (c : StandardGroupSchemes.additive F ⟶ C)
      (m : StandardGroupSchemes.additive F ⊗ B.X ⟶ P.X) (aC : ModObj T.X C),
      π ≫ q = ρ ∧ Smooth q.left ∧ IsProjective q.left ∧
      (∀ x : H.left, ∃ (V : Scheme.{u}) (v : V ⟶ H.left)
        (e : pullback q.left v ≅ ProjectiveLine V),
        IsOpenImmersion v ∧ x ∈ Set.range v ∧
        e.hom ≫ (ProjectiveLine V ↘ V) = pullback.snd q.left v) ∧
      Nonempty (C ≅ Over.mk (ProjectiveLine (Spec (.of F)) ↘ Spec (.of F))) ∧
      p ≫ inc = iP.hom.hom ≫ π ∧ IsClosedImmersion inc.left ∧
      IsPullback inc (toUnit C) q (η[G.X] ≫ ρ) ∧
      Flat p.left ∧ Surjective p.left ∧
      (fst P.X B.X * (snd P.X B.X ≫ bP.hom.hom)) ≫ p = fst P.X B.X ≫ p ∧
      IsPullback (fst P.X B.X)
        (fst P.X B.X * (snd P.X B.X ≫ bP.hom.hom)) p p ∧
      (∀ x : C.left, ∃ (V : Over (Spec (.of F))) (v : V ⟶ C) (σ : V ⟶ P.X),
        IsOpenImmersion v.left ∧ x ∈ Set.range v.left ∧ σ ≫ p = v) ∧
      IsOpenImmersion c.left ∧
      Set.range c.left = (Set.range (η[P.X] ≫ p).left)ᶜ ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A] (a : A),
        (TorusCharacterTangent.additiveParameterPoint F a ≫ c ≫ inc) =
          ((TorusCharacterTangent.additiveParameterPoint F a ≫
            coord.hom.hom.hom ≫ (iU α.val).hom.hom) * (toUnit _ ≫ n.val)) ≫ π) ∧
      m ≫ iP.hom.hom =
        (fst _ _ ≫ coord.hom.hom.hom ≫ (iU α.val).hom.hom) *
          (toUnit _ ≫ n.val) * (snd _ _ ≫ iB.hom.hom) ∧
      IsPullback (fst _ _) m c p ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (t : StandardGroupSchemes.affine F A ⟶ T.X)
        (z : StandardGroupSchemes.affine F A ⟶ P.X),
        lift t (z ≫ p) ≫ aC.smul ≫ inc =
          ((t ≫ iT.hom.hom) * (z ≫ iP.hom.hom)) ≫ π) ∧
      ∀ (A : Type u) [CommRing A] [Algebra F A]
        (t : StandardGroupSchemes.affine F A ⟶ T.X) (a : A),
        lift t (TorusCharacterTangent.additiveParameterPoint F a ≫ c) ≫ aC.smul =
          TorusCharacterTangent.additiveParameterPoint F
            (TorusCharacterTangent.multiplicativePointCoordinate F
              (t ≫ α.val.val.toMul.hom.hom) * a) ≫ c := by
  sorry

end AlgebraicGeometry
