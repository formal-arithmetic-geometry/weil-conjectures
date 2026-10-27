module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.AlgebraicGeometry.Group.Affine
import Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Rosenlicht's splitting criterion

Source: Milne, Algebraic Groups (2017), Theorem 16.58, p.345, and Section 16g,
pp.343--344 (blueprint: lem-sfb-rosenlicht-split-solvable-criterion).

The dominating map is a morphism of schemes over k, with no homomorphism condition.
The conclusion records the entire subnormal series and its represented fppf quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth geometrically connected solvable affine algebraic group dominated by a
split torus has a split series; when it is unipotent every quotient is additive.

Source: Milne, Algebraic Groups (2017), Theorem 16.58, p.345; split-series convention
in Section 16g, p.343, and the unipotent clause in Proposition 16.54, p.344
(blueprint: lem-sfb-rosenlicht-split-solvable-criterion).

Proof plan from the DAG, with the cited prerequisite nodes:
1. For any smooth geometrically connected affine group $H$ occurring below, [lem-trf-smooth-
   connected-fibre-normal-integrality] makes $H$ geometrically integral. Thus its coordinate
   ring is a domain, and a dense morphism into $H$ has injective pullback: a function vanishing
   on the image vanishes at every prime, hence is nilpotent and therefore zero. If $\dim H=0$,
   [lem-pc-zero-dimensional-closed-subscheme-finite], applied to $H\hookrightarrow H$, makes
   $k[H]$ a finite-dimensional domain, hence a field (multiplication by a nonzero element is an
   injective endomorphism of a finite-dimensional vector space and is surjective). Evaluation at
   the identity embeds this field into $k$, identically on $k$, so $k[H]=k$ and $H=1$. In
   particular every nontrivial such $H$ has positive dimension.
   Dependencies: lem-trf-smooth-connected-fibre-normal-integrality, lem-pc-zero-dimensional-
   closed-subscheme-finite.
2. Split series are closed under extension in the precise form needed here. If $N\triangleleft
   H$ and $N,H,Q=H/N$ are smooth geometrically connected, take the inverse images in $H$ of the
   terms of a split series for $Q$, then append a split series for $N$. The correspondence and
   quotient clauses of [lem-sfb-affine-normal-quotient-geometry] identify each quotient in the
   lifted segment with the corresponding quotient for $Q$, and give closed normal inclusions.
   Its smoothness and connectedness clause, applied after every field extension, makes every
   inverse-image term smooth and geometrically connected. The appended terms already have these
   properties. The same argument gives additive-only series when both input series have
   additive-only quotients.
   Dependencies: lem-sfb-affine-normal-quotient-geometry.
3. First treat a smooth geometrically connected group $H$ of multiplicative type dominated by
   $f:T_0=\mathbf G_m^N\to H$. Replace $f$ by $h(t)=f(1)^{-1}f(t)$, so $h(1)=1$. Over $\bar k$,
   embed $H_{\bar k}$ in a power of $\mathbf G_m$ using the meaning of multiplicative type in
   [lem-sfb-unipotent-to-multiplicative-trivial]. For any coordinate unit $u$ of the composite,
   apply [lem-sfb-rosenlicht-product-unit-factorization] on $T_{0,\bar k}\times T_{0,\bar k}$ to
   $u(xy)$. The normalized identity reads $u(xy)=u(x)u(y)$, so the composite, and therefore
   $h_{\bar k}$, is a group homomorphism. Equality of the two coordinate pullbacks descends by
   injectivity in [lem-sfb-field-extension-tensor-injective]; hence $h$ is a homomorphism over
   $k$. Its closed-image factorization is [lem-sfb-affine-homomorphism-flat-image]. Density and
   reducedness of $H$ force the closed-image ideal to be zero, so $h$ is faithfully flat. By
   [lem-sfb-field-split-torus-flat-quotient], $H$ is a split torus. Its coordinate-factor series
   has successive quotients $\mathbf G_m$.
   Dependencies: lem-sfb-unipotent-to-multiplicative-trivial, lem-sfb-rosenlicht-product-unit-
   factorization, lem-sfb-field-extension-tensor-injective, lem-sfb-affine-homomorphism-flat-
   image, lem-sfb-field-split-torus-flat-quotient.
4. Next let $H$ be a smooth geometrically connected closed subgroup of $\mathbf G_a^n$ in
   characteristic $p>0$, dominated by $f:\mathbf G_m^N\to H$. Put $A=k_\sigma[F]$,
   $\sigma(c)=c^p$, with multiplication as in [lem-sfb-primitive-frobenius-module-duality]. That
   node identifies $P(H)=\operatorname{Hom}(H,\mathbf G_a)$ with a finitely generated left
   $A$-module and reconstructs $H$ from it. By [lem-sfb-affine-group-coordinate-hopf], these
   homomorphisms are exactly primitive coordinate functions: the equality $a(xy)=a(x)+a(y)$ is
   $\Delta(a)=a\otimes1+1\otimes a$. A constant primitive is zero, since $c=2c$ implies $c=0$.
   Thus $P(H)\to k[H]/k$ is injective. Dominance gives an injective map $k[H]/k\to L/k$, where
   $L=k[z_1^{\pm1},\ldots,z_N^{\pm1}]$: if $f^*a=c$, injectivity of $f^*$ gives $a=c$. The
   composite is $A$-linear for $F[a]=[a^p]$; this action is well-defined modulo constants
   because $(a+c)^p-a^p=c^p$.
   Dependencies: lem-sfb-primitive-frobenius-module-duality, lem-sfb-affine-group-coordinate-
   hopf.
5. The left $A$-module $L/k$ is free. Index a basis by the vectors $v\in\mathbf
   Z^N\setminus\{0\}$ not in $p\mathbf Z^N$, sending the generator $e_v$ to $[z^v]$. Indeed each
   nonzero exponent $u$ has a unique expression $u=p^rv$ with $r\geq0$ and $v\notin p\mathbf
   Z^N$. For $\sum_r c_rF^r\in A$, its value on $[z^v]$ is $\sum_r c_r[z^{p^rv}]$. Distinct
   pairs $(v,r)$ give distinct Laurent monomials, so this map $\bigoplus_v A\to L/k$ is both
   injective and surjective, by coefficient comparison. This also covers $N=0$, when both sides
   are zero. Apply [lem-sfb-frobenius-skew-free-submodules] to the finitely generated image of
   $P(H)$ in this free module: $P(H)\simeq A^d$. Reconstruction by [lem-sfb-primitive-frobenius-
   module-duality] now gives $H\simeq\mathbf G_a^d$: an $A$-linear map $A^d\to R$ is uniquely
   determined by its $d$ basis values in $R$, with addition coordinatewise. Coordinate-factor
   subgroups give the desired additive series.
   Dependencies: lem-sfb-frobenius-skew-free-submodules, lem-sfb-primitive-frobenius-module-
   duality.
6. In characteristic zero, let $H$ be commutative and smooth geometrically connected, still with
   a dominant torus morphism. The field is perfect, so [lem-sfb-perfect-commutative-torus-
   unipotent-product] gives $H\simeq U\times T$, with both factors smooth geometrically
   connected, $T$ a torus and $U$ closed in a unitriangular group. Projection of the dominant
   morphism onto $T$ is dominant (the projection is surjective and continuous), so step 3 splits
   $T$. The commutative factor $U$ is a vector group by [lem-sfb-char-zero-commutative-
   unipotent-vector-group]. The additive coordinate series of $U$, the multiplicative coordinate
   series of $T$, and step 2 therefore give the required split series of $H$.
   Dependencies: lem-sfb-perfect-commutative-torus-unipotent-product, lem-sfb-char-zero-
   commutative-unipotent-vector-group.
7. We now prove the solvable conclusion by strong induction on $d=\dim G$, for every smooth
   geometrically connected solvable affine group with a dominant torus morphism. Step 1 handles
   $d=0$. For later reductions, a nontrivial proper smooth geometrically connected normal
   subgroup $N\subset G$ has $0<\dim N<d$: positivity is step 1 and strictness is [lem-wf-
   affine-dimension-drop], since $G$ is integral. The quotient $Q=G/N$ is smooth geometrically
   connected by [lem-sfb-affine-normal-quotient-geometry], and [lem-sfb-homogeneous-quotient-
   krull-dimension] gives $\dim Q=d-\dim N<d$. Whenever both $N$ and $Q$ have dominant torus
   morphisms and are solvable, the induction hypothesis splits each and step 2 splits $G$. This
   is the induction assertion used below, not an assumption that arbitrary subgroups inherit
   domination.
   Dependencies: lem-wf-affine-dimension-drop, lem-sfb-affine-normal-quotient-geometry, lem-sfb-
   homogeneous-quotient-krull-dimension.
8. Take $D=D(G)$ from [lem-sfb-derived-commutator-word-arbitrary-field]. It and $G/D$ are smooth
   geometrically connected, and the quotient is commutative. Both are solvable: intersect a
   solvable series with $D$ and use that commutators in each intersection lie in the next; its
   commutative quotients are represented by [lem-sfb-affine-normal-quotient-geometry]. The
   quotient $G/D$ is commutative, hence solvable. Explicitly $D^i(G)$ lies in the $i$th term of
   the given subnormal series; if $D(G)=G$, all $D^i(G)=G$, forcing $G=1$. Thus for nontrivial
   $G$, $D\ne G$. If $D=1$, $G$ is commutative. Otherwise $D$ has a dominant torus morphism:
   compose the dominant word $w_r:G^{2r}\to D$ with $f^{2r}$. To check dominance, the tensor
   powers of the injective coordinate map $f^*$ remain injective by [lem-weil-pbc-module-over-
   field-flat, lem-trf-flat-tensor-preserves-injection], so $f^{2r}$ and then its composite with
   $w_r$ are dominant. The quotient $G/D$ is dominated by the composite of $f$ with its
   faithfully flat quotient map. Step 7 applies. It remains only to split commutative $G$;
   characteristic zero was settled in step 6.
   Dependencies: lem-sfb-derived-commutator-word-arbitrary-field, lem-sfb-affine-normal-
   quotient-geometry, def-sfb-solvable-group-structure, lem-weil-pbc-module-over-field-flat,
   lem-trf-flat-tensor-preserves-injection.
9. Suppose now $G$ is commutative and $\operatorname{char}k=p>0$. Factor $[p]_G:G\to G$ through
   its closed image $I$ using [lem-sfb-algebraic-group-homomorphism-factorization]. Its kernel
   $K$ is normal and the quotient description is $I=G/K$. Thus [lem-sfb-affine-normal-quotient-
   geometry] makes $I$ smooth geometrically connected. It is dominated by the torus through
   $G\to I$. The quotient $G/I$ is also smooth geometrically connected and dominated through
   $G\to G/I$. All these groups are commutative, hence solvable. If $1\ne I\ne G$, step 7 and
   the induction hypothesis apply to $I\triangleleft G$; step 2 finishes. If $I=1$, then
   $[p]_G=0$, and [lem-sfb-smooth-p-torsion-additive-embedding] embeds $G$ as a closed subgroup
   of a vector group over $k$. Steps 4-5 give $G\simeq\mathbf G_a^d$.
   Dependencies: lem-sfb-algebraic-group-homomorphism-factorization, lem-sfb-affine-normal-
   quotient-geometry, lem-sfb-smooth-p-torsion-additive-embedding.
10. In the remaining case $I=G$, the closed immersion $I\hookrightarrow G$ is an isomorphism
   ($I$ is smooth, hence reduced, and $G$ is reduced), so $[p]_G$ is flat and surjective on
   underlying spaces. Its coordinate map is a flat ring map (source and target are affine)
   inducing a surjection of prime spectra, hence faithfully flat in the sense of [def-weil-pbc-
   faithfully-flat-ring-map] by [lem-weil-pbc-flat-surjective-spectrum-faithfully-flat]. Over
   $F=\bar k$, apply [lem-sfb-commutative-diagonalizable-unipotent-product]: $G_F\simeq U\times
   D$ with $U\hookrightarrow\mathcal U_n$ and $D$ diagonalizable. Each factor is a quotient by
   the other and hence smooth and geometrically connected by [lem-sfb-affine-normal-quotient-
   geometry]. For $p^e\geq n$, every upper unitriangular matrix $1+X$ over every $F$-algebra
   satisfies $(1+X)^{p^e}=1+X^{p^e}=1$, since $X^n=0$. Thus $[p^e]_U=0$. On the other hand
   $[p^e]_{G_F}$ is faithfully flat: base change preserves faithful flatness [lem-weil-pbc-
   faithfully-flat-base-change]. Composition does too directly from [def-weil-pbc-faithfully-
   flat-ring-map]: for $R\to S\to B$, tensoring a complex with $B$ is tensoring first with $S$
   and then with $B$ over $S$, and each functor preserves and reflects exactness. The projection
   $U\times_FD\to U$ is faithfully flat: its coordinate map $F[U]\to F[U]\otimes_FF[D]$ is the
   base change along $F\to F[U]$ of $F\to F[D]$, which is flat [lem-weil-pbc-module-over-field-
   flat] and surjective on spectra because $F[D]\neq0$, hence faithfully flat [lem-weil-pbc-
   flat-surjective-spectrum-faithfully-flat]; base change keeps it faithfully flat [lem-weil-
   pbc-faithfully-flat-base-change]. The composite $\operatorname{pr}_U\circ[p^e]_{G_F}$ is
   therefore faithfully flat, and it equals $[p^e]_U\circ\operatorname{pr}_U$, the constant
   homomorphism. Injectivity of its coordinate map [lem-weil-pbc-faithfully-flat-universally-
   injective], applied to the source ring as a module over itself, forces every $a\in F[U]$ to
   equal $\epsilon(a)$, so $U=1$. Thus $G_F\simeq D$ is diagonalizable and $G$ is of
   multiplicative type, exactly the geometric definition. Step 3 splits $G$. This completes the
   strong induction.
   Dependencies: lem-sfb-commutative-diagonalizable-unipotent-product, lem-sfb-affine-normal-
   quotient-geometry, lem-weil-pbc-faithfully-flat-base-change, def-weil-pbc-faithfully-flat-
   ring-map, lem-weil-pbc-faithfully-flat-universally-injective, lem-sfb-unipotent-to-
   multiplicative-trivial, lem-weil-pbc-flat-surjective-spectrum-faithfully-flat, lem-weil-pbc-
   module-over-field-flat.
11. Finally assume the original $G$ is unipotent and use the split series just obtained. Each
   smooth closed term $G_i$ is unipotent: restrict the faithful representation of $G$; the
   restriction is still a closed embedding and its geometric matrices remain unipotent. If a
   quotient $G_i/G_{i+1}$ in this series were $\mathbf G_m$, its quotient homomorphism would be
   trivial by [lem-sfb-unipotent-to-multiplicative-trivial], contradicting its faithful flatness
   onto the nontrivial multiplicative group. Thus every quotient is $\mathbf G_a$. All terms are
   smooth geometrically connected and all quotient maps represent the fppf quotients by
   construction. The group $1$ admits the empty series, also covering a dominant morphism with
   $N=0$.
   Dependencies: lem-sfb-unipotent-to-multiplicative-trivial.
-/
theorem exists_split_series_of_dense_splitTorus {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    (hG : SolvableGroupStructure.IsAlgebraic G)
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    (hsolv : SolvableGroupStructure.IsSolvable G)
    (N : ℕ) (f : (MultiplicativeType.splitTorus k N).X ⟶ G.X)
    (hf : DenseRange f.left.base) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Grp (Over (Spec (.of k)))),
      Nonempty (S 0 ≅ G) ∧ Nonempty (S (Fin.last m) ≅ Grp.trivial _) ∧
      (∀ a : Fin (m + 1), Smooth (S a).X.hom ∧ GeometricallyConnected (S a).X.hom) ∧
      ∀ a : Fin m, ∃ (Q : Grp (Over (Spec (.of k))))
          (j : S a.succ ⟶ S a.castSucc) (q : S a.castSucc ⟶ Q),
        IsClosedSubgroupScheme j.hom.hom ∧ IsNormalSubgroupScheme j.hom.hom ∧
        SolvableGroupStructure.IsFppfQuotient j.hom.hom q ∧
        (Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.additive k)) ∨
          Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.multiplicative k))) ∧
        (SolvableGroupStructure.IsUnipotent G →
          Nonempty (Q ≅ Grp.mk (StandardGroupSchemes.additive k))) := by
  sorry

end AlgebraicGeometry
