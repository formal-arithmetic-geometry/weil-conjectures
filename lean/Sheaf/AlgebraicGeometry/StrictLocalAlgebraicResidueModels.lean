/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.ZetaSeries
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift

/-!
# Strict local models with algebraic residue extensions

Source: Stacks Project, Tags 0F0U and 0F0X, compatible étale models and residue-field control
(blueprint: lem-kun-strict-local-algebraic-residue-models).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The strict localization has nonempty affine finite type models over a separably closed
coefficient field of the prescribed transcendence degree. Their residue extensions over an
affine neighbourhood are algebraic at every point. The cone is a limit in the slice over that
neighbourhood, and its vertex identification respects the canonical morphism to the original
scheme.

Source: Stacks Project, Tag 0F0U, proof and compatible-model footnote; Tag 0F0X, second paragraph
(blueprint: lem-kun-strict-local-algebraic-residue-models).

Proof:
1. Choose a finite-type affine chart $U_0=\operatorname{Spec}A_0$ containing $y$, using the finite
affine cover in [def-weil-finite-type-morphism]. If $\mathfrak p_0$ represents $y$, then
$\kappa(y)=\operatorname{Frac}(A_0/\mathfrak p_0)$ is finitely generated as a field over $K$: the
images of a finite list of $K$-algebra generators generate its fraction field. Apply [lem-weil-
pbc-finitely-generated-field-finite-transcendence-basis] to obtain a finite basis $\bar
t_1,\ldots,\bar t_b$; its size is $b$ by [def-kun-transcendence-degree]. Write these elements as
fractions of images of elements of $A_0$ and invert the product of their denominators, which is
not in $\mathfrak p_0$. This gives a principal affine neighbourhood $U=\operatorname{Spec}A$ of
$y$, still finite type over $K$ (adjoin one inverse), with lifts $t_1,\ldots,t_b\in A$. The map
$R=K[T_1,\ldots,T_b]\to A$, $T_i\mapsto t_i$, is injective: a polynomial in its kernel vanishes on
the algebraically independent $\bar t_i$. The image of $y$ in $\operatorname{Spec}R$ is the
generic point, and its residue field is $F=K(T_1,\ldots,T_b)$.

2. Write $\bar y:\operatorname{Spec}\Omega\to U$ and let $\bar\eta$ be its image in
$\operatorname{Spec}R$. Let $L$ be the separable algebraic closure of $F$ inside $\Omega$, as in
[def-weil-pbc-relative-separable-closure]; it is a separably closed algebraic extension of $F$.
Apply [lem-weil-pbc-etale-local-ring-triples](3) with the identity affine chart of
$\operatorname{Spec}R$. It identifies the pointed-neighbourhood ring colimit with the etale
residue-triple colimit, compatibly with the coprojections. The strict henselization of $R$ at
$\bar\eta$ is therefore $L$: apply [lem-weil-pbc-strict-henselization-triples] with prime $(0)$
and residue field $F$. Its colimit is a local ring whose maximal ideal is $(0)$ and whose residue
field is $L$, so the residue quotient is the ring itself. Apply [lem-weil-pbc-strict-
henselization-functoriality](3) to $U\to\operatorname{Spec}R$ to obtain a unital $K$-algebra map
$h:L\to B=\mathcal O^{\mathrm{sh}}_{Y,\bar y}$ compatible with $R\to A\to B$. The same
functoriality statement (1) makes $B$ a nonzero local ring, so $h$ is injective. To identify the
ring over $U$ with the required ring over $Y$, apply [lem-weil-pbc-etale-local-ring-triples](2) to
the affine chart $U\subset Y$. The affine pointed neighbourhoods factoring through $U$ give the
same ring colimit as all affine pointed neighbourhoods of $Y$; as pointed $U$-neighbourhoods they
are precisely the diagram defining $\mathcal O^{\mathrm{sh}}_{U,\bar y}$. The identification
respects the coprojections, in particular the map from $A$ and the geometric residue embedding.
Thus $B$ and its $A$-structure are the requested ones. Finally, [lem-kun-transcendence-degree-
tower] gives $\operatorname{trdeg}_K L=\operatorname{trdeg}_K F=b$, since $L/F$ is algebraic.

3. Use [def-weil-pbc-strict-henselization-limit] for the two pointed affine schemes
$\operatorname{Spec}R$ and $U$ to choose small filtered ring diagrams $D:I\to\mathbf{CRing}$ and
$E:J\to\mathbf{CRing}$ with $L=\varinjlim_iD_i$ and $B=\varinjlim_jE_j$. The maps $R\to D_i$ and
$A\to E_j$ are etale, and both diagrams and their colimits are over $R$. Choose the representative
subcategories to include the identity neighbourhoods $D_{i_0}=R$ and $E_{j_0}=A$; these are
initial objects in the ring-indexed categories. By [lem-weil-pbc-etale-ring-map-iff-etale-affine],
every $D_i$ is finitely presented over $R$ and every $E_j$ is finitely presented over $A$. In
particular $E_j$ is finite type over $K$ and over $R$, because $A$ is finite type over $K$ and the
image of $R$ contains $K$.

4. Here is the finite-presentation calculation needed for the compatible models. For any finitely
presented $R$-algebra $P=R[X_1,\ldots,X_n]/(f_1,\ldots,f_m)$ and any $R$-algebra map $P\to B$,
[lem-pc-filtered-colimit-commrings-elementwise](1) lifts the images of the $X_r$ into some $E_j$.
Move finitely many representatives to a common object using filteredness. Evaluate the finitely
many relations there; their images in $B$ are zero. Part (2) of the same node and filteredness
move these equalities to one later object, giving an $R$-algebra map $P\to E_k$ factoring the
original map. Two maps from a finitely generated $R$-algebra to stages of $E$ that induce the same
map to $B$ agree after a common refinement: apply part (2) to their finitely many generator images
and combine the finitely many equalities. If the resulting witnesses give different arrows out of
a stage, equalize those arrows using filteredness, so that all equalities use the same transition.
This calculation uses the full small filtered category $J$, not an assumed directed poset.

5. Define a small category $T$ whose objects are triples $\tau=(i,j,\psi)$ with $\psi:D_i\to E_j$
an $R$-algebra map satisfying $\beta_j\psi=h\alpha_i$, where $\alpha_i:D_i\to L$ and
$\beta_j:E_j\to B$ are the coprojections. A morphism to $(i',j',\psi')$ is a pair $(a:i\to
i',c:j\to j')$ with $E(c)\psi=\psi'D(a)$. It is small because $I,J$ are small and each set of ring
maps is a set. It is nonempty: $(i_0,j_0,R\to A)$ is an object. To give a successor of two
triples, first choose a common $i'$ in $I$. Apply the finite-presentation calculation of step 4 to
$D_{i'}\to L\xrightarrow h B$ to obtain a lift into some $E_k$. Choose a common successor in $J$
of $k$ and the two old $j$'s. The composites from each old $D_i$ to that stage and to $B$ agree;
the eventual-equality calculation of step 4, applied to the finite generators of both old $D_i$,
gives a further stage where both compatibility squares commute. For two parallel arrows of
triples, equalize their $I$ components by $i'\to i''$ and their $J$ components by $j'\to j''$.
Lift $D_{i''}\to B$ to a stage of $E$ and then refine $j''$ so that its restriction along
$D_{i'}\to D_{i''}$ agrees with the old $\psi'$; step 4 gives precisely this equality. The
resulting morphism out of the target triple equalizes the original pair in both components. These
are all three filteredness axioms of [def-weil-pbc-category-colimit].

6. For $\tau=(i,j,\psi)$ put $C_\tau=E_j\otimes_{D_i,\psi}L$. A morphism $(a,c)$ of triples
induces $e\otimes\ell\mapsto E(c)(e)\otimes\ell$; the compatibility square makes this well-
defined. The maps $\gamma_\tau:C_\tau\to B$, $e\otimes\ell\mapsto\beta_j(e)h(\ell)$, are
compatible unital maps. The ring $C_\tau$ is finite type over $L$: take any finite set of
$R$-algebra generators of $E_j$ from step 3; their tensors with $1$ generate $C_\tau$ over $L$.
Also $C_\tau$ is nonzero because it maps unitally to the nonzero ring $B$. More explicitly,
composing $\gamma_\tau$ with the residue map from $B$ to its residue field gives a unital map to a
field; its kernel is a proper prime ideal of $C_\tau$, since a product mapping to zero in a field
has a factor mapping to zero. This prime is a point of $V_\tau$, proving nonemptiness without
invoking existence of maximal ideals. All these maps preserve the given $A$-algebra structures,
hence their spectra are $K$-morphisms over $U$.

7. We verify the colimit, including its universal property, rather than assuming that the $C_\tau$
are subalgebras of $B$. Let $m_\tau:C_\tau\to M$ be any compatible cocone of commutative rings.
For every $j$, $(i_0,j,R\to E_j)$ is a triple, so $e\mapsto m_{(i_0,j)}(e\otimes1)$ defines
compatible maps $E_j\to M$, and hence a unique ring map $f:B\to M$. The triple $(i_0,j_0)$ maps to
every triple, so all restrictions $\ell\mapsto m_\tau(1\otimes\ell)$ are the same map $g:L\to M$.
For any $\ell\in L$, [lem-pc-filtered-colimit-commrings-elementwise](1) gives $d\in D_i$ with
$\alpha_i(d)=\ell$; step 4 supplies a triple $(i,j,\psi)$. The tensor relation
$\psi(d)\otimes1=1\otimes\alpha_i(d)$ then gives $f(h(\ell))=g(\ell)$. There is a morphism
$(i_0,j)\to(i,j,\psi)$, so $m_\tau(e\otimes1)=f(\beta_j(e))$. Since $C_\tau$ is generated as a
ring by these elements and $1\otimes L$, these two equations give $m_\tau=f\gamma_\tau$.
Uniqueness follows from the colimit presentation $B=\varinjlim E_j$. Thus $B=\varinjlim_T C_\tau$
as rings and as $A$-algebras. By [lem-weil-pbc-spec-small-colimit-limit], the compatible maps from
$S=\operatorname{Spec}B$ to $V_\tau=\operatorname{Spec}C_\tau$ are a limit cone in schemes; the
compatibility with $A$ makes it a limit over $U$ as well.

8. Fix a prime $q$ of $C_\tau$ and let $w$ and $u$ be its contractions to $E_j$ and $A$,
respectively. Since $A\to E_j$ is etale, [lem-weil-pbc-etale-algebra-residue-field-separable]
gives a finite separable extension $\kappa(w)/\kappa(u)$. Let $p_i$ be the kernel of $D_i\to L$.
This is also the contraction of $w$ to $D_i$: in $C_\tau/q$ the two images of $D_i$ agree, and the
unital map from the field $L$ to $\kappa(q)$ is injective. The induced field embeddings
$\kappa(p_i)\to L$ and $\kappa(p_i)\to\kappa(w)$ are therefore compatible in $\kappa(q)$. Since
$R\to L$ is injective, $p_i$ contracts to $(0)$ in $R$. Apply [lem-weil-pbc-etale-algebra-residue-
field-separable] to $R\to D_i$ to obtain $\kappa(p_i)/F$ finite separable. In particular
$L/\kappa(p_i)$ is algebraic: every polynomial witnessing algebraicity over $F$ also witnesses
algebraicity over this intermediate field. The field $\kappa(q)$ is generated by the images of
$\kappa(w)$ and $L$, because $C_\tau$ is generated by $E_j$ and $L$ and
$\kappa(q)=\operatorname{Frac}(C_\tau/q)$. Consequently $\kappa(q)/\kappa(w)$ is algebraic.
Explicitly, any one of its elements is a rational expression in finitely many elements of $L$ with
coefficients in $\kappa(w)$; those elements are algebraic over $\kappa(w)$, so their successive
simple adjunctions are finite-dimensional fields (use their monic minimal polynomials). The
expression belongs to this finite extension. As $\kappa(w)/\kappa(u)$ is finite, the same element
is algebraic over $\kappa(u)$: the finite-dimensional tower is finite-dimensional, and its powers
are linearly dependent. This proves the required residue algebraicity for every point, without a
lifting-to-$S$ assumption.

9. The schemes $V_\tau$ are nonempty by step 6 and are affine and finite type over $L$. Their
inverse index category is the small cofiltered category $T^{\mathrm{op}}$ by step 5. Their
transition maps are affine by [lem-weil-pbc-morphism-affine-schemes-affine], since both their
source and target are affine. Thus steps 2, 6, 7 and 8 establish every asserted clause, including
the limit over $U$ and every residue extension. When $b=0$ use $R=F=K$ and the empty list of
$t_i$; all the constructions and arguments still apply.
-/
theorem exists_strictLocal_algebraicResidue_models
    {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧ IsAffineOpen U ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
        Algebra.trdeg K L =
          @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
            (((Y ↘ Spec (.of K)).residueFieldAlgebraMap
              (s (IsLocalRing.closedPoint Ω))).toAlgebra) ∧
        ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
          (D : I ⥤ Over U.toScheme)
          (p : ∀ i : I, (D.obj i).left ⟶ Spec (.of L))
          (c : Cone D) (e : strictHenselizationScheme s ≅ c.pt.left),
          Nonempty (IsLimit c) ∧
          e.hom ≫ c.pt.hom ≫ U.ι = strictHenselizationStructuralMap s ∧
          (∀ i : I, Nonempty (D.obj i).left ∧ IsAffine (D.obj i).left ∧
            LocallyOfFiniteType (p i) ∧ QuasiCompact (p i) ∧
            (D.obj i).hom ≫ U.ι ≫ (Y ↘ Spec (.of K)) =
              p i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
          (∀ (i j : I) (a : i ⟶ j), IsAffineHom (D.map a).left) ∧
          ∀ (i : I) (v : (D.obj i).left),
            @Algebra.IsAlgebraic (U.toScheme.residueField ((D.obj i).hom v))
              ((D.obj i).left.residueField v) _ _
              (((D.obj i).hom.residueFieldMap v).hom.toAlgebra) := by
  sorry

end AlgebraicGeometry.Scheme
