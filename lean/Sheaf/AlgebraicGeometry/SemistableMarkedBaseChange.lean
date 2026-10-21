/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Sheaf.AlgebraicGeometry.NagataMorphismEqEventually
import Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage
import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import WeilConjectures.RingTheory.FlatLocalCompletionIso
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension

/-! # Base change of semistable multipointed curves

Source: Temkin, Stable Modification of Relative Curves, §1.2, pp. 2–3; Stacks 0C59 and 0C5B
(blueprint: lem-trf-semistable-marked-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.MultipointedPair

/-- Multipointed curves survive arbitrary base change. Source: Temkin §1.2;
Stacks 0C5B (blueprint: lem-trf-semistable-marked-base-change).

Proof plan from the DAG:
1. Put $X'=X\times_TT'$ and $D'=D\times_TT'$. Apply [lem-weil-pbc-flat-morphism-base-change] and
clause (3) of [lem-weil-pbc-qcqs-morphism-permanence] to both structural morphisms. They remain
flat and of finite presentation. The marking $D'\to X'$ is the base change of $D\to X$ along
$X'\to X$, by the universal property of the fibre product, and is a closed immersion by
[lem-weil-pbc-closed-immersion-base-change].
2. For either structural morphism $Z\to T$, write $d=1$ for $Z=X$ and $d=0$ for $Z=D$. Its fibres
are finite type over fields and hence Noetherian by [lem-weil-pbc-finite-type-over-noetherian].
Pure dimension $d$ implies constant local topological dimension $d$ by
[lem-sbc-equidimensional-open-local-dimension], with the whole fibre as the open. For every $z'\in
Z\times_TT'$, [lem-sc-fibre-dimension-after-base-change] identifies the local dimension of the
fibre at $z'$ with that at its image $z$. The new fibre is also finite type and Noetherian. Apply
[lem-sbc-constant-local-dimension-components] to this whole fibre to recover pure dimension $d$.
Empty fibres satisfy this assertion vacuously. Thus Step 1 gives a multipointed curve for every
base change.
3. Under the extra integral-base hypothesis, the generic-point condition induces a field map
$\kappa(\eta_T)\to\kappa(\eta_{T'})$. Associating the fibre products identifies $X'_{\eta_{T'}}$
and $D'_{\eta_{T'}}$ with the scalar extensions of $X_{\eta_T}$ and $D_{\eta_T}$ along this map.
Clause (2) of [lem-pc-proper-base-change] preserves smoothness of the first, and
[lem-weil-pbc-etale-scheme-base-change] preserves etaleness of the second. This proves precisely
the generic assertion, without using properness.
4. Now take the semistable source $Y\to T$. First verify the hypotheses of
[lem-trf-nodal-family-fitting-singular] and [lem-trf-nodal-family-etale-local-model], which
quantify over every algebraically closed field, whereas semistability is a condition on the chosen
geometric fibres $Y_{\bar t}$, $\bar t:\operatorname{Spec}\overline{\kappa(t)}\to T$. Let
$\operatorname{Spec}\Omega\to T$ be any geometric point, over $t\in T$. By
[lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] the chosen algebraic closure
$\overline{\kappa(t)}$ embeds into $\Omega$ over $\kappa(t)$, and associating fibre products
identifies $Y\times_T\operatorname{Spec}\Omega$ with the base change of $Y_{\bar t}$ to $\Omega$.
The scheme $Y_{\bar t}$ is locally of finite presentation, hence locally of finite type, over
$\overline{\kappa(t)}$ by clause (3) of [lem-weil-pbc-qcqs-morphism-permanence], and its nonsmooth
points have completed local ring $\overline{\kappa(t)}[[u,v]]/(uv)$; so
[lem-trf-node-algebraically-closed-extension] gives completed local ring $\Omega[[u,v]]/(uv)$ at
every nonsmooth point of $Y_\Omega$. Step 2, applied to $\operatorname{Spec}\Omega\to T$, makes
$Y_\Omega$ empty or pure of dimension $1$. Now apply [lem-trf-nodal-family-fitting-singular]. Its
remaining hypotheses are flatness and local finite presentation; it imposes no properness or
Noetherian condition on $T$. It supplies an open relative smooth locus $U\subset Y$ and says that
the nonsmooth locus after every base change is the inverse image of $Y\setminus U$. Taking
complements gives exactly $U'=U\times_TT'$, including the assertion that the relative smooth locus
commutes with base change.
5. We will use completed local rings only on schemes locally of finite type over an algebraically
closed field $\Omega$. For an etale map between such schemes and a closed $\Omega$-point upstairs,
its image is also a rational closed point, and the residue-field maps are identities on $\Omega$,
by [lem-weil-pbc-closed-point-residue-field-base] (or by evaluation of the coordinates in affine
charts). The local rings are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to
affine charts. Etaleness gives flatness; [lem-weil-pbc-etale-prime-generates-maximal] gives
$\mathfrak m_A B=\mathfrak m_B$. Consequently [lem-weil-pbc-flat-local-completion-iso] identifies
the completed local rings. This is a direct application of that lemma with identical residue
fields.
6. Fix a singular closed point $y'$ on a geometric fibre of $Y'=Y\times_TT'$, over an
algebraically closed field $\Omega$. By Step 4 its image $y\in Y$ is nonsmooth. Apply
[lem-trf-nodal-family-etale-local-model] at $y$, whose hypotheses for every algebraically closed
field were verified in Step 4, obtaining etale maps $U_0\to Y$, $V\to T$ and $U_0\to
W=\operatorname{Spec}_V\mathcal O_V[u,v]/(uv-h)$ and a point of $U_0$ over $y$. Pull these back to
the geometric point under consideration, using [lem-weil-pbc-etale-scheme-base-change]. The fibre
of $U_0\to Y$ over $y'$ is nonempty: the original nonempty etale fibre is a disjoint union of
finite separable field spectra by [lem-trf-unramified-field-fibre-decomposition], and tensoring a
nonzero vector space with a field extension is nonzero. Over $\Omega$ its points are rational by
the same decomposition. A chosen lift therefore maps to a rational point of the plane curve
$uv=a$, where $a$ is the image of $h$ in $\Omega$.
7. The lift in Step 6 cannot be smooth over $\Omega$ when $y'$ is nonsmooth. Indeed an open smooth
neighbourhood of the lift has open image under its etale map, by [lem-weil-pbc-flat-lfp-open]; its
map onto that image is flat, surjective and locally finitely presented.
[lem-sbc-smooth-flat-surjective-source-descent] would make that image smooth. On $uv=a$, away from
$u=v=0$ one coordinate is invertible and the other is determined, so that this open is an open of
$\mathbf A^1_\Omega$; it is smooth of dimension one. Smoothness of its etale inverse image follows
from [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] and
[lem-sbc-smooth-relative-dimension-permanence]. Hence the point of $uv=a$ from Step 6 must be the
origin, and $a=0$.
8. At that origin, the completion of $\Omega[u,v]_{(u,v)}$ is $\Omega[[u,v]]$: compatible
polynomial residues modulo $(u,v)^n$ specify exactly one coefficient of each monomial, and
localization does not change these quotients since polynomials with nonzero constant term are
units in them. [lem-weil-pbc-local-completion-quotient] therefore gives the completion of
$\Omega[u,v]_{(u,v)}/(uv)$ as $\Omega[[u,v]]/(uv)$. Apply Step 5 to both etale arrows from the
lifted point, one to $Y'_\Omega$ and the other to the plane-curve model. The completed local ring
at $y'$ is thus $\Omega[[u,v]]/(uv)$. Steps 1--2 give flatness, finite presentation and pure
dimension for $Y'$ and $E'$. Etaleness of $E'\to T'$ follows from
[lem-weil-pbc-etale-scheme-base-change], and $E'\subset U'$ from Step 4. This proves all the
semistability clauses.
9. To compare the chosen algebraic-closure fibres in the definition with larger algebraically
closed fibres, let $k\subset L$ be algebraically closed fields and let $C$ be a finite-type
$k$-scheme. By [lem-weil-pbc-algebraic-over-algebraically-closed-subfield], $k$ is algebraically
closed in $L$; [lem-zl-field-extension-algebraically-closed-geometric] makes
$\operatorname{Spec}L$ geometrically irreducible over $k$.
[lem-sc-product-irreducible-components-bijection] gives a bijection of irreducible components
after scalar extension, both for $C$ and separately for each reduced component $R\subset C$. In
particular each $R_L$ is irreducible: it is nonempty and has exactly one irreducible component.
The closed sets $|R_L|$ cover $C_L$, and none is contained in another since projection is
surjective on each $R$. This surjectivity follows affine-locally from
[lem-weil-pbc-field-extension-base-change-faithfully-flat] and
[lem-weil-pbc-faithfully-flat-surjective-spectrum]. Since $k$ is perfect,
[lem-kun-geometric-reduced-perfect] says $R_L$ is reduced. Thus $R\mapsto R_L$ identifies the
reduced component schemes themselves.
10. For a reduced component $R$ of such a finite-type scheme, suppose $R_L\cong\mathbf P^1_L$. The
component $R$ is closed in a finite-type Noetherian scheme, hence quasi-compact and
quasi-separated (intersections of affine opens are Noetherian opens and quasi-compact). Both $R$
and $\mathbf P^1_k$ are of finite presentation over the field $k$ (use finite-type Noetherian
affine charts). Write $L$ as the directed union of its finitely generated $k$-subalgebras. Apply
[lemma-nagata-morphism-descends] to the isomorphism and its inverse, then
[def-nagata-morphism-equality-stage] and [lemma-nagata-morphism-eq-eventually] to the two inverse
equations. At one common stage $A\subset L$ this gives inverse $A$-morphisms
$R_A\rightleftarrows\mathbf P^1_A$. The nonzero finite-type $k$-algebra $A$ has a maximal ideal;
[lem-weil-pbc-closed-point-residue-field-base] identifies its residue field with $k$. Pulling the
two inverse morphisms back to this point gives $R\cong\mathbf P^1_k$. Conversely such an
isomorphism pulls back to one over $L$, with projective-space base change supplied by
[lemma-nagata-projective-space-base-change-pullback]. This uses only the two cited
morphism-descent assertions, their equality assertion, and specialization.
11. For a semistable marked geometric curve $(C,F)$ over $k$, its marking and its singular
subscheme are finite disjoint unions of $k$-points: use
[lem-trf-unramified-field-fibre-decomposition] for the etale marking and for the unramified
singular subscheme supplied by [lem-trf-nodal-family-fitting-singular], applied to
$C\to\operatorname{Spec}k$. Its hypotheses hold for every algebraically closed extension $\Omega$
of $k$: $C_\Omega$ is pure of dimension one by Step 2 and nodal by
[lem-trf-node-algebraically-closed-extension]. They are quasi-compact closed subschemes of the
finite-type Noetherian curve, so the disjoint decompositions have finitely many terms. Scalar
extension replaces each $\operatorname{Spec}k$ by one $\operatorname{Spec}L$. Step 4 identifies
the pulled-back singular locus, and a marking is pulled back as a closed subscheme. Therefore on
corresponding components $R,R_L$ the number of distinct points in the union of marking and
singular locus is unchanged. Intersections are fibre products of the same closed subschemes, so a
given rational point belongs to $R$ if and only if its unique lift belongs to $R_L$. This counts
points on the component, as distinct points of the component; it does not count branches of the
normalization.
12. For a morphism of the geometric pairs and a corresponding component $R$, contraction is
unchanged by $k\subset L$. If $R\cong\mathbf P^1_k$ and its image is a point, that point is
$k$-rational (evaluate at a rational point of $R$); the morphism is constant. Indeed choose an
affine neighbourhood $\operatorname{Spec}B$ of its image. On the two affine charts of
[def-sc-p1-standard] its maps are ring maps $B\to k[t]$ and $B\to k[t^{-1}]$, by
[def-weil-affine-spectrum]. They agree in $k[t,t^{-1}]$, whose two subrings have intersection $k$.
Thus both chart morphisms factor through the same rational point and glue to the constant
morphism. Its scalar extension is constant too. Conversely if $R_L$ is contracted, projection of
its image and the surjectivity $R_L\to R$ from Step 9 show that the image of $R$ has one point.
Together with Step 10 and Step 11, every exceptional contracted $\mathbf P^1$ component after
extension would give exactly such a component before extension, with the same number of special
points. Thus a fibre with no exceptional component remains without one.
13. Let $t'\in T'$ map to $t\in T$. Choose an embedding of an algebraic closure $k$ of $\kappa(t)$
into an algebraic closure $L$ of $\kappa(t')$, extending the residue-field map;
[lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] supplies it. Associating fibre
products identifies the geometric pair and its morphism over $t'$ with the scalar extension to $L$
of the geometric pair and morphism over $t$. Steps 9--12 show that its forbidden-component
predicate cannot appear. This proves stability under arbitrary base change, for exactly the
geometric stability condition in the statement.
14. Finally let $(T_i)$ be an open cover of $T$. Flatness and local finite presentation are
pointwise affine-local conditions. Quasi-compactness is local on the target by
[lem-pc-quasi-compact-local-on-target]; apply the same lemma to the diagonal to check
quasi-separatedness locally, using that an open cover of $T$ pulls back to an open cover of the
diagonal target. Thus finite presentation is local on $T$. Closed immersion and etaleness are
local on the target by [lem-weil-pbc-closed-finite-etale-zariski-local], applying closed-immersion
locality over the inverse-image cover of the curve. Every point of $T$ belongs to a $T_i$, and its
fibre, marking and fibre morphism are identical to those of the restricted pair. Hence pure
dimensions, nodes and the no-exceptional-component condition are local as well; the marking's
inclusion in the smooth locus is pointwise. These arguments allow empty marking and nonproper,
nonseparated curves. They assert nothing about schematic density or preservation of
modifications. -/
theorem isMultipointed_baseChange {T T' : Scheme.{u}} (P : MultipointedPair T)
    (g : T' ⟶ T) (hP : P.IsMultipointed) : (P.baseChange g).IsMultipointed := sorry

/-- The smooth generic curve and etale generic marking survive a generic-point-preserving
map of integral bases. Source: Temkin §1.2
(blueprint: lem-trf-semistable-marked-base-change).
Proof: the generic-point condition induces the residue-field map; associate fibre products,
then apply smooth and etale base change (DAG Step 3). -/
theorem generic_smooth_etale_baseChange {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (P : MultipointedPair T) (hP : P.IsMultipointed) (g : T' ⟶ T)
    (η : T) (η' : T') (hη : IsGenericPoint η Set.univ)
    (hη' : IsGenericPoint η' Set.univ) (hg : g η' = η)
    (hC : Smooth (P.curve.hom.fiberToSpecResidueField η))
    (hD : Etale (P.marking.hom.fiberToSpecResidueField η)) :
    Smooth ((P.baseChange g).curve.hom.fiberToSpecResidueField η') ∧
      Etale ((P.baseChange g).marking.hom.fiberToSpecResidueField η') := sorry

/-- Every semistability clause survives arbitrary base change. Source: Temkin §1.2,
Stacks 0C59 and 0C5B (blueprint: lem-trf-semistable-marked-base-change).
Proof: Steps 1–2 preserve the structural properties. Step 4 passes from chosen closures to
arbitrary algebraically closed fields using nodal scalar extension, and identifies the singular
locus by its Fitting ideal. Steps 5–8 use the etale local model uv=a, force a=0 at a nonsmooth
point, and identify its scalar-compatible completed local ring. Etale base change preserves the
marking, which stays in the pulled-back smooth locus. -/
theorem isSemistable_baseChange {T T' : Scheme.{u}} (P : MultipointedPair T)
    (g : T' ⟶ T) (hP : P.IsSemistable) : (P.baseChange g).IsSemistable := sorry

/-- The relative smooth locus of a semistable pair pulls back to the relative smooth locus.
It is written as its underlying set of formally smooth stalk maps; local finite presentation
is supplied by semistability. Source: Stacks 0C59 and 0C5B
(blueprint: lem-trf-semistable-marked-base-change).
Proof: apply Step 4: formation of the Fitting singular locus commutes with base change;
take complements. -/
theorem smoothLocus_baseChange {T T' : Scheme.{u}} (P : MultipointedPair T)
    (g : T' ⟶ T) (hP : P.IsSemistable) :
    {x | (((P.baseChange g).curve.hom).stalkMap x).hom.FormallySmooth} =
      (pullback.fst P.curve.hom g) ⁻¹'
        {x | (P.curve.hom.stalkMap x).hom.FormallySmooth} := sorry

/-- Multipointedness and semistability are local for an arbitrary open cover of the base.
Source: Temkin §1.2 and Stacks 0C59
(blueprint: lem-trf-semistable-marked-base-change).
Proof: Step 14 checks flatness and local finite presentation locally, quasi-compactness for the
map and diagonal locally on the target, and closed immersions and etaleness locally. Fibres
and their markings identify over an open neighbourhood of each base point, so pure dimension,
nodality and avoidance of the nonsmooth locus are local as well. -/
theorem isMultipointed_isSemistable_iff_openCover {T : Scheme.{u}} (P : MultipointedPair T)
    (I : Type w) (U : I → T.Opens) (hU : ∀ t : T, ∃ i : I, t ∈ U i) :
    (P.IsMultipointed ↔ ∀ i : I, (P.baseChange (U i).ι).IsMultipointed) ∧
      (P.IsSemistable ↔ ∀ i : I, (P.baseChange (U i).ι).IsSemistable) := sorry

/-- Geometric stability of a compatible pair morphism is preserved by arbitrary base change.
Source: Temkin §1.2 (blueprint: lem-trf-semistable-marked-base-change).
Proof: Steps 9–10 identify reduced components over algebraically closed field extensions and
show that being a projective line descends, by approximation of the isomorphism and inverse
and specialization at a rational closed point. Step 11 identifies the marking and singular
points and their incidence on components, counting distinct points rather than branches.
Step 12 preserves contraction, using constants on the two affine charts of the projective line.
Step 13 embeds the chosen residue-field closures and associates fibre products. Thus no
forbidden component can appear. This asserts no preservation of modifications. -/
theorem geometricStability_baseChange {T T' : Scheme.{u}} (P Q : MultipointedPair T)
    (hP : P.IsSemistable) (hQ : Q.IsMultipointed) (f : P.curve ⟶ Q.curve)
    (d : P.marking ⟶ Q.marking) (hcompat : P.inclusion ≫ f = d ≫ Q.inclusion)
    (g : T' ⟶ T) (hf : P.HasGeometricStability Q f) :
    (P.baseChange g).HasGeometricStability (Q.baseChange g) ((Over.pullback g).map f) := sorry

/-- Geometric stability is local on an arbitrary open cover of the base.
Source: Temkin §1.2 (blueprint: lem-trf-semistable-marked-base-change).
Proof: Step 14 identifies each geometric fibre, the morphism and marking with those of a
restriction to any base open containing its image. The exceptional-component condition is
therefore equivalent on the cover. -/
theorem geometricStability_iff_openCover {T : Scheme.{u}} (P Q : MultipointedPair T)
    (hP : P.IsSemistable) (hQ : Q.IsMultipointed) (f : P.curve ⟶ Q.curve)
    (d : P.marking ⟶ Q.marking) (hcompat : P.inclusion ≫ f = d ≫ Q.inclusion)
    (I : Type w) (U : I → T.Opens) (hU : ∀ t : T, ∃ i : I, t ∈ U i) :
    P.HasGeometricStability Q f ↔ ∀ i : I,
      (P.baseChange (U i).ι).HasGeometricStability (Q.baseChange (U i).ι)
        ((Over.pullback (U i).ι).map f) := sorry

end AlgebraicGeometry.MultipointedPair
