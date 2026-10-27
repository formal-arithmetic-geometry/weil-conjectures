/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality
import Sheaf.AlgebraicGeometry.ProperStability
import WeilConjectures.AlgebraicGeometry.ChowLemma
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.FieldTheory.FiniteSeparableClosure
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility

/-!
# Equivariant curve-pencil preparation over a field

Source: A. J. de Jong, Families of curves and alterations (1997), Lemma 5.2,
printed pp. 612–613, field-base case, with equivariant Chow preparation
(blueprint: lem-sfb-equivariant-curve-pencil).
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A normal proper geometrically integral variety of dimension at least two admits
an equivariant H-projective birational modification with an H-projective pencil whose
base is normal projective geometrically integral of dimension one less and whose generic
fibre is a geometrically integral curve.

The field action uses inverse elements in the compatibility equation because `Spec`
is contravariant. Neither group action is required to be faithful. Normality is expressed
on every local ring. Birationality includes both the dense-open isomorphism and
bijectivity of the actual stalk map at the generic point; its source is the generic
stalk of the target because the displayed equality identifies the generic points.

Source: de Jong (1997), Lemma 5.2, pp. 612–613, and the equivariant Chow preparation
in the node's proof (blueprint: lem-sfb-equivariant-curve-pencil).

Proof:
1. Put $E=k(X)$. A nonempty affine open of $X$ has a finitely generated coordinate domain and
   fraction field $E$, so $E/k$ is finitely generated. The dimension formula gives
   $\operatorname{trdeg}_kE=d$. The given geometric integrality passes to this affine open and
   then to $\operatorname{Spec}E$ by the affine function-field transfer lemma. Hence $E\otimes_kK$
   is a domain for every field extension $K/k$. Each automorphism of $X$ induces an automorphism
   of its generic local field, compatibly with the action on $k$. Apply the invariant-parameter
   lemma to obtain $t_1,\ldots,t_d\in E^H$ with $E/k(t_1,\ldots,t_d)$ finite separable.
   Uses: lem-sc-integral-function-field-affine-fraction, lem-sc-closed-irreducible-dimension-
   trdeg, lem-sbc-field-fraction-ring-geometric-integrality, lem-sfb-invariant-separating-
   parameters.
2. Set $k_0=k^H$. Apply the finite-faithful-action theorem to the image of $H$ in
   $\operatorname{Aut}(k)$, rather than to $H$ itself: $k/k_0$ is finite Galois. Thus
   $\operatorname{Spec}k\to\operatorname{Spec}k_0$ is finite, hence proper. Composition makes $X$
   proper of finite type over $k_0$; it is Noetherian, since a field is Noetherian (its only
   ideals are $0$ and the whole field). All elements of $H$ are now $k_0$-automorphisms. Apply
   Noetherian Chow to obtain $p:M\to X$, proper surjective and an isomorphism over a dense open
   $U$, with an immersion $M\to\mathbf P^n_{k_0}$. This immersion is proper because $M$ is proper
   over $k_0$ and projective space is separated, hence it is closed.
   Uses: lem-wf-finite-field-action-fixed-degree, def-weil-finite-integral-morphism, lem-weil-pbc-
   finite-proper, lem-kun-proper-stability, lem-weil-pbc-finite-type-over-noetherian, lem-weil-
   pbc-chow-noetherian, lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-immersion-
   closed.
3. Replace $M$ by the scheme-theoretic closure of $p^{-1}U\simeq U$. It is integral: on every
   ambient affine open meeting the closure, the defining kernel is the kernel of a map to sections
   on a nonempty open of the integral scheme $U$, which inject into $E$; that kernel is prime. The
   closure is a closed subscheme of the original projective $M$, remains proper over $X$, and
   remains isomorphic to $U$ over $U$. Its image is closed and contains the dense open $U$, hence
   is all of $X$. We keep the names $M,p$. All opens in this construction are quasi-compact since
   the ambient schemes are Noetherian, so the scheme-image kernel assertions apply.
   Uses: lem-weil-pbc-scheme-image-qc-kernel, lemma-nagata-scheme-image-ideal-qc, lem-sc-integral-
   scheme-stalks-in-function-field, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-
   pbc-closed-immersion-comp, lem-kun-projective-implies-proper, lem-kun-proper-stability.
4. For $h\in H$ give the $h$-indexed copy of $M$ the map $c_h=h\circ p:M\to X$, and form their
   fibre product $D=\prod_{h\in H,X}(M,c_h)$. It is a closed subscheme of $Q=\prod_{h\in H,k_0}M$:
   the equations $c_h(m_h)=c_1(m_1)$ are pullbacks of the closed diagonal of the separated
   $k_0$-scheme $X$. By repeated Segre embedding, $Q$ and then $D$ are projective over $k_0$. Put
   $U_0=\bigcap_hh(U)$. It is a dense invariant open. The map $D\to X$ has inverse image $U_0$
   isomorphic to $U_0$, since over $x\in U_0$ its $h$-coordinate is uniquely $p^{-1}(h^{-1}x)$;
   this identity also holds functorially as an inverse of isomorphisms over $U_0$.
   Uses: lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp, lem-chow-
   segre, def-weil-proper-morphism, def-pc-fibre-product.
5. Define $a_b$ on $Q$ by $(a_bm)_h=m_{b^{-1}h}$. If the common image of $(m_h)$ in $X$ is $x$,
   then $c_h(m_{b^{-1}h})=h(b^{-1}h)^{-1}x=bx$. Thus $a_b$ preserves $D$, induces $b$ on its map
   to $X$, and $a_ba_c=a_{bc}$. Let $C$ be the scheme-theoretic closure of $U_0\subset D$. The
   affine kernel description shows that these automorphisms preserve its ideal: pulling back
   functions carries functions restricting to zero on $U_0$ to functions restricting to zero on
   the same invariant open. Consequently $C$ has an $H$-action. The same prime-kernel argument as
   in Step 3 makes $C$ integral, projective over $k_0$, and birational over $X$.
   Uses: lem-weil-pbc-scheme-image-qc-kernel, lemma-nagata-scheme-image-ideal-qc, lem-sc-integral-
   scheme-stalks-in-function-field, lem-weil-pbc-closed-immersion-comp.
6. Normalize $C$ in $E$, giving $C^\nu\to C$, finite surjective birational. The normalization is
   normal integral by its affine integral-closure construction and the residue-field normalization
   lemma. The action lifts explicitly: an isomorphism of affine domains induced by $b$ extends to
   their fraction fields and takes a root of a monic polynomial to a root of the polynomial with
   transformed coefficients. It therefore takes one integral closure isomorphically to the other.
   These isomorphisms restrict on overlaps (the normalization commutes with open restriction), and
   satisfy the group law because their maps on subrings of $E$ do. The composite $p_1:C^\nu\to X$
   is equivariant and is an isomorphism on $U_0$: $U_0$ is normal since $X$ is normal.
   Uses: lem-sc-normalization-exists, lem-weil-pbc-normalization-in-residue-field-extension, def-
   sc-normalization, lem-weil-pbc-reduced-algebraic-normalization-field-change.
7. The projective embedding of $C$ over $k_0$ supplies an ample invertible sheaf. The finite map
   $C^\nu\to C$ is projective in the bundle convention, and the ample-base conversion makes it
   H-projective. Composition makes $C^\nu$ projective over $k_0$. For a projective $k_0$-scheme
   $V$ with a map to a separated $k_0$-scheme $B$, the graph $V\to V\times_{k_0}B$ is closed (it
   is the pullback of the closed diagonal of $B$); base-changing a closed embedding $V\to\mathbf
   P^N_{k_0}$ and composing gives a closed embedding $V\to\mathbf P^N_B$. Apply this first with
   $B=\operatorname{Spec}k$, and then with $B=X$. Thus $C^\nu$ is projective over $k$ and $p_1$ is
   H-projective.
   Uses: lem-pc-very-ample-ample, lem-trf-finite-projective-bundle, lem-trf-projective-bundle-to-
   h-projective, lem-trf-h-projective-composition, lem-weil-pbc-closed-immersion-base-change, lem-
   weil-pbc-closed-immersion-comp, def-weil-proper-morphism.
8. Write $P=\mathbf P^{d-1}_k$ and $F=k(t_1,\ldots,t_{d-1})$. The standard affine chart has
   polynomial coordinates, so $k(P)=F$ via these parameters. On a nonempty affine of $C^\nu$,
   clear the finitely many denominators of the $t_i$ to define $r=[1:t_1:\cdots:t_{d-1}]$ on a
   dense open. Its generic map is dominant by algebraic independence. Let $H$ act on $P$ by its
   action on $k$ and by fixing the homogeneous coordinates. The identities $h(t_i)=t_i$ make this
   rational map equivariant; intersect its finitely many translated domains to obtain an invariant
   dense open $V$ on which it is an equivariant morphism.
   Uses: lem-weil-pbc-projective-space-standard-charts, lem-sc-integral-function-field-affine-
   fraction, def-weil-affine-spectrum.
9. Let $Z$ be the scheme-theoretic closure of the graph of $r|_V$ in $C^\nu\times_kP$. It is
   integral by the prime-kernel argument of Step 3 and has function field $E$. The partial-section
   image lemma makes $Z\to C^\nu$ an isomorphism over $V$. Equivariance of the graph preserves its
   kernel ideal as in Step 5, so $H$ acts on $Z$. The product is projective over $k$ by Segre;
   hence $Z$ is projective over $k$. Normalize $Z$ in $E$ and call the result $X'$. Finiteness,
   normality, surjectivity, and the lifted action follow exactly from the normalization statements
   and affine monic-polynomial calculation of Step 6. Since $V$ is normal, normalization preserves
   its open graph. The ample-base argument of Step 7 makes $X'$ projective over $k$.
   Uses: lem-weil-pbc-scheme-image-qc-kernel, lemma-nagata-scheme-image-ideal-qc, lemma-nagata-
   scheme-image-partial-section, lem-sc-integral-scheme-stalks-in-function-field, lem-chow-segre,
   lem-sc-normalization-exists, lem-weil-pbc-normalization-in-residue-field-extension, def-sc-
   normalization, lem-weil-pbc-reduced-algebraic-normalization-field-change, lem-pc-very-ample-
   ample, lem-trf-finite-projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-
   projective-composition.
10. Let $\pi:X'\to C^\nu\to X$ and $r':X'\to P$ be the resulting morphisms. Both are equivariant
   and H-projective: use the graph-embedding argument of Step 7 for the projective $k$-scheme $X'$
   and the separated $k$-targets $X,P$. They are proper. Their maps on function fields are
   respectively the identity of $E$ and the inclusion $F\subseteq E$, so they are dominant. The
   proper image of $\pi$ is closed and dense, hence all of $X$. There is a dense open of $X$ over
   which both modifications are isomorphisms: intersect $U_0$ with the image in $X$ of $V\cap
   p_1^{-1}U_0$. This proves the specified birationality of $\pi$.
   Uses: lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp, def-weil-
   proper-morphism, lem-kun-projective-implies-proper.
11. The scheme $X'$ is geometrically integral over $k$. Indeed every nonempty affine open
   $A\subseteq X'$ is integral with fraction field $E$. Compare it with a nonempty affine open of
   the original geometrically integral $X$, whose fraction field is the same $E$. The affine
   transfer lemma gives geometric integrality of $A$. For every extension $K/k$ these affine opens
   cover $X'_K$ by integral schemes; any two have nonempty intersection after base change, since
   their intersection in the integral $X'$ is nonempty and base extension of a nonzero $k$-algebra
   to a field is nonzero (a vector-space basis remains a basis). Thus $X'_K$ is reduced and
   irreducible, hence integral.
   Uses: lem-sbc-field-fraction-ring-geometric-integrality, lem-sc-integral-function-field-affine-
   fraction, def-pc-geometrically-irreducible.
12. Apply the normal Stein-factor lemma to $r':X'\to P$. It gives
   $X'\xrightarrow{g}Y\xrightarrow{q}P$, with $Y$ normal integral, $q$ finite dominant, $g$
   proper, and $L=k(Y)$ the algebraic closure of $F$ in $E$. Both $Y$ and $X'$ are of finite type
   over $k$. Since $P$ is projective over $k$, it has an ample sheaf; the finite-projective and
   ample-base statements make $q$ H-projective. Composition makes $Y$ projective over $k$, hence
   proper. Finally the graph embedding of the projective $k$-scheme $X'$ into projective space
   over separated $Y$ makes $g$ H-projective. It is dominant since $k(Y)=L\subseteq E$.
   Uses: lem-sfb-normal-stein-constant-field, lem-pc-very-ample-ample, lem-trf-finite-projective-
   bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, lem-kun-
   projective-implies-proper, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-
   immersion-comp.
13. The group action on the Stein scheme is explicit. For any affine $W\subseteq P$, the
   automorphisms on $X'$ and $P$ identify $r'^{-1}W$ with $r'^{-1}(hW)$ and induce an isomorphism
   of section algebras $\Gamma(r'^{-1}(hW),\mathcal O)\to\Gamma(r'^{-1}W,\mathcal O)$. Taking
   spectra yields $q^{-1}W\to q^{-1}(hW)$. These maps agree on intersections because the section
   maps commute with restrictions. They therefore glue, satisfy the group law, and make $q$
   equivariant. The evaluation maps defining $g$ commute with these same pullbacks, so $g$ is
   equivariant. Restriction to the scalar subrings is the original action on $k$; hence the
   actions are compatible with the $k$-structures.
   Uses: lem-sfb-normal-stein-constant-field.
14. The scheme $Y$ is geometrically integral over $k$. Take a nonempty affine open $W\subseteq Y$.
   Its inverse image in the dominant integral $X'$ is nonempty; sections inject into $E$. Thus
   $\mathcal O_Y(W)$, viewed as its subring of $L\subseteq E$, injects into $E$. Tensoring this
   inclusion with any extension field $K/k$ remains injective: extend a basis of the subspace to a
   $k$-basis of $E$. Since $E\otimes_kK$ is a domain by Step 1, $\mathcal O_Y(W)\otimes_kK$ is a
   domain. These integral affine base changes cover $Y_K$ and their pairwise intersections are
   nonempty by the same basis argument as in Step 11. Hence $Y_K$ is integral.
   Uses: def-pc-geometrically-irreducible.
15. The generic fibre $T=X'\times_Y\operatorname{Spec}L$ is proper over $L$. On affines of $Y$,
   forming it localizes the integral source rings by the nonzero elements of the base ring. Thus
   $T$ is integral and normal, is of finite type over $L$, and has function field $E$. By Step 1,
   $E/F$ is separably generated with basis $t_d$, so all $E\otimes_FK$ are reduced. Also $L/F$ is
   finite separable: separably generated implies separable, and its finite algebraic subextension
   $L/F$ has a separating basis of size zero. Restriction across this separable algebraic
   extension shows that $E\otimes_LK$ is reduced for every $K/L$. Apply the generic-stalk
   reducedness criterion to get that $T$ is geometrically reduced.
   Uses: lem-kun-proper-stability, lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-
   separably-generated-tensor-reduced, lem-weil-pbc-separably-generated-separable, def-weil-pbc-
   separable-field-extension, lem-trf-geometric-reducedness-separable-scalar-restriction, lem-pur-
   geometric-reducedness-from-generic-stalks.
16. Since $L$ is algebraically closed in $E$, its separable algebraic closure in $E$ is $L$
   itself. The finite-separable-closure lemma therefore makes $\operatorname{Spec}E$ geometrically
   irreducible over $L$. The generic-point criterion transfers this to $T$. Combined with Step 15,
   $T$ is geometrically integral. Finally $L/F$ is finite, $F=k(t_1,\ldots,t_{d-1})$, and
   $\operatorname{trdeg}_kE=d$. The transcendence-degree tower formula gives
   $\operatorname{trdeg}_kL=d-1$ and $\operatorname{trdeg}_LE=1$. The finite-type dimension
   formula applied to $Y/k$ and $T/L$ gives $\dim Y=d-1$ and $\dim T=1$. These are all required
   clauses, without any claim that $T$ is smooth.
   Uses: lem-zl-finite-separable-closure, lem-zl-generic-point-geometric-irreducibility, lem-kun-
   transcendence-degree-tower, lem-sc-closed-irreducible-dimension-trdeg, def-pc-geometrically-
   irreducible.
-/
theorem exists_equivariant_curve_pencil
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k))
    [IsIntegral X] [IsProper p] [GeometricallyIntegral p]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (d : ℕ) (hd : 2 ≤ d) (hdim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (H : Type v) [Group H] [Finite H]
    (α : H →* Aut X) (β : H →* (k ≃+* k))
    (hsemilinear : ∀ h : H, (α h).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (β h⁻¹).toRingHom)) :
    ∃ (X' Y : Scheme.{u}) (p' : X' ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k))
      (_ : IsIntegral X') (_ : IsIntegral Y)
      (α' : H →* Aut X') (γ : H →* Aut Y) (π : X' ⟶ X) (g : X' ⟶ Y),
      (∀ x : X', IsDomain (X'.presheaf.stalk x) ∧
        IsIntegrallyClosed (X'.presheaf.stalk x)) ∧
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsProper p' ∧ GeometricallyIntegral p' ∧
      IsProper q ∧ GeometricallyIntegral q ∧ IsHProjective q ∧
      π ≫ p = p' ∧ g ≫ q = p' ∧
      (∀ h : H, (α' h).hom ≫ p' =
        p' ≫ Spec.map (CommRingCat.ofHom (β h⁻¹).toRingHom)) ∧
      (∀ h : H, (γ h).hom ≫ q =
        q ≫ Spec.map (CommRingCat.ofHom (β h⁻¹).toRingHom)) ∧
      IsHProjective π ∧ Surjective π ∧
      (∀ h : H, (α' h).hom ≫ π = π ≫ (α h).hom) ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)) ∧
      (∃ hη : π (genericPoint X') = genericPoint X,
        Function.Bijective
          (X.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
            π.stalkMap (genericPoint X') : X.functionField ⟶ X'.functionField)) ∧
      IsHProjective g ∧ IsDominant g ∧
      (∀ h : H, (α' h).hom ≫ g = g ≫ (γ h).hom) ∧
      topologicalKrullDim Y = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint Y)) ∧
      topologicalKrullDim (g.fiber (genericPoint Y)) = (1 : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
