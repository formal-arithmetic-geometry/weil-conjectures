/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

import Sheaf.AlgebraicGeometry.ProperStability
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.NagataRing
import Sheaf.RingTheory.JapaneseDomain
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import Sheaf.AlgebraicGeometry.FractionFieldSectionsBaseChange
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Mathlib.RingTheory.RingHom.Flat

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Localization.Integral
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.FieldTheory.FiniteSeparableClosure
import Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction

/-!
# Factorization with a geometrically integral generic curve

Source: de Jong, Families of curves and alterations (1997), Lemma 5.2 and its proof,
printed pp. 612–613, with trivial group and retaining only properness;
Stacks Project, Tag 02JX, for finite total dimensions
(blueprint: lem-trf-geometrically-integral-curve-factorization).

## Main statements

* `exists_geometricallyIntegralCurveFactorization` gives a proper birational modification
  factoring through proper dominant maps with geometrically integral generic fibres of
  dimensions one and `d - 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper dominant family with geometrically integral generic fibre of dimension at least two
admits a proper birational modification factoring through a geometrically integral generic curve.

Source: de Jong, Families of curves and alterations (1997), Lemma 5.2 and its proof,
printed pp. 612–613 (trivial group; properness only); Stacks Project, Tag 02JX
(blueprint: lem-trf-geometrically-integral-curve-factorization).

`ηS` and `ηY` are generic points in the sense of Stacks Tag 004X. Excellence is the
recorded `IsExcellent` predicate on every affine coordinate ring. Noetherianness is
local Noetherianness together with quasi-compactness. The restriction `π ∣_ U` has
source the whole preimage of `U`, so its being an isomorphism expresses exactly a
modification over a dense open. Finite total dimension is a conditional conclusion.

Proof plan (the thirteen steps of the DAG node):

1. Put $K=k(S)$ and $M=k(X)$. The generic fibre $X_\eta$ is a proper integral $K$-variety: on an
   affine chart over $\operatorname{Spec}B\subseteq S$ its rings are localizations by
   $B\setminus\{0\}$; they are domains and their common generic point has residue field $M$.
   Properness follows by base change. A nonempty affine chart has fraction field $M$ and a finite
   list of algebra generators, so $M/K$ is finitely generated. The dimension--transcendence-degree
   theorem gives $\operatorname{trdeg}_K M=d$. Moreover $\operatorname{Spec}M$ is geometrically
   integral over $K$: take a nonempty affine open $U\subseteq X_\eta$, which is geometrically
   integral by the definition, and apply the affine function-field transfer lemma to $U$ and
   $\operatorname{Spec}M$, using their identical fraction fields. Thus $M\otimes_KE$ is a domain
   for every field extension $E/K$. Uses: [lem-kun-proper-stability],
   [lem-sc-integral-function-field-affine-fraction], [lem-sc-closed-irreducible-dimension-trdeg],
   [lem-sbc-field-fraction-ring-geometric-integrality], [def-pc-geometrically-irreducible],
   [lem-weil-pbc-fibre-product-affine-spectra].

2. Choose a separating transcendence basis $t_1,\ldots,t_d$ of $M/K$. In characteristic zero the
   perfect-field separating-basis lemma applies. In characteristic $p>0$, the reducedness of every
   $M\otimes_KE$ from step 1 implies separability by the geometrically-reduced-extension lemma;
   apply its definition to the finitely generated subextension $M$ itself. The cardinality of the
   basis is $d$ by the definition of transcendence degree. Put $F=K(t_1,\ldots,t_{d-1})$. Then
   $t_d$ is a separating transcendence basis of $M/F$, since $M/K(t_1,\ldots,t_d)$ is separable
   algebraic. In particular $M/F$ is separably generated and has transcendence degree one.
   Tensoring it with any extension field of $F$ is reduced by the separably-generated tensor
   theorem. Uses: [lem-weil-pbc-perfect-field-separating-basis],
   [lem-weil-pbc-geometrically-reduced-extension-separable],
   [def-weil-pbc-separable-field-extension], [def-weil-pbc-transcendence-basis],
   [def-kun-transcendence-degree], [lem-weil-pbc-separably-generated-tensor-reduced].

3. Let $P=\mathbf P^{d-1}_S$. Its standard charts over an affine domain $B$ in $S$ are polynomial
   rings in $d-1$ variables over $B$. The charts are integral, have nonempty pairwise overlaps,
   and have the same generic point, so $P$ is integral, with function field $F$, and is proper
   dominant over $S$. Choose a nonempty affine $V\subseteq X$ mapping into an affine open of $S$.
   Express the finitely many $t_i$, $i<d$, as fractions in $\mathcal O_X(V)$, and invert the
   product of their nonzero denominators. On the resulting dense affine open $U\subseteq X$ they
   define the map $[1:t_1:\cdots:t_{d-1}]$ into the first chart of $P$. This is an $S$-morphism
   $r_0:U\to P$. Algebraic independence makes the map from the coordinate domain of that chart
   injective, hence $r_0$ maps the generic point to the generic point and is dominant. Uses:
   [lem-weil-pbc-projective-space-standard-charts],
   [lemma-nagata-projective-space-base-change-proper],
   [lem-sc-integral-function-field-affine-fraction], [def-weil-affine-spectrum].

4. Form the scheme-theoretic image $Z$ of $(1,r_0):U\to X\times_SP$, and write $a:Z\to X$ and
   $r_Z:Z\to P$ for the projections. The map is quasi-compact: $U$ is Noetherian, so all its open
   subsets are quasi-compact. The image lemmas give that $|Z|$ is the closure of the irreducible
   nonempty graph, hence irreducible and nonempty; they also give $a^{-1}(U)\simeq U$. For an
   affine open $W$ of the product meeting $Z$, its inverse image in $U$ is nonempty by density.
   Sections there inject into $M$. The defining ideal on $W$ is the kernel of the map to these
   sections, hence is prime. Thus every affine chart of $Z$ has a domain as coordinate ring, so
   $Z$ is reduced and integral. The dense open $a^{-1}(U)$ identifies its function field with $M$.
   Uses: [lem-weil-pbc-scheme-image-qc-kernel], [lemma-nagata-scheme-image-ideal-qc],
   [lemma-nagata-scheme-image-partial-section], [lem-sc-integral-scheme-stalks-in-function-field],
   [def-pc-integral-scheme].

5. The two projections of $X\times_SP$ are proper by base change, and the inclusion of $Z$ is
   closed. Thus $a$ and $r_Z$ are proper. Their images contain respectively $U$ and $r_0(U)$, so
   both are dominant. Consequently $Z\to S$ is proper. The schemes $P$ and $Z$ are Noetherian by
   finite type over the Noetherian base. They are excellent as well: over an affine excellent
   chart $\operatorname{Spec}B\subseteq S$, the locally finite type affine-pairs lemma makes the
   coordinate rings of source affine charts finite type over $B$. Excellence ascends to these
   rings, and the affine-cover excellence lemma gives excellence on every affine open. Uses:
   [lem-kun-proper-stability], [lem-weil-pbc-closed-immersion-proper],
   [lem-weil-pbc-finite-type-over-noetherian], [lem-weil-pbc-lft-affine-pairs],
   [lem-exc-finite-type-localization-excellent], [lem-trf-excellent-scheme-affine-cover].

6. Normalize $Z$ in $M=k(Z)$, obtaining $\nu:X\prime\to Z$. The residue-field normalization lemma
   gives an integral normal $X\prime$ with function field $M$. This map is finite: each excellent
   affine domain $B\subset M$ is quasi-excellent, hence Nagata, hence N-2 by taking its zero
   prime; its integral closure $\overline B\subset M$ is a finite $B$-module. The localization
   theorem identifies these finite affine normalization rings on overlaps. This also shows
   directly that $\nu$ is an isomorphism over a dense open: take a nonempty affine
   $\operatorname{Spec}B\subseteq Z$ and finite module generators of $\overline B$, write them as
   fractions in $B$, and invert the product $b\ne0$ of their denominators. Then $\overline
   B[1/b]=B[1/b]$. Choose the affine inside $a^{-1}(U)$; the composite $\pi=a\nu$ is an
   isomorphism over the corresponding dense open of $X$. Uses:
   [lem-weil-pbc-normalization-in-residue-field-extension], [def-sc-normalization],
   [lem-exc-quasi-excellent-nagata], [def-weil-pbc-nagata-ring], [def-weil-pbc-japanese-domain],
   [lem-weil-pbc-integral-closure-commutes-localization], [def-weil-finite-integral-morphism].

7. The finite map $\nu$ is proper, so $\pi$ and $X\prime\to S$ are proper. The finite-type
   arguments of step 5 show that $X\prime$ is excellent and Noetherian. Put $r=r_Z\nu:X\prime\to
   P$. It is proper by composition and dominant because it induces the inclusion $F\subset M$. Let
   $T=X\prime\times_P\operatorname{Spec}F$. This is a proper integral $F$-variety with function
   field $M$. It is normal: over an affine chart of $P$, formation of this generic fibre inverts
   the nonzero elements of its coordinate domain. At a point of $T$ all those elements are already
   units in the local ring of $X\prime$, so the local rings of $T$ are the same integrally closed
   domains. No smoothness of $T$ is asserted. Uses: [lem-weil-pbc-finite-proper],
   [lem-kun-proper-stability], [lem-weil-pbc-finite-type-over-noetherian],
   [lem-weil-pbc-lft-affine-pairs], [lem-exc-finite-type-localization-excellent],
   [lem-trf-excellent-scheme-affine-cover], [def-pc-scheme-fibre],
   [lem-sc-integral-function-field-affine-fraction].

8. Take $\mathcal B=r_*\mathcal O_{X\prime}$ and $q:Y=\underline{\operatorname{Spec}}_P(\mathcal
   B)\to P$. Proper coherent pushforward makes $\mathcal B$ a coherent, hence quasi-coherent,
   finite $\mathcal O_P$-algebra; here $\mathcal O_{X\prime}$ is coherent since $X\prime$ is
   Noetherian (on a Noetherian affine, kernels between finite free modules are finite). Relative
   spectrum gives $q^{-1}(V)=\operatorname{Spec}\Gamma(r^{-1}V,\mathcal O)$ for each affine
   $V\subseteq P$, and $q$ is finite by the finite-morphism criterion. The identity on this
   section algebra defines the local evaluation map $r^{-1}V\to q^{-1}V$. These maps agree on
   overlaps: restriction of the algebra and of its relative spectrum commutes with open
   restriction, and maps to an affine are determined by their maps on sections. They therefore
   glue to $g:X\prime\to Y$ with $r=qg$. Uses: [lem-pc-coherent-hi], [pqf-def-coherent],
   [lem-weil-pbc-affine-morphism-relative-spec], [def-weil-finite-integral-morphism],
   [lem-weil-pbc-morphism-into-affine-scheme].

9. The map $g$ is dominant. Indeed, on $q^{-1}V=\operatorname{Spec}B_V$, sections
   $B_V=\Gamma(r^{-1}V,\mathcal O)$ inject into $M$. A nonempty principal open $D(b)$ has $b\ne0$;
   this section cannot vanish at every point of the reduced scheme $r^{-1}V$, so $g^{-1}D(b)$ is
   nonempty. These principal opens form a basis, and the affine opens $q^{-1}V$ cover $Y$.
   Therefore $Y$ is irreducible, since it contains the dense image of the irreducible $X\prime$.
   Its rings $B_V$ are domains, so $Y$ is reduced and integral. The finite $q$ is proper, hence
   $h:Y\to P\to S$ is proper; $q$ is dominant because $qg=r$ is dominant, and thus so is $h$.
   Since $h$ is separated and $hg=f\pi$ is proper, the proper-over-separated lemma makes $g$
   proper. Finite type over $P$ and then $S$ also makes $Y$ Noetherian and excellent by exactly
   the affine-cover argument of step 5. Uses: [lem-sc-integral-scheme-stalks-in-function-field],
   [lem-weil-pbc-morphism-into-affine-scheme], [def-pc-integral-scheme],
   [lem-weil-pbc-finite-proper], [lem-kun-proper-stability], [lem-weil-pbc-proper-over-separated],
   [lem-weil-pbc-finite-type-over-noetherian], [lem-weil-pbc-lft-affine-pairs],
   [lem-exc-finite-type-localization-excellent], [lem-trf-excellent-scheme-affine-cover].

10. Put $L=\Gamma(T,\mathcal O_T)$. The proper-variety global-sections theorem says that $L/F$ is
   a finite field extension. Restrict to a nonempty affine $V=\operatorname{Spec}B\subseteq P$.
   Flat base change of global sections along $B\to F$ identifies $\Gamma(r^{-1}V,\mathcal
   O)\otimes_BF$ with $L$. This is a ring isomorphism: on pure tensors it sends $s\otimes c$ to
   $c$ times the restricted section $s$, so preserves products and the unit. Consequently
   $Y\times_P\operatorname{Spec}F=\operatorname{Spec}L$ and $k(Y)=L$; the generic fibre of $g$ is
   precisely $T$ regarded as an $L$-variety. Furthermore $L$ is algebraically closed in $M$. If
   $z\in M$ is algebraic over $L$, its monic polynomial over $L$ has coefficients regular on all
   of $T$. Thus $z$ is integral over each local ring of $T$, and normality puts it in each such
   ring. Local representatives agree in the common field $M$, so glue to a global section: $z\in
   L$. Finally $L/F$ is separable algebraic: every element $a\in L$ belongs to the finitely
   generated algebraic subextension $F(a)/F$ of the separable extension $M/F$, so the definition
   of separability gives an empty separating transcendence basis and hence separability of $a$.
   Uses: [lem-pc-h0-proper-variety], [lem-sc-fraction-field-sections-base-change],
   [lem-weil-pbc-affine-morphism-relative-spec],
   [lem-sc-integral-scheme-stalks-in-function-field],
   [lem-weil-pbc-separably-generated-separable], [def-weil-pbc-separable-field-extension].

11. By step 2 the $F$-algebra $M$ is geometrically reduced, and by step 10 $L/F$ is separable
   algebraic. Apply the scalar-restriction lemma to this $L$-algebra $M$: for every extension
   $E/L$, $M\otimes_LE$ is reduced. The generic-stalk reducedness criterion, applied to the
   integral $L$-variety $T$ with its sole generic stalk $M$, therefore proves that $T$ is
   geometrically reduced over $L$. The finite-separable-closure lemma applied to $M/L$ makes it
   geometrically irreducible after taking the separable algebraic closure of $L$ in $M$. That
   closure is $L$ itself by step 10. Thus $\operatorname{Spec}M$ is geometrically irreducible over
   $L$, and the generic-point criterion makes $T$ geometrically irreducible. Combining reducedness
   and irreducibility after every field extension proves that the generic fibre of $g$ is
   geometrically integral. Uses: [lem-trf-geometric-reducedness-separable-scalar-restriction],
   [lem-pur-geometric-reducedness-from-generic-stalks], [lem-zl-finite-separable-closure],
   [lem-zl-generic-point-geometric-irreducibility], [def-pc-geometrically-irreducible].

12. For every extension field $E/K$, the inclusion $L\subset M$ gives an injection
   $L\otimes_KE\hookrightarrow M\otimes_KE$: $E$ is flat over $K$ and flatness preserves
   injections. The latter ring is a domain by step 1, so the former is a domain as well; it is
   nonzero because it contains the unit of that domain. Thus $\operatorname{Spec}L$ is
   geometrically integral over $K$. The generic fibre $Y_\eta$ of $h$ is integral with function
   field $L$, by localization on its affine charts. The generic-point irreducibility criterion
   makes $Y_\eta$ geometrically irreducible. The generic-stalk reducedness criterion applied to
   these tensor products makes it geometrically reduced. It is therefore geometrically integral.
   Since $L/F$ is finite algebraic and $\operatorname{trdeg}_KF=d-1$, the tower formula gives
   $\operatorname{trdeg}_KL=d-1$ and $\operatorname{trdeg}_LM=1$. Apply the
   dimension--transcendence-degree theorem to the integral proper varieties $Y_\eta/K$ and $T/L$
   to obtain dimensions $d-1$ and $1$. Uses: [lem-weil-pbc-module-over-field-flat],
   [def-weil-pbc-flat-ring-map], [lem-weil-pbc-fibre-product-affine-spectra],
   [lem-zl-generic-point-geometric-irreducibility],
   [lem-pur-geometric-reducedness-from-generic-stalks], [lem-kun-transcendence-degree-tower],
   [lem-sc-closed-irreducible-dimension-trdeg], [def-pc-geometrically-irreducible].

13. The equality $hg=f\pi$ follows from $qg=r=r_Z\nu$ and the two projections of the graph over
   $S$. We have proved all the required integrality, properness, dominance and dimension
   assertions, and step 6 gives the dense-open isomorphism required of $\pi$. For the last clause,
   apply the closed-dominant dimension theorem to the proper birational map $\pi$: it gives $\dim
   X\prime=\dim X$, because its function-field extension is the identity. Apply the same theorem
   to $h$ to get $\dim Y=\dim S+(d-1)$. Hence $X\prime$ and $Y$ have finite dimension whenever $X$
   and $S$ do. Uses: [lem-trf-closed-dominant-dimension], [def-weil-proper-morphism].
-/
theorem exists_geometricallyIntegralCurveFactorization
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    [IsLocallyNoetherian S] [CompactSpace S]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hS : ∀ U : S.Opens, IsAffineOpen U → IsExcellent Γ(S, U))
    (hX : ∀ U : X.Opens, IsAffineOpen U → IsExcellent Γ(X, U))
    (f : X ⟶ S) [IsProper f] [IsDominant f]
    (ηS : S) (hηS : IsGenericPoint ηS Set.univ)
    (d : ℕ) (hd : 2 ≤ d)
    (hgeom : GeometricallyIntegral (f.fiberToSpecResidueField ηS))
    (hdim : topologicalKrullDim (f.fiber ηS) = (d : WithBot ℕ∞)) :
    ∃ (X' Y : Scheme.{u}) (π : X' ⟶ X) (g : X' ⟶ Y) (h : Y ⟶ S) (ηY : Y),
      IsIntegral X' ∧ IsIntegral Y ∧
      (∀ U : X'.Opens, IsAffineOpen U → IsExcellent Γ(X', U)) ∧
      (∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U)) ∧
      IsLocallyNoetherian X' ∧ CompactSpace X' ∧
      IsLocallyNoetherian Y ∧ CompactSpace Y ∧
      IsProper π ∧ (∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)) ∧
      IsProper g ∧ IsDominant g ∧ IsProper h ∧ IsDominant h ∧ π ≫ f = g ≫ h ∧
      IsGenericPoint ηY Set.univ ∧
      GeometricallyIntegral (g.fiberToSpecResidueField ηY) ∧
      topologicalKrullDim (g.fiber ηY) = (1 : WithBot ℕ∞) ∧
      GeometricallyIntegral (h.fiberToSpecResidueField ηS) ∧
      topologicalKrullDim (h.fiber ηS) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      (topologicalKrullDim S < ⊤ ∧ topologicalKrullDim X < ⊤ →
        topologicalKrullDim Y < ⊤ ∧ topologicalKrullDim X' < ⊤) := by
  sorry

end AlgebraicGeometry
