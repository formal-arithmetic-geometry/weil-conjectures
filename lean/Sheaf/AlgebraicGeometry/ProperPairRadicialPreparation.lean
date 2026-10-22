/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Sheaf.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Dense
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Localization.Integral

/-!
# Proper normal pair preparation after a radicial constant extension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3, Step 1,
printed p.150 (blueprint: lem-sfb-proper-pair-radicial-preparation).

The finite disjoint union is expressed by a finite pairwise disjoint open cover.
`IsNormalScheme` includes integrality and nonemptiness of each member. Projectivity
is in the projective-bundle convention, and residue extensions use the actual map `r`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Proper normal pair preparation after a finite purely inseparable constant extension.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3, Step 1,
printed p.150 (blueprint: lem-sfb-proper-pair-radicial-preparation).

Proof plan from the reviewed DAG split:

1. Apply [sk-thm-nagata-compactification] to $X\to\operatorname{Spec}k$; the base is affine and
hence quasi-compact and quasi-separated. By the dense-compactification definition
[sk-def-nagata-sketch-data] this gives $j:X\hookrightarrow\overline X$ with $\overline X$ proper
over $k$ and $X$ dense in $\overline X$. Proper includes finite type. Set $C=\overline{j(Z)}$ as a
closed subset. Since $Z$ is closed in the open $X$, $C\cap X=Z$. Both $X$ and $\overline X$ are
Noetherian by [lem-weil-pbc-finite-type-over-noetherian], because $\operatorname{Spec}k$ is
Noetherian (its only local ring is a field). Thus $\overline X$ has finitely many components by
[lem-weil-pbc-noetherian-finitely-many-components]. Each component has a generic point in $X$: its
complement in the other finitely many components is a nonempty open subset of that component,
which the dense open $X$ meets. No such generic point lies in $Z$, since $Z$ is nowhere dense in
$X$. The equality $C\cap X=Z$ now shows that $C$ contains no component; hence it is nowhere dense.

Uses: sk-thm-nagata-compactification, sk-def-nagata-sketch-data, def-weil-proper-morphism,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-finitely-many-components.

2. Apply [lem-pur-finite-inseparable-geometric-reduction] to $\overline X/k$ and its finitely many
irreducible components. Choose its single finite purely inseparable extension $e/k$, and put
$T=(\overline X\times_k\operatorname{Spec}e)_{\mathrm{red}}$. Then $T$ is geometrically reduced
over $e$. The reduced induced structure is the closed subscheme supplied by
[lem-weil-pbc-reduced-induced-closed-subscheme], applied to the whole base change. Properness is
stable under base change and closed subschemes, so $T$ is proper over $e$, and hence finite type
and Noetherian. In characteristic zero, purely inseparable means equality, so this choice has
$e=k$ [def-weil-pbc-finite-purely-inseparable-extension].

Uses: lem-pur-finite-inseparable-geometric-reduction,
lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-proper-base-change,
lem-weil-pbc-closed-immersion-proper, def-weil-proper-morphism,
lem-weil-pbc-finite-type-over-noetherian, def-weil-pbc-finite-purely-inseparable-extension.

3. Write $t:T\to\overline X$. The field map $\operatorname{Spec}e\to\operatorname{Spec}k$ is
finite: a finite $k$-basis of $e$ is a finite module generating set. Its base change is finite,
and the reduction closed immersion is finite; thus $t$ is finite
[lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-closed-immersion-finite,
lem-weil-pbc-finite-composition]. By [lem-pc-homeo-pure-insep], and since reduction changes no
points, $t$ is a homeomorphism. The field map is universally injective by
[lem-pc-spec-pure-insep-integral-radicial-surjective]; this property survives base change by
[lem-trf-finite-radicial-basechange], and restriction to the reduction remains universally
injective. The radicial equivalence [def-weil-radicial-morphism] therefore makes every residue
extension of $t$ purely inseparable; it is finite because $t$ is finite (the residue field is a
quotient of the finite-dimensional fibre algebra). In particular generic points correspond
bijectively, with finite purely inseparable residue fields.

Uses: lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-closed-immersion-finite,
lem-weil-pbc-finite-composition, lem-pc-homeo-pure-insep,
lem-pc-spec-pure-insep-integral-radicial-surjective, lem-trf-finite-radicial-basechange,
def-weil-radicial-morphism.

4. Let $T_1,\ldots,T_s$ be the reduced induced closed subschemes on the components of $T$, using
[lem-weil-pbc-reduced-induced-closed-subscheme]. The finite number $s$ is positive by
[lem-weil-pbc-noetherian-finitely-many-components], since $X$ is nonempty and $t$ is a
homeomorphism. Each $T_i$ is integral (reduced and irreducible), nonempty and proper over $e$; the
last assertion is [lem-weil-pbc-closed-immersion-proper]. Set $C_i=t^{-1}C\cap T_i$ as a closed
subset, and give it its reduced induced structure. It misses the generic point of $T_i$, so is
nowhere dense. Its ideal $\mathcal I_i$ is quasi-coherent by the reduced-induced-structure
theorem, and of finite type: on each Noetherian affine chart it is an ideal in a Noetherian ring
and thus finitely generated. The complement $U_i=T_i\setminus C_i$ is a nonempty quasi-compact
dense open.

Uses: lem-weil-pbc-reduced-induced-closed-subscheme,
lem-weil-pbc-noetherian-finitely-many-components, lem-weil-pbc-closed-immersion-proper.

5. Form the ordinary blowup $b_i:S_i=\operatorname{Bl}_{\mathcal I_i}T_i\to T_i$. It is proper by
[lemma-nagata-blowup-proper] and is an isomorphism over $U_i$ by
[thm-nagata-global-blowup-complement]. The extended ideal $\mathcal I_i\mathcal O_{S_i}$ is
locally generated by a non-zero-divisor, by [thm-nagata-blowup-principalizes-center]; its support
is $b_i^{-1}C_i$. The open $U_i$ is dense in $S_i$ by
[lemma-nagata-conrad-dense-in-admissible-blowup], applied to this $U_i$-admissible blowup. The
next step checks reducedness and integrality directly from the charts.

Uses: lemma-nagata-blowup-proper, thm-nagata-global-blowup-complement,
thm-nagata-blowup-principalizes-center, lemma-nagata-conrad-dense-in-admissible-blowup.

6. On a nonempty affine $\operatorname{Spec}A\subseteq T_i$, the ring $A$ is a domain. By
[prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring], the nonempty blowup charts
are spectra of the subalgebras $A[\mathcal I_i/a]\subseteq A_a$ for nonzero $a\in\mathcal
I_i(\operatorname{Spec}A)$. These are domains; the charts with $a=0$ are empty. Thus $S_i$ is
reduced. Its dense open $U_i$ is irreducible, so its closure $S_i$ is irreducible. Hence $S_i$ is
nonempty integral and $b_i$ is birational. Properness over $e$ follows by
[lem-weil-pbc-proper-composition] from the properness of $b_i$ and $T_i/e$.

Uses: prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring,
lem-weil-pbc-proper-composition.

7. Apply [lem-weil-pbc-integral-chow-relatively-ample] over the field $e$ to $S_i$, which is
integral, separated and finite type because it is proper over $e$. Obtain an integral $Y_i$, a
proper surjection $c_i:Y_i\to S_i$, an immersion $Y_i\to\mathbf P^{n_i}_e$ and a nonempty open
$V_i\subseteq S_i$ over which $c_i$ is an isomorphism. Hence $c_i$ induces equality of function
fields. The scheme $Y_i$ is proper over $e$ by proper composition. Its immersion into projective
space is proper by [lem-weil-pbc-proper-to-separated], since projective space is separated, and
then is closed by [lem-weil-pbc-proper-immersion-closed]. Consequently $Y_i$ is projective over
$e$. This auxiliary birational Chow modification is inserted to give an absolute projective
embedding before normalizing.

Uses: lem-weil-pbc-integral-chow-relatively-ample, lem-weil-pbc-proper-composition,
lem-weil-pbc-proper-to-separated, lemma-nagata-projective-space-base-change-proper,
def-weil-proper-morphism, lem-weil-pbc-proper-immersion-closed, def-kun-projective.

8. Let $n_i:N_i=Y_i^\nu\to Y_i$ be the normalization in its own function field, as in
[def-sc-normalization]. By [lem-sc-normalization-exists] it is finite, surjective and birational.
It is integral and normal: on a nonempty affine chart of $Y_i$ its normalization ring is the
integral closure of a domain $A$ in $\operatorname{Frac}A$ [def-sc-normalization];
[lem-weil-pbc-integral-closure-finite-extension-normal] with the identity field extension makes
that ring an integrally closed domain, and [lem-weil-pbc-localization-normal-domain] makes all of
its local rings integrally closed domains. The closed immersion $Y_i\hookrightarrow\mathbf
P^{n_i}_e$ of Step 7 together with quasi-compactness of $Y_i$ (it is of finite type over $e$) says
that $Y_i\to\operatorname{Spec}e$ is projective in the convention of [def-pc-projective-morphism]
(H-projective and quasi-compact), which is the hypothesis of [lem-fin-finite-over-projective]. By
[lem-fin-finite-over-projective], with the affine Noetherian base $\operatorname{Spec}e$, the
finite map $n_i$ above the projective $Y_i/e$ makes $N_i$ projective over $e$ in that convention:
there is a closed immersion $N_i\hookrightarrow\mathbf P^{m_i}_e$ over $e$. Thus $N_i$ is
nonempty, integral, normal, proper and finite type over $e$, and $N_i\to T_i$ induces equality of
function fields.

Uses: def-sc-normalization, lem-sc-normalization-exists,
lem-weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-localization-normal-domain,
def-pc-projective-morphism, lem-fin-finite-over-projective, lem-kun-projective-implies-proper,
def-weil-proper-morphism.

9. The Cartier marking survives both $c_i$ and $n_i$ without a flatness assumption. Write $f$ for
a local non-zero-divisor generator of $\mathcal I_i\mathcal O_{S_i}$. It is nonzero in $k(S_i)$.
Both $Y_i$ and $N_i$ are integral and their maps to $S_i$ induce inclusions (in fact equalities)
of function fields. Their affine section rings inject into these function fields by
[lem-sc-integral-function-field-affine-fraction]. Therefore the image of $f$ is nonzero in each
target local domain and is a non-zero-divisor. The image ideal is generated by that image of $f$,
so it is an effective Cartier ideal [def-nagata-effective-cartier-ideal]. Its vanishing set is
exactly the inverse image of the vanishing set of $f$. Thus there is an effective Cartier divisor
on $N_i$ with support $(t b_i c_i n_i)^{-1}C$.

Uses: lem-sc-integral-function-field-affine-fraction, def-nagata-effective-cartier-ideal.

10. The schemes $N_i$ remain geometrically reduced over $e$. Let $\eta_i$ be the generic point of
$T_i$. There is an affine open neighbourhood $W$ of $\eta_i$ in $T$ meeting no other component.
Then $W$ is an open subscheme of $T_i$ and is geometrically reduced, since after every field
extension it is open in the reduced base change of $T$. Write $W=\operatorname{Spec}A$. Its
function field is $F_i=\operatorname{Frac}A$ by [lem-sc-integral-function-field-affine-fraction].
For every extension $L/e$, $F_i\otimes_e L$ is a localization of the reduced ring $A\otimes_e L$
and is reduced: if a fraction has nilpotent numerator, multiplying by one denominator kills a
power, and reducedness kills the fraction itself. The generic stalk of $N_i$ is this same $F_i$,
because $b_i,c_i,n_i$ are birational. Now [lem-pur-geometric-reducedness-from-generic-stalks]
applies to the reduced integral scheme $N_i$ and proves geometric reducedness. This verifies the
extra condition through every inserted birational model.

Uses: lem-sc-integral-function-field-affine-fraction,
lem-pur-geometric-reducedness-from-generic-stalks.

11. Set $B=\coprod_{i=1}^sN_i$ and define $r:B\to\overline X$ by the maps $t b_i c_i n_i$, using
[lem-weil-pbc-scheme-coproduct-family]. Each summand is open and closed, so $B$ is a finite
disjoint union of nonempty integral normal schemes and is geometrically reduced (after any field
extension each of its open summands is reduced). The effective Cartier ideals from Step 9 define
an ideal on this disjoint union by restriction to the summands; it is locally generated by their
non-zero-divisor generators and has support $r^{-1}C$. Every $N_i\to T_i$ is surjective: $n_i$ and
$c_i$ are surjective, and $b_i$ is proper with image containing the dense open $U_i$, hence has
closed image all of $T_i$. Since the $T_i$ cover $T$ and $t$ is surjective, $r$ is surjective.
Exactly one generic point is supplied by each $N_i$, and Step 3 and birationality show that they
correspond bijectively to the generic points of $\overline X$ with the same finite purely
inseparable residue extensions as for $t$.

Uses: lem-weil-pbc-scheme-coproduct-family, def-nagata-effective-cartier-ideal,
def-weil-proper-morphism.

12. The finite disjoint union $B$ is projective over $e$. Indeed, choose the embeddings
$N_i\hookrightarrow\mathbf P^{m_i}_e$ from Step 8, and give one projective space $\mathbf P^M_e$,
$M+1=\sum_i(m_i+1)$, disjoint blocks of homogeneous coordinates of these sizes. The linear
subspace defined by setting every coordinate outside block $i$ to zero is $\mathbf P^{m_i}_e$.
Distinct such subspaces are disjoint, since their simultaneous equations kill every homogeneous
coordinate. Their finite union is a closed subscheme, and is the disjoint union of those
subspaces: locally the other blocks are absent, so its structure sheaf restricts to that of the
single block. The embeddings $N_i$ therefore give a closed immersion $B\hookrightarrow\mathbf
P^M_e$. Hence $B/e$ is proper and finite type by [lem-kun-projective-implies-proper,
def-weil-proper-morphism].

Uses: def-kun-projective, def-nagata-projective-space-base-change,
lem-kun-projective-implies-proper, def-weil-proper-morphism.

13. The morphism $\operatorname{Spec}e\to\operatorname{Spec}k$ is finite, so is projective in the
projective-bundle sense by [lem-trf-finite-projective-bundle]. The structure sheaf of
$\operatorname{Spec}k$ is ample by [def-weil-pbc-ample-invertible-module]: the section $1$ has
nonvanishing locus the entire affine scheme. Consequently
[lem-trf-projective-bundle-to-h-projective] makes this finite field morphism H-projective. Since
$B/e$ is H-projective by Step 12, [lem-trf-h-projective-composition] gives a closed immersion
$\iota:B\hookrightarrow\mathbf P^d_k$.

Uses: lem-trf-finite-projective-bundle, def-weil-pbc-ample-invertible-module,
lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, def-kun-projective.

14. Because $\overline X$ is separated over $k$, its diagonal is a closed immersion
[def-weil-proper-morphism]. The graph $\Gamma_r:B\to B\times_k\overline X$ is its base change
along $(r,\mathrm{id}_{\overline X})$, hence a closed immersion by
[lem-weil-pbc-closed-immersion-base-change]. The morphism $\iota\times\mathrm{id}_{\overline X}$
is another base change of a closed immersion. Their composite is a closed immersion (on affine
charts the corresponding surjections of rings compose) $B\hookrightarrow\mathbf
P^d_k\times_k\overline X=\mathbf P^d_{\overline X}$ over $r$; the equality is fibre-product
associativity in [def-nagata-projective-space-base-change]. Thus $r$ is H-projective. The finite
projective space is the projective bundle of the finite free module $\mathcal O_{\overline
X}^{d+1}$ [def-nagata-relative-projective-space], so $r$ is projective in the required
projective-bundle convention [def-trf-projective-bundle-morphism]. Together with Steps 1--13 this
proves every clause, including the empty-marking case: then each $\mathcal I_i=\mathcal O_{T_i}$,
its blowup is the identity, and the Cartier ideals have empty support.

Uses: def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change,
def-nagata-projective-space-base-change, def-nagata-relative-projective-space,
def-trf-projective-bundle-morphism, def-kun-projective.
-/
theorem exists_proper_pair_radicial_preparation
    (k : Type u) [Field k] (X : Scheme.{u}) [Nonempty X]
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set X) (hZ : IsClosed Z) (hZnd : interior Z = ∅) :
    ∃ (Xbar : Scheme.{u}) (fbar : Xbar ⟶ Spec (.of k)) (j : X ⟶ Xbar),
      IsProper fbar ∧ IsOpenImmersion j ∧ DenseRange j ∧ j ≫ fbar = f ∧
      ∃ C : Set Xbar, IsClosed C ∧ interior C = ∅ ∧ j ⁻¹' C = Z ∧
      ∃ (e : Type u) (_ : Field e) (i : k →+* e),
        i.Finite ∧ @IsPurelyInseparable k e _ _ i.toAlgebra ∧
        (ringChar k = 0 → Function.Surjective i) ∧
        ∃ (B : Scheme.{u}) (b : B ⟶ Spec (.of e)) (r : B ⟶ Xbar),
          IsProper b ∧ GeometricallyReduced b ∧ IsProjectiveBundle r ∧ Surjective r ∧
          r ≫ fbar = b ≫ Spec.map (CommRingCat.ofHom i) ∧
          (∃ (n : ℕ) (U : Fin n → B.Opens),
            Pairwise (fun a c ↦ Disjoint (U a) (U c)) ∧ (⨆ a, U a) = ⊤ ∧
              ∀ a, IsNormalScheme (U a).toScheme) ∧
          Set.BijOn r
            {η : B | ∃ T ∈ irreducibleComponents B, IsGenericPoint η T}
            {η : Xbar | ∃ T ∈ irreducibleComponents Xbar, IsGenericPoint η T} ∧
          (∀ (T : Set B), T ∈ irreducibleComponents B →
            ∀ η : B, IsGenericPoint η T →
              (r.residueFieldMap η).hom.Finite ∧
              @IsPurelyInseparable (Xbar.residueField (r η)) (B.residueField η) _ _
                (r.residueFieldMap η).hom.toAlgebra) ∧
          ∃ D : B.IdealSheafData, D.IsInvertible ∧ (D.support : Set B) = r ⁻¹' C := by
  sorry

end AlgebraicGeometry
