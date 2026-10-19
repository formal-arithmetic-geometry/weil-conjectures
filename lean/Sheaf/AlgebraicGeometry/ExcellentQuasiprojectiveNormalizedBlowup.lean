/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.RelativeProj.Rees
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion

/-!
# Quasi-projectivity of normalized blowups over excellent affine bases

Source: Stacks Project, Divisors, Tags 02NS and 02ND; Morphisms, Tags 035S, 087S,
0C4M and 01VT; More on Algebra, Tag 07QU
(blueprint: lem-per-excellent-quasiprojective-normalized-blowup).

The ordinary blowup is the existing affine-chart gluing, and its normalization is
normalization in its function field. The existential integrality witness makes the
latter construction available without assuming the integrality being asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonzero finite-type ideal on an integral scheme quasi-projective over an excellent
Noetherian affine base has integral Noetherian blowup and normalization. Both remain of
finite type and quasi-projective over the base. The normalization map is finite, and the
normalized blowup map is H-projective and induces an isomorphism on dense opens.
Source: Stacks Project, Tags 02NS, 02ND, 035S, 087S, 0C4M, 01VT and 07QU
(blueprint: lem-per-excellent-quasiprojective-normalized-blowup).

The coordinate type `ULift (Fin (m + 1))` represents classical projective dimension `m`,
including dimension zero, in the scheme universe. Each embedding commutes with the
specified morphism to the affine base. No projectivity of the base morphism is assumed.

Proof plan (the DAG proof, in order):
1. $S$ is Noetherian because it is the spectrum of the Noetherian ring $A$. Apply [lem-weil-pbc-
finite-type-over-noetherian] to $X\to S$. Thus $X$ is Noetherian, in particular quasi-compact.
Uses: pqf-def-locnoeth, lem-weil-pbc-finite-type-over-noetherian.
2. Let $i:X\hookrightarrow\mathbf P^m_S$ be the given immersion. By [lem-nagata-affine-proj-
scalar-extension], applied to $\mathbf Z\to A$ and the graded isomorphism $A\otimes_{\mathbf
Z}\mathbf Z[T_0,\ldots,T_m]\cong A[T_0,\ldots,T_m]$, the scheme $\mathbf
P^m_S=S\times_{\operatorname{Spec}\mathbf Z}\mathbf P^m_{\mathbf Z}$ is identified over $S$ with
$\operatorname{Proj}A[T_0,\ldots,T_m]$; we regard $i$ as an immersion into this Proj. By [lemma-
nagata-immersion-shrink-to-closed-exists], its image is contained in a quasi-compact open $W$ of
this Proj and $X\to W$ is closed. Apply [lem-trf-proj-qc-open-twist-ample] to obtain an ample
invertible twist $\mathcal O_W(e)$ for some $e\geq1$. Its pullback to $X$ is ample by [lem-trf-
ample-restrict-closed-immersion]. Hence $X$ admits an ample invertible sheaf.
Uses: lem-nagata-affine-proj-scalar-extension, lemma-nagata-immersion-shrink-to-closed-exists,
lem-trf-proj-qc-open-twist-ample, lem-trf-ample-restrict-closed-immersion.
3. Form the sheaf Rees algebra $\mathcal R=\bigoplus_{n\geq0}J^n$ [def-nagata-sheaf-rees-algebra].
The degree-one inclusion $J\to\mathcal R$ extends by [lem-weil-pbc-quasi-coherent-symmetric-
algebra] to $\operatorname{Sym}(J)\to\mathcal R$. It is graded and surjective: in degree $n$ every
element of $J^n$ is locally a finite sum of products of $n$ sections of $J$, and each such product
is the image of the corresponding symmetric monomial. Apply [prop-nagata-relative-proj-
functoriality] to get a closed immersion $\operatorname{Proj}_X\mathcal R\hookrightarrow\mathbf
P_X(J)$. This source is the blowup in the statement: over $\operatorname{Spec}R$, the standard
chart for $at$ has coordinate ring $(R[Jt]_{at})_0=R[J/a]$, since $b t^n/(at)^n$ maps to $b/a^n$
for $b\in J^n$. The displayed maps commute with localization and with each other on overlaps, so
identify the chart gluing over $X$. Consequently $p$ is projective in the projective-bundle sense
[def-trf-projective-bundle-morphism], using the finite-type quasi-coherent module $J$.
Uses: def-nagata-sheaf-rees-algebra, lem-weil-pbc-quasi-coherent-symmetric-algebra, prop-nagata-
relative-proj-functoriality, def-trf-projective-bundle-morphism.
4. Put $U=X\setminus V(J)$. It is nonempty and dense: a nonzero ideal subsheaf of $\mathcal O_X$
on an integral scheme is nonzero at the generic point, since on any nonempty affine open its
sections embed in the function field. On $U$ the ideal is the unit ideal, and the blowup charts
are those of $U$ itself; hence $p^{-1}U\to U$ is an isomorphism. Each chart
$\operatorname{Spec}R[J/a]$ with $a\ne0$ has domain coordinate ring inside $\operatorname{Frac}R$,
and its open $D(a)$ is nonempty and maps into $U$. Thus $p^{-1}U$ is dense in every chart, so
dense in $Z$. All charts are reduced, and this dense open is irreducible because it is isomorphic
to the nonempty open $U$ of the integral scheme $X$. Therefore $Z$ is reduced, irreducible and
nonempty, hence integral [def-pc-integral-scheme]; $p$ is birational.
Uses: def-pc-integral-scheme.
5. By [lem-trf-projective-bundle-proper], $p$ is proper, hence of finite type by [def-weil-proper-
morphism]. Compose with $X\to S$ using [lem-sfb-finite-type-composition-base-change]; this makes
$Z\to S$ finite type. Thus $Z$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Choose
the finite affine cover of $Z$ by finite-type $A$-algebras given by the definition of finite type.
Each of these rings is excellent by [lem-exc-finite-type-localization-excellent]. By [lem-trf-
excellent-scheme-affine-cover], every affine coordinate ring of $Z$ is excellent.
Uses: lem-trf-projective-bundle-proper, def-weil-proper-morphism, lem-sfb-finite-type-composition-
base-change, lem-weil-pbc-finite-type-over-noetherian, def-weil-finite-type-morphism, lem-exc-
finite-type-localization-excellent, lem-trf-excellent-scheme-affine-cover.
6. Since $X$ has an ample invertible sheaf, [lem-trf-projective-bundle-to-h-projective] upgrades
$p$ to a closed immersion $Z\hookrightarrow\mathbf P^r_X$ followed by projection for some
$r\geq0$. Base change the given locally closed immersion $i:X\hookrightarrow\mathbf P^m_S$ along
$\mathbf P^r_S\to S$. Factoring $i$ as a closed immersion followed by an open immersion, [lem-
weil-pbc-closed-immersion-base-change] and [lem-weil-pbc-open-immersion-base-change] give an
immersion $\mathbf P^r_X\hookrightarrow\mathbf P^r_S\times_S\mathbf P^m_S$. Composition of
immersions [lem-weil-pbc-proper-fp-permanence](e), followed by the closed Segre embedding [lem-
chow-segre], gives a locally closed immersion $Z\hookrightarrow\mathbf P^{(r+1)(m+1)-1}_S$.
Uses: lem-trf-projective-bundle-to-h-projective, lem-weil-pbc-closed-immersion-base-change, lem-
weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-fp-permanence, lem-chow-segre.
7. Apply the same explicit ample-sheaf construction to the immersion of $Z$ from Step 6. The
Noetherian scheme $Z$ is quasi-compact, so [lemma-nagata-immersion-shrink-to-closed-exists]
provides a quasi-compact open $W_Z$ of that projective space containing $Z$ as a closed subscheme.
By [lem-nagata-affine-proj-scalar-extension], as in Step 2, that projective space is
$\operatorname{Proj}$ of the polynomial ring over $A$, so [lem-trf-proj-qc-open-twist-ample]
supplies an ample invertible twist on $W_Z$. Pull it back by the closed immersion using [lem-trf-
ample-restrict-closed-immersion]. Thus $Z$ admits an ample invertible sheaf.
Uses: lem-nagata-affine-proj-scalar-extension, lemma-nagata-immersion-shrink-to-closed-exists,
lem-trf-proj-qc-open-twist-ample, lem-trf-ample-restrict-closed-immersion.
8. Apply [lem-per-excellent-normalization-preparation] to the reduced Noetherian excellent scheme
$Z$. For an integral scheme its componentwise normalization is its function-field normalization,
because it has only one irreducible component [def-weil-pbc-reduced-normalization]. Thus $\nu:N\to
Z$ is finite and surjective, $N$ is Noetherian excellent, and there is a dense open $O\subseteq Z$
over which $\nu$ is an isomorphism. The scheme $N$ is integral: by [def-sc-normalization] the
inverse image of an affine domain chart $\operatorname{Spec}B\subset Z$ is
$\operatorname{Spec}\overline B$, with $\overline B$ the integral closure of $B$ in $k(Z)$; these
are domains, and their zero primes all glue to the same generic point with residue field $k(Z)$.
Thus their union is reduced and irreducible. Finally a finite module algebra is generated as an
algebra by its finite module generators, so [def-weil-finite-integral-morphism] makes $\nu$ finite
type. Composition [lem-sfb-finite-type-composition-base-change] makes $N\to S$ finite type.
Uses: lem-per-excellent-normalization-preparation, def-weil-pbc-reduced-normalization, def-sc-
normalization, def-weil-finite-integral-morphism, lem-sfb-finite-type-composition-base-change.
9. The finite map $\nu$ is projective in the projective-bundle sense by [lem-trf-finite-
projective-bundle]. Since $Z$ admits an ample invertible sheaf (Step 7), [lem-trf-projective-
bundle-to-h-projective] makes $\nu$ H-projective. Compose it with the H-projective map $p$ (Step
6), using [lem-trf-h-projective-composition], to obtain a closed immersion
$N\hookrightarrow\mathbf P^t_X$ over $X$. Base change $i:X\hookrightarrow\mathbf P^m_S$ along
$\mathbf P^t_S\to S$ exactly as in Step 6, using stability of closed and open immersions under
base change. Compose immersions and then the Segre closed immersion to obtain
$N\hookrightarrow\mathbf P^{(t+1)(m+1)-1}_S$. This proves both the required projectivity of $p\nu$
and the quasi-projectivity of $N$ over $S$.
Uses: lem-trf-finite-projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-
projective-composition, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-open-immersion-
base-change, lem-weil-pbc-proper-fp-permanence, lem-chow-segre.
10. The two dense opens $O$ and $p^{-1}U$ of the integral scheme $Z$ have nonempty intersection
$V$. The isomorphism $p^{-1}U\cong U$ identifies $V$ with a nonempty open $U_0\subset X$. The
inverse image $\nu^{-1}V$ is isomorphic to $V$ because $V\subset O$, and is a nonempty open of the
integral scheme $N$. Both $U_0$ and $\nu^{-1}V$ are therefore dense. The composite $p\nu$
restricts to their isomorphism, which is the asserted birationality.
-/
theorem excellent_quasiprojective_normalizedBlowup
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsExcellent A)
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ∃ (m : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A))),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A)) ↘ Spec (.of A) = f)
    (J : X.IdealSheafData) (hJ₀ : J ≠ ⊥)
    (hJ : J.toModules.IsQuasiCoherentFiniteType) :
    ∃ hZ : IsIntegral J.blowup,
      IsNoetherian J.blowup ∧
      IsIntegral (@Scheme.normalization J.blowup hZ) ∧
      IsNoetherian (@Scheme.normalization J.blowup hZ) ∧
      LocallyOfFiniteType (J.blowupMap ≫ f) ∧
      QuasiCompact (J.blowupMap ≫ f) ∧
      LocallyOfFiniteType (@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap ≫ f) ∧
      QuasiCompact (@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap ≫ f) ∧
      (∃ (m : ℕ) (i : J.blowup ⟶ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A))),
        IsImmersion i ∧
        i ≫ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A)) ↘ Spec (.of A) = J.blowupMap ≫ f) ∧
      (∃ (m : ℕ) (i : @Scheme.normalization J.blowup hZ ⟶
          ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A))),
        IsImmersion i ∧
        i ≫ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of A)) ↘ Spec (.of A) =
          @Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap ≫ f) ∧
      IsFinite (@Scheme.fromNormalization J.blowup hZ) ∧
      IsHProjective (@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap) ∧
      ∃ U : X.Opens,
        Dense (U : Set X) ∧
        Dense ((@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap) ⁻¹ᵁ U :
          Set (@Scheme.normalization J.blowup hZ)) ∧
        IsIso ((@Scheme.fromNormalization J.blowup hZ ≫ J.blowupMap) ∣_ U) := by
  sorry

end AlgebraicGeometry
