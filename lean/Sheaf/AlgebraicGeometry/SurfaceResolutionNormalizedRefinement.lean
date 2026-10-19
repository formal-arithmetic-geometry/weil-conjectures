/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.RingTheory.CompletionDimension
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FiniteDegree.Algebra
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# Refining a local surface resolution by normalized point blowups

Source: Stacks Project, Resolution of Surfaces, Tags 0BGM and 0BBS
(blueprint: lem-per-surface-resolution-normalized-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A normal Noetherian local surface with a regular proper birational model admits a finite
proper normalized point-blowup tower with regular endpoint. All levels are integral and
normal, the normalizations are finite, and all reduced point centers lie over the closed
point. The base identification is the isomorphism `p 0`; the displayed composition equations
fix all structure maps. `Fin n` is empty when `n = 0`, so that case is retained.

Source: Stacks Project, Resolution of Surfaces, Tags 0BGM and 0BBS
(blueprint: lem-per-surface-resolution-normalized-refinement).

Proof plan:
1. Apply the regular-model completion lemma to the given $T\to\operatorname{Spec}A$. It supplies a
complete Noetherian normal local domain $C=\widehat A$ and an integral regular proper birational
model $T_C\to\operatorname{Spec}C$. The completion-dimension theorem gives $\dim C=\dim A=2$. It
is enough to construct a proper normalized point-blowup tower with regular endpoint over $C$: the
existing completion-descent theorem will then give the required tower over $A$, including
regularity of its endpoint. We construct that tower in Steps 2--7 rather than assuming that
domination alone preserves regularity.
Uses: lem-per-regular-model-completion, lem-weil-pbc-completion-dimension.
2. The complete-local excellence theorem makes $C$ excellent. The finite-type Noetherian theorem
and excellent finite-type/localization stability make $T_C$ Noetherian and excellent. The
closed-dominant dimension theorem applies to its proper birational map to $\operatorname{Spec}C$:
the function-field extension has transcendence degree zero, so $\dim T_C=2$. Apply normalized
domination to this map, obtaining $Y=Y_n\to\cdots\to Y_0=\operatorname{Spec}C$ and a factorization
$q:Y\to T_C$. Apply the excellent normalized-tower geometry theorem: since the normal base has
trivial initial normalization, every $Y_j$ is integral, normal, excellent, Noetherian and
two-dimensional, and every normalization used is finite. All arrows are proper by the domination
theorem. The composite $Y\to\operatorname{Spec}C$ of these proper arrows is proper by composition
of proper morphisms, so the factor $q$ is proper by proper-to-separated cancellation over
$\operatorname{Spec}C$, and is birational because both structure maps identify their function
fields with $\operatorname{Frac}C$.
Uses: lem-per-complete-local-excellence, lem-weil-pbc-finite-type-over-noetherian,
lem-exc-finite-type-localization-excellent, lem-trf-closed-dominant-dimension,
lem-per-excellent-surface-normalized-domination, lem-per-excellent-normalized-blowup-tower,
lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-composition.
3. Apply the excellent-normal-surface local-data theorem to $Y$. Its singular set is a finite set
of closed points $y_1,\ldots,y_t$, and $B_a=\mathcal O_{Y,y_a}$ is an excellent Noetherian normal
local domain of dimension $2$. Each $B_a$ is a localization of a finite-type $C$-algebra: choose
an affine neighbourhood of $y_a$ in the finite-type $C$-scheme $Y$ and localize at its prime. If
$t=0$, $Y$ is already regular and the subsequent local choices are empty.
Uses: lem-per-excellent-normal-surface-local-data.
4. Fix $a$, put $x_a=q(y_a)$ and $R_a=\mathcal O_{T_C,x_a}$. The regular scheme $T_C$ is normal by
regular-implies-normal. At a codimension-one point its one-dimensional Noetherian normal local
domain is a DVR. Thus the modification-codimension-one theorem applied to $q$ gives an isomorphism
over every point of codimension zero or one in $T_C$. If $x_a$ had either codimension, the local
ring at $y_a$ would be a regular local ring of $T_C$, a contradiction. Since $\dim T_C=2$, $R_a$
has dimension $2$. It is regular, and is excellent by finite-type/localization stability over $C$.
The local map $R_a\hookrightarrow B_a$ is injective and identifies their fraction fields by
birationality. It is essentially of finite type: in affine charts
$\operatorname{Spec}E\to\operatorname{Spec}D$ for $q$, $E$ is finite type over $D$; if the primes
are $\mathfrak q$ over $\mathfrak p$, then $E_{\mathfrak q}$ is the localization of
$E\otimes_DD_{\mathfrak p}$ at the induced prime. Apply the birational-local rationality lemma to
$R_a\subset B_a$. It gives $H^1(Z,\mathcal O_Z)=0$ for every normal proper birational model of
$\operatorname{Spec}B_a$.
Uses: rem-pc-regular-normal, lem-sc-normal-dim1-dvr, lem-per-normal-modification-codimension-one,
lem-exc-finite-type-localization-excellent,
lem-per-regular-surface-birational-rational-local-rings.
5. For each $a$, apply the rational-surface point-blowup resolution lemma to $B_a$ over the
complete local ring $C$. Step 3 supplied its essentially-finite-type presentation and dimension,
and Step 4 supplied exactly its vanishing hypothesis. This gives an ordinary point-blowup tower
$V_{a,m_a}\to\cdots\to V_{a,0}=\operatorname{Spec}B_a$ with integral normal intermediate schemes,
proper arrows, centers over its closed point, and regular endpoint. Regard it as a normalized
point-blowup tower: each ordinary blowup in this particular tower is already normal, so its
normalization in its function field is the identity. Indeed on a normal affine chart the ring is
integrally closed in its fraction field, which makes the integral closure used to define
normalization equal to the ring itself. This changes neither the schemes nor the arrows.
Uses: lem-per-rational-surface-point-blowup-resolution, def-sc-normalization,
def-weil-pbc-normal-ring.
6. Globalize these $t$ local proper normalized towers at the distinct closed points $y_a$ by the
local-normalized-blowups globalization theorem. It gives a proper normalized point-blowup tower
$W\to\cdots\to Y$, an isomorphism over the regular open $Y\setminus\{y_a\}$, and endpoint
local-ring identifications over each $y_a$ with the local rings of $V_{a,m_a}$. Therefore $W$ is
regular: a point over the regular open has its regular local ring unchanged, and a point over
$y_a$ has the regular local ring of its corresponding point on $V_{a,m_a}$. These cases cover
every point. In case $t=0$ this is the identity tower. Applying the excellent normalized-tower
geometry theorem over $Y$ also shows that the intermediate schemes are integral, normal, excellent
and Noetherian, and all their normalization morphisms are finite.
Uses: lem-per-local-normalized-blowups-globalize, def-weil-regular-scheme,
lem-per-excellent-normalized-blowup-tower.
7. Concatenate the first tower ending at $Y$ and the tower of Step 6. Its endpoint is regular.
Every intermediate scheme is proper over $\operatorname{Spec}C$, by composition of proper
morphisms. If $z$ is one of the chosen closed centers, its singleton is closed in that
intermediate scheme; the proper structure map is closed, so its image is a closed singleton in
$\operatorname{Spec}C$. Since $C$ is local, this image is its unique closed point. Hence all
centers of the concatenated tower lie over that point, as required for completion descent.
Uses: lem-weil-pbc-proper-composition, def-weil-proper-morphism.
8. Apply the normalized-blowup completion-descent theorem to $A\to C$. Step 1 supplied normality
of the completion, and Steps 2--7 supplied a finite proper normalized point-blowup tower over $C$,
supported over its closed point and with regular endpoint. Descent yields $X_N\to\cdots\to
X_0=\operatorname{Spec}A$ with the same properties of properness and support of centers, and with
$X_N$ regular. The theorem identifies the base change of the whole tower, including all structure
maps. It explicitly allows length zero.
Uses: lem-per-normalized-blowup-completion-descent.
9. We check the remaining integral/normal clauses on the descended tower. Start with the normal
integral base $\operatorname{Spec}A$. For an integral intermediate scheme, the ordinary point
blowup is integral: on a nonempty affine open with domain $D$ and ideal $I$, its chart rings
$D[I/a]\subset D_a\subset\operatorname{Frac}D$ are domains for nonzero generators $a$, and all
these charts share the unchanged generic point. The zero-generator charts are empty; the point
ideal is nonzero, since the intermediate scheme has dimension $2$ and its closed center cannot be
its generic point. The chart-cover theorem covers the blowup by exactly these charts. Its
normalization in the common function field is the relative normalization in
$\operatorname{Spec}K$: the affine integral-closure description agrees with the definition of
$(-)^\nu$. The relative-normalization theorem makes it integral, and the
normalization-normal-stalks theorem makes all its local rings normal (the source
$\operatorname{Spec}K$ is normal). The generic-point morphism to a Noetherian scheme is
quasi-compact and quasi-separated, so both theorems apply. Induction proves that all $X_j$ are
integral and normal: after each normalization its proper birational map to the base has dimension
$2$ by the closed-dominant dimension theorem, providing the dimension hypothesis for the next
point blowup. Noetherianity at each stage follows from proper finite type over the Noetherian
base.
Uses: prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring, def-sc-normalization,
lem-weil-pbc-relative-normalization, lem-weil-pbc-normalization-normal-stalks,
lem-weil-pbc-finite-type-over-noetherian, lem-trf-closed-dominant-dimension.
10. For each descended arrow write $X_{j+1}\xrightarrow{\nu_j}B_j=\operatorname{Bl}_{x_j}X_j\to
X_j$. The normalization map is integral by the relative-normalization theorem, with the
identification in Step 9. The blowup is proper by the blowup-proper theorem, since a reduced
closed-point ideal on a Noetherian scheme is finite type and quasi-coherent, and in particular it
is separated. The composite $X_{j+1}\to X_j$ is proper by Step 8. Apply proper-to-separated
cancellation to this triangle to conclude that $\nu_j$ is proper and therefore locally of finite
type. The finite-iff-integral-and-locally-finite-type theorem now shows that $\nu_j$ is finite.
This proves the finiteness of every normalization without assuming that $A$ itself is excellent or
Nagata. Together with Steps 8 and 9 it proves every clause of the statement.
Uses: lem-weil-pbc-relative-normalization, lemma-nagata-blowup-proper,
lemma-nagata-proper-to-separated-target, lem-weil-pbc-finite-iff-integral-lft. -/
theorem exists_regular_normalized_point_blowup_tower
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hDim : ringKrullDim A = 2)
    (T : Scheme.{u}) [IsIntegral T] (hT : IsRegularScheme T)
    (f : T ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (hη : f (genericPoint T) = genericPoint (Spec (CommRingCat.of A)))
    (hBir : IsIso (f.functionFieldMap hη)) :
    ∃ (n : ℕ) (X : Fin (n + 1) → Scheme.{u})
      (p : ∀ i : Fin (n + 1), X i ⟶ Spec (CommRingCat.of A)),
      IsIso (p 0) ∧
      (∀ i : Fin (n + 1), IsIntegral (X i) ∧
        ∀ x : X i, IsDomain ((X i).presheaf.stalk x) ∧
          IsIntegrallyClosed ((X i).presheaf.stalk x)) ∧
      IsRegularScheme (X (Fin.last n)) ∧
      ∀ j : Fin n, ∃ (x : X j.castSucc) (hx : IsClosed ({x} : Set (X j.castSucc)))
        (I : (X j.castSucc).IdealSheafData),
        I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ ∧
        p j.castSucc x = IsLocalRing.closedPoint A ∧
        ∃ (_ : IsIntegral I.blowup) (e : X j.succ ≅ I.blowup.normalization),
          IsFinite I.blowup.fromNormalization ∧
          IsProper (e.hom ≫ I.blowup.fromNormalization ≫ I.blowupMap) ∧
          e.hom ≫ I.blowup.fromNormalization ≫ I.blowupMap ≫ p j.castSucc = p j.succ := by
  sorry

end AlgebraicGeometry
