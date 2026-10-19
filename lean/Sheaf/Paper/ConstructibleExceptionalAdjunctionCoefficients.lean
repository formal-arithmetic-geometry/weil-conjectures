/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
import Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence

/-! # Constructible exceptional adjunction and coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Compact support and the constructible exceptional functor form the specified
coefficient-compatible exact adjunction on the actual finite-Tor categories.
Source: current blueprint, sec-six-functors-basics, exceptional inverse image;
etale coefficient systems as in Zheng, Lemma 5.22
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).

Proof plan from the DAG:
1. Work first at a fixed finite coefficient stage and a fixed compactification (c=(j,p_f)). The
scheme (overline X) is finite type over (k): finite affine covers of (Y) and of the finite-type
morphism (p_f) give finitely generated coordinate algebras over (k). Choose a nonnegative
dimension bound (d) by lem-kun-dimension-finite-type (take (d=0) for the empty scheme). The
open-extension theorem puts (j_!K) in the finite-Tor category with its original interval
([a,b]); cor-sf-direct-image-ctf-proetale gives (F_AK=Rp_{f,*}j_!K) constructible with interval
([a,b+2d]). Finite type over the Noetherian field makes all schemes Noetherian. Open extension
and proper derived direct image are exact by the two triangulated-functor nodes, so (F_A) is
exact on the finite-Tor subcategory and its compactification refinements agree.
Uses: lem-kun-dimension-finite-type, lem-trf-open-ctf, cor-sf-direct-image-ctf-proetale,
lem-weil-pbc-finite-type-over-noetherian, lem-sf-exact-functor-derived-triangulated,
lem-weil-pbc-derived-direct-image-triangulated, prop-compactification-coherence-detailed.

2. Work on the ordinary unbounded etale derived categories. The compactification has Noetherian
source and target by Step 1, so thm-amb-etale-exceptional-adjoint supplies
$F_A^{\mathrm{et}}=Rp_{\mathrm{et},*}j_!^{\mathrm{et}}\dashv G_A^{\mathrm{et}}$. Apply
thm-sf-ambient-adjoint-class to the same compactification: for bounded-below pro-etale $L$ it
gives the bounded-below composite $G_AL=\nu_X^*G_A^{\mathrm{et}}R\nu_{Y,*}L$ and its natural Hom
bijection for bounded-below etale-origin inputs. This is exactly the finite functor defined in
def-weil-exceptional-inverse-image. The preservation corollary applies to this specified
composite, including nonseparated finite-type $X,Y$, and gives constructibility and finite-Tor
bounds. Thus the Hom bijection restricts to the full finite-Tor constructible categories. Its
transpose formulas give units, counits and triangles. The unique adjoint shift comparison
supplies coherent shifts and unit/counit compatibility; the triangulated-right-adjoint lemma
then gives exactness. No Brown theorem is applied to a pro-etale category or to an unspecified
localizing closure.
Uses: thm-amb-etale-exceptional-adjoint, thm-sf-ambient-adjoint-class,
def-weil-exceptional-inverse-image, cor-pur-general-admissibility-datum,
lem-weil-finite-ctf-triangulated, lem-weil-pbc-adjunction-of-natural-bijection,
lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint.

3. A finite-Tor input has a bounded flat model by lem-sf-flat-model. After extension from (A) to
a finite coefficient ring (B), tensoring with a (B)-module is the original flat tensor followed
by restriction, so the same Tor interval is retained; no flatness of a quotient (A_n\to A_m) is
used. The finite-tensor constructibility theorem gives constructible cohomology, and refining
the finite etale trivializing covers makes the induced (B)-action locally constant with finite
(B)-stalks. K-flat change of rings is independent of the chosen model by
lem-pur-derived-change-of-rings. Hence all finite coefficient-change functors in the statement
have the displayed domains; higher stages are handled below.
Uses: lem-sf-flat-model, lem-pur-finite-tensor-constructible-cohomology,
lem-pur-derived-change-of-rings.

4. On ordinary etale categories use $F_A^{\mathrm{et}}\dashv G_A^{\mathrm{et}}$. Exact
restriction of scalars $r_T$ is conservative. Open extension commutes with restriction termwise,
and ringed-topos direct-image composition gives $r_YF_B^{\mathrm{et}}\cong
F_A^{\mathrm{et}}r_X$. Derived scalar extension $T_T$ is left adjoint to $r_T$, computed by
K-flat models. Define $q:T_YF_A^{\mathrm{et}}\to F_B^{\mathrm{et}}T_X$ by transposing
$F_A^{\mathrm{et}}$ of the scalar unit. After restriction it is the constant-$B$ projection map
of lem-pur-etale-exceptional-constant-tensor, hence an isomorphism. The Hom chain using $T\dashv
r$, $F_A\dashv G_A$, $F_B\dashv G_B$ and $q$ identifies $r_XG_B^{\mathrm{et}}\cong
G_A^{\mathrm{et}}r_Y$. Under this identification, restriction of the counit-transpose map
$b:T_XG_A^{\mathrm{et}}\to G_B^{\mathrm{et}}T_Y$ is precisely the constant-$B$ exceptional
tensor map of that same lemma: both have transpose the inverse projection map followed by
$1\otimes\epsilon_A$. That lemma makes it invertible even when $B$ is nonflat over $A$;
conservativity then proves that $b$ is invertible as a $B$-linear map. The identity and
composite $q$ comparisons are the tensor associators on K-flat models.
Uses: thm-amb-etale-exceptional-adjoint,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-pur-etale-exceptional-constant-tensor, lem-galois-yoneda-hom-bijection,
lem-weil-pbc-ringed-topoi-module-adjunction, lem-sc-derived-adjunction-from-underived,
lem-pur-derived-change-of-rings.

5. Transport the preceding comparison across the etale--pro-etale constructible-origin
equivalence. The Tor-amplitude comparison preserves the same interval, the site-comparison unit
identifies (R\nu_*\nu^*) with the identity on bounded-below etale complexes, and the
compact-support comparison identifies pro-etale (F_A) with the transported etale
(F_A^{\mathrm{et}}). Exact inverse image commutes with tensoring by a constant coefficient ring
on a flat model, so the transported (q) is the canonical pro-etale coefficient map. The
transported (b), units, and counits are the same maps because they are characterized by the
natural Hom transposes; hence they are independent of witnesses and compactification choices.
Uses: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude,
thm-weil-pbc-site-comparison, lem-sf-class-compact-support-comparison,
lem-weil-pbc-adjunction-of-natural-bijection.

6. For a coefficient map $T$, define $b_L:T_XG_AL\to G_BT_YL$ as the $F_B\dashv G_B$ transpose
of $T_Y\epsilon_L\circ q_{G_AL}^{-1}$. The inverse-transpose formula gives the displayed counit
equation. Put $a_K=b_{F_AK}\circ T_X\eta_{A,K}:T_XK\to G_BT_YF_AK$. Its inverse transpose is
$$T_Y\epsilon_{A,F_AK}\circ q_{G_AF_AK}^{-1}\circ F_BT_X\eta_{A,K} =T_Y(\epsilon_{A,F_AK}\circ
F_A\eta_{A,K})\circ q_K^{-1}=q_K^{-1},$$ by naturality of $q$ and the triangle identity. After
postcomposing $a_K$ with $G_B(q_K)$, its inverse transpose is $q_K\circ q_K^{-1}=1_{F_BT_XK}$.
This is also the inverse transpose of $\eta_{B,T_XK}$. Injectivity proves exactly the completed
unit equation in the statement. The unique-adjoint coefficient lemma transports this
counit-normalized comparison to any other adjoint choices; mate pasting applied to the identity
and tensor-composition comparisons for $q$ proves the identity and composition cocycles for $b$.
Uses: det-sp-unique-right-adjoint, det-sp-unique-adjoint-coefficients,
lem-weil-pbc-adjunction-of-natural-bijection, lem-weil-pbc-mate-pasting.

7. Form $\mathsf S_A(T_{\mathrm{et}})$ with $A_n=R/\varpi^n$ (not an $\ell$-power reindexing).
Apply lem-pur-etale-coefficient-system-adjoint directly to the fixed compactification. It
supplies an actual $R$-linear exact adjunction $\mathcal
F^{\mathrm{et}}=Rp_{A,*}j_{!,A}\dashv\mathcal G^{\mathrm{et}}$ on ordinary unbounded etale
system derived categories. In particular its stated canonical isomorphism $e_n\mathcal
G^{\mathrm{et}}\cong G_{A_n}^{\mathrm{et}}e_n$ preserves evaluated units, counits and transition
mates; its uniform lower bound and bounded-below normalization assertions apply here. These are
conclusions of this cited theorem, not consequences asserted from $e_n\mathcal
F^{\mathrm{et}}\cong F_{A_n}^{\mathrm{et}}e_n$ alone. Zheng Lemma 5.22 uses the derived
evaluation-left-adjoint comparisons of Lemma 5.13 and (5.16.2). We use its system theorem,
including that evaluation result, rather than constructing a different Brown adjoint and
identifying it by evaluations. No separatedness of the structure maps of $X,Y$ is required by
this theorem.
Uses: lem-pur-etale-coefficient-system-adjoint, lem-pur-coefficient-system-derived-comparison.

8. Write $C_T=\nu_{T,A}^*$ and $V_T=R\nu_{T,A,*}$ on actual derived systems. The
system-comparison theorem and finite site-comparison unit make $C_T,V_T$ inverse equivalences
between bounded-below etale systems and bounded-below pro-etale systems with etale-origin
levels. Indeed the unit evaluates to the finite unit and is invertible by joint conservativity;
the counit and preservation of normalization are stated by the system-comparison theorem. Form
the compact-support system comparison $C_Y\mathcal F^{\mathrm{et}}\to\mathcal
F^{\mathrm{proet}}C_X$: use the proper direct-image mate of the commuting inverse images,
followed by the open comparison. These are actual system maps by derived system adjunction and
direct-image composition. Their evaluations are the canonical finite comparisons, invertible by
the finite proper and open comparison nodes; joint conservativity proves invertibility of the
system comparison, without assuming faithfulness on maps. Consequently, for normalized
bounded-below systems $M,N$ with constructible finite-Tor levels, $$\operatorname{Hom}(\mathcal
F^{\mathrm{proet}}M,N)\cong\operatorname{Hom}(\mathcal
F^{\mathrm{et}}V_XM,V_YN)\cong\operatorname{Hom}(V_XM,\mathcal
G^{\mathrm{et}}V_YN)\cong\operatorname{Hom}(M,C_X\mathcal G^{\mathrm{et}}V_YN).$$ Thus the
transported right functor is $\mathcal G=C_X\mathcal G^{\mathrm{et}}V_Y$, with actual system
units, counits and triangles. Its transitions are the finite mates from Step 6 and Step 7, and
it preserves normalization and common bounds. The composite $\mathcal G\mathcal R_Y$ is exactly
$\mathcal T_f$ in def-weil-exceptional-inverse-image, before applying the derived limit.
Uses: lem-pur-coefficient-system-derived-comparison, thm-weil-pbc-site-comparison,
lem-pur-system-level-left-extension, lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison,
lem-weil-pbc-adjunction-of-natural-bijection, def-weil-exceptional-inverse-image.

9. Use the ordinary reduction--limit adjunction $\mathcal R_T\dashv\mathcal L_T$ on strict
towers. Its unit is the map $P\to\mathcal L_T\mathcal R_TP$ whose compatible finite projections
on one flat-term K-flat representative are the actual reduction maps
$P\to\operatorname{Res}_n(P\otimes^L A_n)$; the total-limit cone is the stated (R\lim) cone, so
for a derived-complete integral object the unit is an isomorphism by the (E'=E) case of the
finite-free completed-scalar comparison. Its counit is an isomorphism on normalized towers by
normalized-DVR effectivity. Hence derived-complete integral finite-Tor objects are equivalent to
normalized towers with the common bounds required in the statement, and all maps are maps in the
ordinary derived categories.
Uses: lem-coef-derived-system-evaluation-calculus,
lem-weil-finite-free-completed-scalar-comparison, lem-coef-normalized-dvr-effectivity,
def-weil-derived-complete-integral-detailed, def-weil-finite-tor-amplitude,
lem-weil-pbc-ringed-strict-tower-homotopy-limit.

10. The common bounds required for the equivalence are uniform: Step 1 gives ([a,b+2d]) at every
finite level for compact supports, and the admissibility theorem gives coefficient-independent
bounds for the right adjoints. The integral compact-support comparison identifies the total
limit and each finite reduction with (Rf_!K), while normalized effectivity identifies the
right-adjoint tower with the completed (G_R). The integral finite-Tor category is triangulated,
so the adjunction, units, counits and exactness descend from the tower category.
Uses: lem-coef-integral-compact-support, cor-pur-general-admissibility-datum,
lem-coef-normalized-dvr-effectivity, lem-weil-integral-ctf-triangulated,
lem-weil-pbc-ringed-strict-tower-homotopy-limit.

11. For a finite extension (E\subset E'), the finite-free coefficient-system comparison
transports the tower adjunction and its (q,b) maps. The subsequence
(R'/\varpi^nR'=R'/\varpi'^{en}R') is cofinal; normalized transition maps recover every level (m)
from any level (en\ge m), and the cocycle makes the result independent of the choice. The
completed comparison (chi_{E'/E}) identifies this tower scalar extension with ordinary derived
scalar extension and the integral scalar-extension definition; constructibility is preserved by
the integral scalar-extension theorem.
Uses: lem-pur-etale-coefficient-system-adjoint,
lem-weil-finite-free-completed-scalar-comparison,
lem-weil-integral-scalar-extension-constructible, lem-pur-derived-change-of-rings,
def-weil-integral-scalar-extension.

12. Localize the integral (R)-linear adjunction at (\varpi). Every integral constructible object
has finite-Tor reductions by the residue-Tor theorem, so the preceding construction applies to
every integral representative. The Hom bijections are (R)-linear, hence localization gives
inverse natural Hom bijections for (E)-coefficients; units, counits, triangles, and coefficient
cocycles are images of the integral ones. Finally represent two \(\overline{\mathbf
Q}_\ell\)-objects over a common finite coefficient field. Step 6 makes the finite-stage Hom
bijections commute with every further scalar extension, so they pass to the directed colimit
defining the common-stage category. This yields the adjunction and all comparisons for (E) and
\(\overline{\mathbf Q}_\ell\), with field reduction interpreted through an integral
representative.
Uses: def-weil-rationalization-karoubi, lem-coef-integral-residue-tor,
lem-weil-linear-scalar-localization-triangulated, def-weil-algebraically-closed-coefficients,
lem-weil-pbc-adjunction-of-natural-bijection.

13. For a compactification refinement, transpose its compact-support comparison
(a:F_1\xrightarrow{\sim}F_2) to obtain (\rho:G_2\to G_1). The counit equation is the
inverse-transpose identity, and the unit equation follows by taking the two inverse transposes
and using the triangle identity; mate pasting gives identity and composition. The shift
comparison for the right adjoint is uniquely determined by the shift comparison for (F) and unit
compatibility, and the shift-compatible natural transformations remain compatible under
composition and whiskering. Therefore the adjunction, coefficient comparisons, refinement
cocycles and shifts all satisfy the displayed identities. Empty schemes give zero functors and
the stated zero bounds; ramified extensions use (en).
Uses: thm-sf-ambient-adjoint-class, prop-compactification-coherence-detailed,
lem-weil-pbc-mate-pasting, lem-weil-pbc-adjunction-shift-compatibility-unique,
lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-commshift-nattrans-triangle-morphism.
-/
theorem exists_system (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (System l Ω D hl (f := f)) := by
  obtain ⟨P⟩ := exists_coefficient_construction l Ω D hl f
  have H := coefficient_construction_coherence l Ω D hl P
  let R : RingSystem l Ω D hl (f := f) := {
    operation := P.ring.operation
    left := P.ring.left
    finiteRight := P.ring.finiteRight
    integralLeft := P.ring.integralLeft
    integralLeft_normalized := P.ring.integralLeft_normalized
    rationalLeft := P.ring.rationalLeft
    scalar := P.ring.scalar
    finiteScalar_eq := P.ring.finiteScalar_eq
    finiteScalar_normalized := P.ring.finiteScalar_normalized
    integralScalar_eq := P.ring.integralScalar_eq
    integralScalar_normalized := P.ring.integralScalar_normalized
    comparison := fun c {s t} a ha ↦
      (P.ring.comparison c (s := s) (t := t) a ha).complete l Ω
    comparison_normalized := P.ring.comparison_normalized
    scalarComposition := P.ring.scalarComposition
    cocycle := H.ring.cocycle
    scalarIdentity := P.ring.scalarIdentity
    identityLeft := H.ring.identityLeft
    identityRight := H.ring.identityRight
  }
  let F : FieldSystem l Ω D hl R := {
    rationalizationComparison := fun c E ↦ (P.fields.rationalizationComparison c E).complete l Ω
    rationalization_normalized := P.fields.rationalization_normalized
    rationalComparison := fun c E L i ↦ (P.fields.rationalComparison c E L i).complete l Ω
    rational_normalized := P.fields.rational_normalized
    rationalCocycle := H.fields.rationalCocycle
    rationalIdentityLeft := H.fields.rationalIdentityLeft
    rationalIdentityRight := H.fields.rationalIdentityRight
  }
  let M : CommonSystem l Ω D hl R F := {
    commonComparison := fun c i ↦ (P.common.commonComparison c i).complete l Ω
    common_normalized := P.common.common_normalized
    commonCocycleLeft := H.common.commonCocycleLeft
    commonCocycleRight := H.common.commonCocycleRight
  }
  let N : RefinementSystem l Ω D hl R F M := {
    refinement := P.refinements.refinement
    refinement_normalized := P.refinements.refinement_normalized
    refinementRational := P.refinements.refinementRational
    refinementCommon := P.refinements.refinementCommon
    refinementIdentity := H.refinements.refinementIdentity
    refinementComposition := H.refinements.refinementComposition
  }
  exact ⟨{ ring := R, fields := F, common := M, refinements := N }⟩

end ConstructibleExceptionalCoefficients
end WeilConjectures
