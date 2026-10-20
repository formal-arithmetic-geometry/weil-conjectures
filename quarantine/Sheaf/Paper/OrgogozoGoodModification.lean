/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.FiniteSupportDefectConservativity
import Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle
import Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.NagataAffineOpensProjective
import Sheaf.Paper.AlterationFiniteRefinement
import Sheaf.Paper.ModificationClosedImageLifting
import Sheaf.Paper.ModificationsZariskiRefinement
import Sheaf.Paper.NearbyClosedImage
import Sheaf.Paper.NearbyCyclesDimensionBound
import Sheaf.Paper.NearbyFiniteBaseDescent
import Sheaf.Paper.NearbyProperHyperdescent
import Sheaf.Paper.NearbySpreadOut
import Sheaf.Paper.OrgogozoInductionData
import Sheaf.Paper.OrientedNearbyStrictLocalDescription
import Sheaf.Paper.PlurinodalProperHypercover

/-!
# A modification making nearby cycles universally compatible with base change

Source: Lu--Zheng, Duality and nearby cycles over general bases, Theorem 4.27(1), p. 37
(blueprint: lem-trf-orgogozo-good-modification).

## Main declarations

- `orgogozoConstantScalars`: the canonical scalar map into the constant ring sheaf.
- `orgogozoModuleSections`: module-valued sections with constant scalars.
- `exists_modification_isPsiGood`: the good-modification theorem.

The helpers restrict intrinsic module sheaves to constant scalars. Constructibility is
then tested with the recorded ordinary small-etale module-sheaf predicate, using a
module-linear natural isomorphism over the canonical `AsSmall` site equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The actual constant-scalar map, the sheafification unit with commutativity forgotten.
Source: Lu--Zheng, Theorem 4.27(1), with ILO XI §4.1 and Stacks 03CY
(blueprint: lem-trf-orgogozo-good-modification). -/
def orgogozoConstantScalars (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  Functor.whiskerRight
    (toSheafify (etaleTopology.{u, u + 1} X)
      ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj (CommRingCat.of (Coeff.{u, u + 1} Λ))))
    (forget₂ CommRingCat RingCat)

/-- Sections of an intrinsic module sheaf, with their canonical constant scalar action.
Restriction uses the sheafification unit and preserves the underlying sections and
restriction maps. The terminal-object API merely packages these fixed scalar modules
as a `ModuleCat`-valued presheaf. Source: Lu--Zheng, Theorem 4.27(1), ILO XI §4.1,
Stacks 03D1 (blueprint: lem-trf-orgogozo-good-modification). -/
def orgogozoModuleSections (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (M : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) :
    (EtaleSite.{u, u + 1} X)ᵒᵖ ⥤ ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ) :=
  (PresheafOfModules.forgetToPresheafModuleCat
    (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
      ((PresheafOfModules.restrictScalars (orgogozoConstantScalars X Λ)).obj M.val)

/-- Orgogozo's good-modification theorem in the integral Noetherian case.
Source: Lu--Zheng, Theorem 4.27(1), p. 37
(blueprint: lem-trf-orgogozo-good-modification).

Proof plan (the DAG proof, preserving its dependency references):
1. Use the fixed finite ring $\Lambda$, its invertible annihilator, and the universal property
$P_r$ of [def-trf-orgogozo-induction-data]. We prove $A_{\mathrm{pr}}(\delta,r,d)$
simultaneously for all reduced excellent Noetherian bases $S$ of dimension $\le\delta$: if
$f:X\to S$ is proper with fibre dimensions $\le d$ and $K\in D^b_c(X,\Lambda)\cap D^{\ge0}$,
there is an alteration $T\to S$ carrying $P_r(f_T,K_T)$. Induct lexicographically on
$(\delta,r+2,d)\in\mathbf N^3$, with $r\ge-2$. After proving all $d$ at fixed $(\delta,r)$ we
will deduce the analogous assertion for arbitrary finite-type sources by affine-source
compactification. All arbitrary finite-type uses in the induction have smaller $(\delta,r)$; all
uses with unchanged $(\delta,r)$ have proper source and smaller $d$. For an empty source or base
take the identity. For $r=-2$ take the identity: inverse image is exact and a bounded-below
injective resolution computes right derived direct image in nonnegative degrees, so the cone of
a comparison for $K\in D^{\ge0}$ lies in $D^{\ge-1}$.

2. At any stage an alteration carrying $P_r$ can be replaced by a modification carrying $P_r$.
Apply [lem-trf-alteration-finite-refinement] to $T\to S$ to obtain $\widetilde T\to T$, $S'\to
S$, and finite surjective $\widetilde T\to S'$. Universality in $P_r$ preserves it on
$\widetilde T$; [lem-trf-nearby-finite-base-descent] then gives $P_r$ over $S'$. Thus the
induction hypotheses supply modifications as well as alterations, without invoking the theorem
being proved. Finitely many such modifications can be replaced by their common refinement
[lem-trf-modifications-zariski-refinement]. For a reducible reduced base first work on its
finitely many reduced irreducible components; their disjoint union is finite surjective. The
componentwise alterations, followed by this finite cover, form an alteration, and the same
finite descent and refinement give the modification version on the original base.

3. Here is the passage from the proper assertions for all $d$ to arbitrary finite-type sources
at fixed $(\delta,r)$. A finite affine cover of $S$ reduces to affine base, with
[lem-trf-modifications-zariski-refinement] combining the local modifications. Cover $X$ by
finitely many affine opens. On any geometric point in such an open the source's strict
localization is unchanged, so the jointly conservative strict-local description
[lem-trf-oriented-nearby-strict-local-description] identifies the comparisons before and after
restricting to that open, including after any preliminary base change. Each affine chart over
affine $S$ embeds into affine space by finitely many algebra generators;
[det-nagata-affine-opens-projective] supplies its proper projective closure. Extension by zero
to this closure is exact and has the original stalks on the open and zero stalks on its
complement [lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-extension-by-zero-stalks]. Its
cohomology is therefore constructible: keep the finitely many original constructible strata and
add the closed complementary stratum with zero value [def-weil-pbc-etale-constructible-sheaf].
Apply the proper assertion at the closure's own finite fibre bound
[lem-fin-finite-type-fibre-dimension-bound]; that bound need not equal the original chart's
bound. Restricting comparisons back gives $P_r$ on each chart. A common modification handles all
charts.

4. For the proper induction step assume all smaller triples known. Reduce to integral bases by
Step 2; A finite-type algebra over an excellent ring remains excellent
[lem-exc-finite-type-localization-excellent]. For any integral alteration or modification, the
dimension formula [lem-exc-dimension-formula-universally-catenary-finite-type-domain] on affine
charts reads
$\operatorname{ht}(q)+\operatorname{trdeg}_{\kappa(p)}\kappa(q)=\operatorname{ht}(p)$, since the
generic extension is finite. Thus each local dimension is at most $\delta$. All ensuing reduced
refinements remain excellent Noetherian with the required dimension bound. A bounded nonnegative
complex reduces by its finitely many truncation triangles [lem-weil-pbc-truncation-triangle] to
its cohomology sheaves: $H^q(K)[-q]$ needs $P_{r-q}$, with $q\ge0$. The $q=0$ case is the
current sheaf assertion proved below; positive $q$ uses a smaller second parameter. If $r-q<-2$,
the nonnegative-complex bound from Step 1 suffices. Ordinary comparisons are natural
transformations of exact derived functors [def-trf-oriented-nearby-cycles], so their cone long
exact sequences transfer the vanishing through these finitely many triangles. We can therefore
assume $K=F$ a constructible sheaf in degree zero.

5. Now let $f$ be proper and $F$ a constructible sheaf. The finite-pushforward embedding
[lem-weil-pbc-constructible-module-finite-pushforward-embedding] gives $0\to F\to F'\to Q\to0$,
with $F'=\bigoplus p_{i,*}\underline{M_i}$, each $p_i$ finite and each $M_i$ finite. The
cokernel $Q$ and these finite direct images are constructible by [thm-constructible-serre] and
the proper finiteness statement [lem-weil-pbc-etale-proper-direct-image-finiteness] (relative
dimension zero). The induction hypothesis at $(\delta,r-1,d)$ gives $P_{r-1}(f,Q)$ after a
modification. The cone triangle for the short exact sequence has $H^{j-1}(C_Q)\to H^j(C_F)\to
H^j(C_{F'})$; thus $P_r(f,F')$ suffices. Finite-source exchange
[lem-trf-nearby-proper-source-exchange] transfers $P_r(fp_i,\underline{M_i})$ to
$P_r(f,p_{i,*}\underline{M_i})$. Finite direct sums cause no additional issue, and finite $p_i$
do not increase the fibre dimension. It remains to handle proper morphisms with constant finite
module coefficients.

6. Replace a proper source by the finite disjoint union of its reduced irreducible components.
Its Cech nerve is a proper hypercover, all of whose terms remain finite over the source. Terms
in positive simplicial degree only require $P_{r-i}$, with $r-i<r$, so the induction hypothesis
handles them after finitely many common refinements. Proper hyperdescent
[lem-trf-nearby-proper-hyperdescent] then reduces the degree-zero contribution to proper
integral sources, still with constant coefficients and the same fibre bound. This also removes
nilpotents of the source; it does not assume that a nonreduced source factors through the
reduced image. Thus in what follows both source and base may be taken integral.

7. For an integral proper source not dominating the integral base, its reduced closed image
$F\subsetneq S$ has dimension at most $\delta-1$: a strict chain of irreducible closed subsets
inside $F$ can be extended by $S$. The source is reduced, so its map factors through $F$. The
induction hypothesis on base dimension supplies a modification $F'\to F$ carrying $P_r$ for
$X\to F$. Apply [lem-trf-modification-closed-image-lifting] to $F'\to F\hookrightarrow S$. It
supplies $p:S'\to S$ and $G\to F\times_S S'$ finite surjective with an $F$-map $G\to F'$.
Universality gives $P_r$ over $G$; [lem-trf-nearby-finite-base-descent] gives it over $F\times_S
S'$, and [lem-trf-nearby-closed-image] gives it for $X\times_S S'\to S'$. The closed-image
comparison applies to the possibly nonreduced total transform because the base-changed source
factors through it; the finite-descent lemma permits a nonreduced base. If $\delta=0$, the
proper nowhere dense image is empty, so this case is already trivial.

8. For a proper dominant integral source use [lem-trf-plurinodal-proper-hypercover]. After an
integral alteration of the base, its proper hypercover $Y_\bullet\to X_T$ has degree zero a
finite disjoint union of plurinodal towers and a proper part with nowhere dense image. The
plurinodal towers have length at most $d$, since their length is the original generic fibre
dimension. The summand with nowhere dense image, still with constant coefficients, is handled by
Step 6 (its finite reduced-component cover; positive simplicial terms need only $P_{r-i}$)
followed by Step 7 for each integral component, none of which dominates $T$; Step 7 lowers the
base dimension, so no bound on the fibre dimension of this summand is needed. For $1\le i\le
r+1$, each $Y_i\to T$ is proper of finite type and has some finite fibre bound $d_i$; apply the
hypothesis at $(\delta,r-i,d_i)$. No bound $d_i\le d$ is claimed or needed. Successively refine
the base to make these finitely many conditions simultaneous. Proper hyperdescent then reduces
$P_r$ for $X_T$ to $P_r$ for the constant-coefficient plurinodal towers.
Alteration-to-modification descent is available from Step 2.

9. Prove the remaining plurinodal assertion. A tower of length zero is an identity, so its
nearby cycles commute with every base change by [lem-trf-nearby-smooth-source-exchange]. For a
tower of length $e\ge1$ write $f=gh$ where $h:X\to Y$ is its last semistable curve factor and
$g:Y\to T$ has length $e-1$. Fix the finite constant module $M$. Proper finiteness
[lem-weil-pbc-etale-proper-direct-image-finiteness], with relative dimension one, gives
$Rh_*\underline M\in D^{[0,2]}_c(Y,\Lambda)$; no freeness or finite Tor dimension of $M$ is
used. Apply the proper induction hypothesis at $(\delta,r,e-1)$ to both $(g,Rh_*\underline M)$
and $(g,\underline M)$. A common refinement makes both $P_r$ simultaneously true. Both maps are
proper and have strictly smaller third parameter, so the modified induction ordering in Step 4
applies.

10. Take any preliminary base change, any further $T'\to T$, and any lifted geometric
specialization. Let $C$ be the sliced comparison cone for $(f,\underline M)$ on the geometric
special fibre $X_{a'}$. By proper-source exchange [lem-trf-nearby-proper-source-exchange],
$Rh_{a',*}C$ is the corresponding sliced cone for $(g,Rh_*\underline M)$, hence has zero
cohomology in degrees $\le r$. On the smooth locus of $h$, smooth-source exchange
[lem-trf-nearby-smooth-source-exchange] identifies each stalk of $C$ with the cone for
$(g,\underline M)$ at its image. The latter also vanishes in degrees $\le r$. Thus $E=\tau_{\le
r}C$ is supported on the chosen closed singular subscheme of the curve factor, finite over
$Y_{a'}$. All these comparisons are the ordinary counit-defined maps; an abstract isomorphism of
the two objects would not suffice.

11. The complex $E$ is bounded: for a constant sheaf the two terms of the comparison lie in
$D^{\ge0}$, so $C\in D^{\ge-1}$ and $E\in D^{[-1,r]}$. Right derived direct image is left
t-exact, hence $\tau_{\le r}Rh_*E\simeq\tau_{\le r}Rh_*C=0$. The ordinary open--closed triangle
[lem-weil-pbc-etale-compact-support-open-closed-triangle], with structure map the identity of
the geometric special fibre, gives $E\simeq i_*i^*E$ because its open restriction is zero. On
this finite closed support, direct image is exact: its geometric stalk is the finite product of
the stalks over that point [lemma-weil-pbc-finite-direct-image-exact,
lemma-weil-pbc-finite-stalk-formula]. The stalk and exactness assertions apply to modules by the
faithful exact forgetful functor to abelian sheaves
[lem-weil-pbc-module-sheaves-colimits-forgetful]; underived direct image has the same sections
after forgetting. Consequently $Rh_*E$ is still concentrated in $[-1,r]$, and therefore is zero.
Apply [lem-trf-finite-support-defect-conservativity] to $h_{a'}$ and the finite closed support:
it gives $E=0$. The choices of the preliminary base change, comparison base change and
specialization were arbitrary. The conservative strict-local description
[lem-trf-oriented-nearby-strict-local-description] therefore gives $P_r(f,\underline M)$. This
proves the plurinodal case and closes the induction step.

12. The lexicographic induction now proves $A_{\mathrm{pr}}$ for every $d$, and then the
finite-type version by Step 3. Every branching operation in the proof used only finitely many
refinements at a fixed $r$: the embedding is finite, the cohomology range is finite, and
hyperdescent needs degrees only $0,\ldots,r+1$. Hence each application yields one proper
alteration and, by Step 2, one modification; no infinite composite of modifications has been
taken. In particular this establishes truncated universal comparison over every integral
excellent finite-dimensional arithmetic model.

13. Return to the item, with integral Noetherian $S$ of possibly infinite Krull dimension. Cover
$S$ by finitely many affine opens $U_i$. For each $U_i$, [lem-trf-nearby-spread-out] descends
$(X_{U_i},K_{U_i})$ to an integral affine finite-type $\mathbf Z[1/m]$-model $(X_i^0\to
S_i^0,K_i^0)$. Choose $[a_i,b_i]$ containing the cohomology of $K_i^0$ and a finite fibre bound
$d_i$ from [lem-fin-finite-type-fibre-dimension-bound]. Use the shifted complex $K_i^0[a_i]$,
with cohomology in $[0,b_i-a_i]$, and apply the induction just proved with a sufficiently large
$r$, then shift back. Specifically choose the shifted degree at least $2d_i+(b_i-a_i)$:
[lem-trf-nearby-dimension-bound] bounds the unshifted nearby cycles after every base change by
$[a_i,b_i+2d_i]$, and their cones by $[a_i-1,b_i+2d_i]$. Vanishing through the chosen top degree
therefore makes every comparison cone zero. We have obtained a modification of $S_i^0$ for which
the original, unshifted complex is universally $\Psi$-good.

14. Pull each arithmetic modification back to $U_i$ and take the reduced closure of the dense
isomorphism open as in [lem-trf-nearby-spread-out]. Universality of $P_r$ transfers the
vanishing to these modifications of $U_i$; the same uniform bounds turn it into full
$\Psi$-goodness. A global modification $r:S_1\to S$ dominating all of them exists by
[lem-trf-modifications-zariski-refinement]. Goodness persists under arbitrary base change by the
two-change quantifier in $P_r$ (or by composing the ordinary comparison maps). The comparison
over any $S_2\to S_1$ is an isomorphism on the opens lying over the $U_i$, hence everywhere. The
refinement is proper and is an isomorphism above a dense open $U\subset S$ whose inverse image
is dense; thus it has exactly the modification properties required in the item. Naming the fibre
product and its projections gives $X_1,r_X,f_1$, and the definition
[def-trf-oriented-nearby-cycles] identifies the conclusion with invertibility of the specified
ordinary comparison for every $S_2\to S_1$.
-/
theorem exists_modification_isPsiGood
    {X S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 1 ≤ m) (hmΛ : ∀ x : Λ, m • x = 0)
    (hmS : IsUnit (m : Γ(S, ⊤)))
    (K : EtaleDerived X Λ)
    (hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff Λ) K)
    (hKc : ∀ q : ℤ,
      ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
        Nonempty (orgogozoModuleSections X Λ
          ((DerivedCategory.homologyFunctor
            ((etaleDatum.{u, u + 1} X).modules (Coeff Λ)) q).obj K) ≅
            (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj)) :
    ∃ (S₁ : Scheme.{u}) (r : S₁ ⟶ S) (U : S.Opens),
      IsProper r ∧ Dense (U : Set S) ∧ IsIso (pullback.snd r U.ι) ∧
      Dense (r ⁻¹' (U : Set S)) ∧
      IsPsiGood (pullback.snd f r) Λ
        (((etaleModules (pullback.fst f r)).pull (Coeff Λ)).obj K) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
