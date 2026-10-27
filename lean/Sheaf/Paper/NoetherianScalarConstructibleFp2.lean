/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.YonedaExtOneFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.FiniteConstantModelResolution
import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.ProEtaleInternalHomLowerBound
import Sheaf.Algebra.Homology.RHomContinuityTriangleClosure
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.Paper.ClosedSupportBoundedContinuity
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity
import Sheaf.Paper.BoundedFiniteModelGeneration
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono

/-! # Hom and Yoneda Ext continuity for Noetherian scalar-model constructibles

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3 and Theorem 6.2(3),
with finite scalar resolutions; Stacks 08JI, 06XU and 06XV
(blueprint: lem-sfb-noetherian-scalar-constructible-fp2).

The two comparisons use the ordinary internal module category, with arbitrary
filtered targets. The second has the actual Yoneda quotient as its carrier.
The coefficient disjunction retains all continuous algebraic-closure-valued
functions and does not add the distinct finite-subextension coefficient object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

attribute [local instance] CategoryTheory.HasExt.standard

namespace AlgebraicGeometry.ProEtale

/-- Hom and Yoneda Ext¹ from any finite constant scalar-model constructible commute
with small filtered colimits of arbitrary uncompleted internal modules.
The normalized Yoneda comparison supplies the existing Baer group; the assertion
holds for every such comparison, so no presentation or arbitrary arrow is chosen.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1),(2), Theorem 6.2(3), and finite scalar
resolutions; Stacks 08JI, 06XU, 06XV. The finite nonregular coefficient extension is
the agent argument recorded in the DAG, rather than a verbatim assertion of HRS
(blueprint: lem-sfb-noetherian-scalar-constructible-fp2).

Proof plan (the node's seven steps):
1. Work with ordinary ringed-site module sheaves via the evaluation-compatible derived
equivalence [lem-sfb-module-object-ringed-site-derived-comparison]. By
[lem-weil-pbc-module-sheaves-colimits-forgetful] and
[lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact], filtered module-sheaf colimits are
exact and their cohomology is computed by taking filtered colimits of cohomology sheaves: kernels
and cokernels commute with these colimits. The Noetherian scheme X has Noetherian underlying
space by [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal]. Every subset of that space is
quasi-compact by [lem-sfb-noetherian-space-compact-subsets]; hence X is quasi-separated as well
as quasi-compact. These facts apply also to open and closed subschemes appearing in a finite
stratification. The ringed-site category is Grothendieck by
[lem-pur-ringed-site-grothendieck-abelian] and has enough injectives by
[lem-sp-grothendieck-enough-injectives].
2. On a chart where a finite constant local model L equals B\otimes_{\underline R}\underline P,
construct an augmented resolution F^\bullet\to L[0] with F^a finite free and F^a=0 for a>0. For
R=\mathcal O_E use [lem-sfb-finite-constant-model-two-term-free-resolution]; R=\mathbf Z_\ell is
the case E=\mathbf Q_\ell. For R=\mathbf Q_\ell,E,\Omega, apply the field clause of
[lem-sfb-scalar-finite-free-resolutions] and the rank-preserving scalar extension of
[lem-sfb-constant-finite-free-presentation-extension], giving a degree-zero resolution. In
particular this uses the scalar field \Omega itself, without restricting continuous functions to
finite subextensions. For finite R=A, identify B with the constant A-ring using
[lem-weil-pbc-finite-discrete-condensed-ring-constant] and
[lem-weil-pbc-finite-discrete-scheme-ring-constant]. Choose a finite free surjection A^{r_0}\to
P. Its kernel K_1 is a finite set because A^{r_0} is finite; the map A^{K_1}\to K_1 sending basis
vectors to their labels is surjective. Repeat on its finite kernel. The composites give an exact
augmented resolution by finite free A-modules in degrees at most zero. Exact constant
sheafification, from [lem-sfb-constant-finite-free-presentation-extension], gives the required
F^\bullet. No finite projective dimension of P is asserted.
3. Write H_T(K,N)=R\mathcal Hom_{\Lambda_T}(K,N). Fix a small filtered diagram N_i in D^{\ge c}.
Good truncation replaces degree c by coker(d^{c-1}) and all lower terms by zero, retaining the
higher terms and their maps; this is functorial and supplies target representatives zero below c,
by [def-sbc-standard-tstructure-derived-category]; exactness in step 1 preserves their colimit.
On any chart of step 2, [lem-weil-pbc-ringed-site-bounded-free-rhom-model] represents H_T(L,N_i)
by the ordinary Hom complex. Its degree n term is the finite sum \bigoplus_{c-n\le
a\le0}(N_i^{a+n})^{r_a}, with differential d_N f-(-1)^n f d_F. Each term commutes with the
filtered colimit, and the termwise comparison commutes with that differential. It is therefore an
isomorphism of complexes, induced by the original target cocone. Slice restriction is exact by
[lem-pur-site-restriction-module-adjunction-exact]; it commutes with colimits because colimits
are sheafified sectionwise colimits (step 1), and slice restriction commutes with abelian
sheafification by [lem-cbc-sieve-slice-sheafification]. Internal Hom restricts to this
computation by [lem-weil-pbc-ringed-internal-hom-exact-restriction], and these restrictions
identify the module-object Hom by step 1. Apply [lem-sfb-sheaf-cover-local-isomorphism] to each
cohomology sheaf to obtain the global internal-Hom comparison isomorphism for L. Moreover
H_T(L,N) lies in D^{\ge c} by [lem-weil-pbc-proetale-internal-hom-lower-bound], since L is a
sheaf in degree zero. Thus L satisfies the property P_T defined in
[lem-sfb-rhom-continuity-triangle-closure], with d_L=0.
4. Let t:S\hookrightarrow V be a reduced closed immersion into an open subscheme of X, and let L
on S have a finite constant local model. Its open complement is quasi-compact by step 1, so
[lem-sfb-open-closed-internal-hom-formulas] applies and identifies H_V(t_*L,N) with
t_*H_S(L,Rt^!N). By [lem-sfb-closed-support-bounded-continuity], Rt^! preserves a common
cohomological lower bound and commutes with filtered colimits of such targets. Apply step 3 to
the resulting bounded-below diagram on S. Ordinary t_* is exact by
[lem-weil-pbc-condensed-open-closed-recollement] and is left adjoint to the underived support
functor by [det-lem-formal-closed-support-adjunction]; it therefore commutes with sheaf colimits
by [lem-weil-pbc-left-adjoint-preserves-colimits]. Consequently the displayed formula gives
P_V(t_*L), with bound zero. Naturality of the internal-Hom formula identifies this comparison
with the evaluation-induced map for the original cocone.
5. For every open v:V\hookrightarrow X and t,L as in step 4,
[lem-sfb-rhom-continuity-open-extension] gives P_X(v_!t_*L). The class P_X contains zero, is
invariant under isomorphism and closed under shifts and extensions by
[lem-sfb-rhom-continuity-triangle-closure]. Apply [lem-sfb-bounded-finite-model-generation] to
this class: X has Noetherian underlying space, the coefficients are a commutative condensed ring,
and step 4 followed by open extension verifies every required generator. Thus P_X(C[0]) holds for
every C in the stated scalar-model constructible heart, including integral torsion models. This
application uses only finitely many strata and triangles for C.
6. Apply step 5 to N_i=M_i[0]. We obtain colim_i H_X(C,M_i[0])\simeq H_X(C,(colim_iM_i)[0]).
Every internal Hom here lies in D^{\ge0}, by [lem-weil-pbc-proetale-internal-hom-lower-bound].
Choose functorial good truncation representatives zero in negative degrees, as in
[def-sbc-standard-tstructure-derived-category]. Since X is qcqs,
[det-pe-bounded-continuity-sections], with U=X, common lower bound zero and coefficient sheaf
\Lambda_X, gives for q=0,1 the isomorphisms colim_i H^q(R\Gamma(X,H_X(C,M_i[0])))\simeq
H^q(R\Gamma(X,H_X(C,(colim_iM_i)[0]))). Exact filtered colimits allow the same truncation
representatives for the source colimit in step 5. All maps remain those of the original cocone;
there is no cohomological-dimension bound or completion in this argument.
7. By [lem-pur-rhom-global-sections] and shift compatibility in
[lem-weil-pbc-ringed-internal-hom-exact-restriction], the groups of step 6 are Hom_{D(\mathcal
A_X)}(C[0],M_i[q]) and the analogous group for colim_i M_i. At q=0 this is ordinary Hom: choose a
nonnegative injective resolution using [lem-weil-pbc-complex-injective-resolution-mono] and step
1, and apply [lem-weil-pbc-ext-via-injective-resolution]. For this resolution 0\to M\to I^0\to
I^1\to\cdots gives H^0 Hom(C,I^\bullet)=ker(Hom(C,I^0)\to Hom(C,I^1))=Hom(C,M), directly from the
kernel universal property. At q=1, [lem-coef-yoneda-derived-ext-comparison] identifies the
derived group naturally with Yoneda Ext^1. Its naturality in M sends an extension to its pushout
along M_i\to colim_i M_i, and respects Baer sum. Hence the q=0,1 isomorphisms of step 6 are
exactly both maps in the statement. Since these are isomorphisms, equality of two Hom maps or
extension classes in the colimit is also detected in the source colimit; both injectivity and
surjectivity follow.
-/
theorem noetherian_scalar_constructible_fp2
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hC : IsConstantModelConstructible Λ X C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [HasColimit M] :
    IsIso (colimit.post M (preadditiveCoyoneda.obj (Opposite.op C))) ∧
    ∀ c : YonedaDerivedExtComparison
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (colimit.post M (c.yonedaExtOneFunctor C)) := by
  sorry

end AlgebraicGeometry.ProEtale
