/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.Paper.PullbackFiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation
import Sheaf.Paper.FiniteScalarLocalModelComplete
import Sheaf.Paper.SupportedKernelImageExtensionComplete
import Sheaf.Paper.FiniteModelSheafQuotientConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.IntegralQuotientDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityCoefficientRestriction
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.SupportedRationalLatticeGeneration
import Sheaf.Paper.SupportedCoefficientLocalization

/-! # Etale coinduction of supported finite scalar local models

Source: agent-formulated etale subproblem below the supported generator obligation,
Hemo--Richarz--Scholbach, Lemma 5.3(1), for bounded continuity only, and
Bhatt--Scholze, Lemma 5.4.3 and Proposition 6.8.4, for comparison and lattices.
An exact full-generality hull-generation reference remains WANTED.
(blueprint: lem-sfb-etale-supported-model-coinduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Actual derived direct image along a qcqs etale morphism sends every supported
finite scalar local model in degree zero into the supported model hull.
The five coefficient cases use all continuous functions, with discrete topology only
in the finite case. The algebraic-closure coefficient is not included.
Quasi-compactness and quasi-separatedness of `e` follow from the qcqs scheme hypotheses.
Every intermediate scheme in `p` is qcqs because its arrows are the admissible open or
closed immersions. The empty support chain is allowed.

Source: the agent-formulated etale subproblem, HRS Lemma 5.3(1) (bounded continuity),
BS Lemma 5.4.3 and Proposition 6.8.4 (comparison and lattice input); exact hull reference
WANTED (blueprint: lem-sfb-etale-supported-model-coinduction).

Proof plan (the eleven steps of the DAG; no unbounded continuity is asserted):
1. First work with any finite discrete coefficient ring $B$ killed by a power of $\ell$. Every
   finite scalar-model constructible module $H$ on a qcqs scheme $V$ has $H[0]\in\mathcal
   G_V(B)$. Indeed refine its finite constructible partition by the finite qcqs open-closed
   tree. Each leaf restriction is a finite scalar local model (pull back its witnessing cover
   and scalar presentation). At an internal vertex use $0\to j_!j^*H\to H\to i_*i^*H\to0$. Apply
   the exact extensions on the path to the root. Induction on this finite tree, using the
   short-exact-sequence triangles, expresses $H[0]$ as finite triangle extensions of the
   supported leaf generators. This uses only the given finite partition, not Noetherian
   induction.

   Uses: lem-fix-constructible-open-closed-refinement,
   new-unbounded-pullback-finite-constant-local-model, lem-weil-pbc-proetale-ringed-open-closed,
   lem-sfb-internal-module-operations-transport, lem-weil-pbc-complex-ses-triangle.

2. Every classical $B$-module sheaf $\nu_V^*F$ on a qcqs $V$, in degree zero, lies in $\mathcal
   G_V(B)$. The module constructible-approximation theorem writes $F$ as a small filtered
   colimit of constructible étale $B$-modules. The fixed-module constructibility comparison and
   the finite discrete encoding identify their inverse images with finite scalar-model
   constructible internal modules. These belong to the hull by step 1. The exact inverse image
   $\nu_V^*$ is a left adjoint, so preserves that colimit. Apply the hull's strict
   filtered-colimit clause to their degree-zero complexes, all with lower bound zero. No finite
   presentation is asserted for $F$ itself.

   Uses: lem-weil-pbc-module-sheaf-colimit-constructible,
   lem-weil-pbc-fixed-module-constructible-origin,
   lem-weil-pbc-constructible-etale-module-sheaf-comparison,
   lem-sf-finite-discrete-encoding-constructibility, sk-thm-pe-classical-sheaves.

3. More generally every bounded-below classical internal $B$-complex lies in the hull. Its
   cohomology sheaves are classical, since the comparison inverse image is exact, and step 2
   puts each of them in the hull. The truncation triangle and the concentrated-single theorem,
   by induction on a finite cohomological interval, put every bounded good truncation in the
   hull. Choose a representative $C$ zero below a common integer $a$ (replace its degree $a$ by
   the cokernel of the preceding differential). The good upper truncations $\tau_{\leq m}C$ form
   a strict direct sequence by their canonical inclusions. In each fixed degree the sequence is
   eventually $C$, so its termwise colimit is $C$. All these truncations are zero below $a$. The
   specified strict bounded-below colimit closure therefore puts $QC$ in the hull. This argument
   does not require an unbounded colimit-continuity theorem for direct image.

   Uses: sk-thm-pe-classical-sheaves, lem-sf-derived-truncation-triangle,
   lem-sf-derived-concentrated-single, lem-weil-pbc-small-module-diagrams-grothendieck.

4. For $\Lambda=B$, a finite coefficient ring, put $M=JL$ on $S$. The admissible finite support
   chain makes $M$ constructible: complete the chain to a finite open-closed tree, with $L$ on
   the specified leaf and zero on its complementary leaves. Exact support extension gives the
   stated restrictions; the finite discrete encoding identifies this with fixed-module
   constructibility. Thus the fixed-module origin theorem gives $M\cong\nu_S^*F$ for an étale
   module $F$. As $e$ is qcqs, bounded-below direct-image comparison gives
   $Re_*M[0]\cong\nu_T^*Re_{\mathrm{et},*}F[0]$. The coefficient-direct-image conjugation makes
   this a comparison of the actual internal direct images. Its target is bounded below (use a
   nonnegative injective resolution of $F$). Step 3 proves the required membership, including
   boundary cohomology.

   Uses: lem-weil-pbc-proetale-ringed-open-closed, lem-sfb-internal-module-operations-transport,
   lem-sf-finite-discrete-encoding-constructibility,
   lem-weil-pbc-fixed-module-constructible-origin, sk-thm-pe-direct-image-comparison,
   lem-weil-pbc-finite-discrete-coefficient-direct-image-conjugation.

5. Now fix $O=\mathcal O_F$ (including $F=\mathbf Q_\ell$) and $M=JH$ for a supported integral
   finite scalar local model. Finite scalar local-model completeness and supported-extension
   completeness make $M[0]$ derived complete. A chain is a path in a finite qcqs open-closed
   tree, by adjoining the complementary siblings; take the identity pro-étale restriction in the
   supported-extension theorem. As in step 4, this $M$ is constructible with finite scalar local
   models on a finite partition. Consequently each derived reduction
   $M_n=M[0]\otimes^L_O(O/\pi^n)$ is bounded constructible in degrees $[-1,0]$. The ordinary
   finite-coefficient equivalence and the encoding comparison make $M_n$ an ordinary bounded
   complex whose cohomology sheaves are pro-étale constructible. The fixed-module
   constructibility-origin theorem writes each of them as $\nu_S^*F_q$ with $F_q$ a globally
   constructible étale sheaf, and the fixed-module bounded-origin theorem then gives an
   étale-origin witness $M_n\cong\nu_S^*L_n$ with $L_n$ bounded. This treats torsion $H$ using
   derived reductions, rather than incorrectly identifying them with ordinary quotients.

   Uses: lem-sfb-finite-scalar-local-model-complete,
   lem-sfb-supported-extension-derived-complete, lem-weil-pbc-proetale-ringed-open-closed,
   lem-sfb-finite-model-sheaf-quotient-constructible,
   lem-sf-finite-discrete-encoding-constructibility,
   lem-weil-pbc-fixed-module-bounded-constructible-origin,
   lem-sf-module-object-ordinary-coefficient-equivalence,
   lem-weil-pbc-fixed-module-constructible-origin.

6. Restriction of scalars $D((O/\pi^n)_T)\to D(O_T)$ sends the entire finite-coefficient hull
   into the integral hull. It is exact, preserves termwise colimits and products (all computed
   on underlying sheaves), hence preserves triangles and the prescribed strict colimits;
   termwise products represent derived products. A finite scalar local model remains one over
   $O$: lift a finite presentation matrix over $O/\pi^n$ to $O$ and adjoin the finitely many
   relations $\pi^n e_j=0$ for its generators. Extending this presentation to the coefficient
   sheaf gives precisely its restricted scalar model, because the cokernel of $\pi^n$ on $O_W$
   is the actual quotient $k_{n,W}$ (the resolution $[O_W\xrightarrow{\pi^n}O_W]$ of $k_{n,W}$
   with its augmentation, stated in the integral quotient direct-image theorem) and scalar
   extension is right exact. Scalar restriction commutes with $j_!$ and $i_*$: the same
   underlying sheaf and scalar action give their adjunction comparisons. Thus each restricted
   supported generator belongs to the integral hull, and its defining minimality gives the
   assertion. This is a direct preservation-of-generators argument; it makes no assertion about
   rationalization preserving products.

   Uses: lem-sfb-internal-section-scalar-adjunction,
   lem-weil-pbc-module-sheaves-colimits-forgetful, det-pe-products-derived,
   lem-sf-exact-functor-derived-triangulated, lem-sfb-internal-module-operations-transport,
   lem-sfb-integral-quotient-direct-image-comparison.

7. Set $P=Re_{*,O}(M[0])$, computed by a nonnegative injective resolution, so $P$ is bounded
   below. The derived adjunction and right-adjoint limit preservation show that $Re_{*,O}$
   preserves products. It is triangulated, so applying it to the completion Roos triangle of $M$
   identifies $P$ with the derived limit of $Re_{*,O}\operatorname{Res}_n M_n$. Scalar-change
   direct-image comparison identifies this tower with $\operatorname{Res}_n Re_{*,O/\pi^n}M_n$.
   The integral quotient direct-image theorem identifies $P\otimes^L_O(O/\pi^n)$ with
   $Re_{*,O/\pi^n}M_n$, compatibly with the quotient transitions. Hence the canonical completion
   unit of $P$ is invertible, and every reduction of $P$ is bounded-below classical, by the qcqs
   direct-image comparison and the origin witnesses in step 5.

   Uses: sk-def-sfb-module-derived-pushpull, lem-weil-pbc-right-adjoint-preserves-limits,
   lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-ring-sheaf-change-adjunction,
   lem-sfb-integral-quotient-direct-image-comparison, sk-thm-pe-direct-image-comparison,
   lem-weil-pbc-finite-discrete-coefficient-direct-image-conjugation,
   lem-pc-right-derived-functor-triangulated.

8. Steps 3 and 7 put every $Re_{*,O/\pi^n}M_n$ in its finite-coefficient hull. Step 6 puts their
   scalar restrictions in $\mathcal G_T(O)$. The two products in their Roos triangle therefore
   belong to $\mathcal G_T(O)$; rotation and shift closure put its first object there. Step 7
   identifies that object with $P=Re_{*,O}M[0]$. This proves the assertion for $\Lambda=\mathbf
   Z_\ell,\mathcal O_E$. Products and triangles are used in the ordinary ambient category
   throughout.

   Uses: lem-weil-pbc-ringed-strict-tower-homotopy-limit.

9. For the same bounded-below $P$ in step 7, the classical-adic rational generation lemma
   applies: its completeness hypothesis is exactly the canonical completion isomorphism proved
   there, and its classical finite reductions are the same $Re_{*,O/\pi^n}M_n$. It yields
   $F_T\otimes^L_{O_T}P\in\mathcal G_T(F)$. This is an additional coefficient input, not a
   consequence of the integral membership in step 8.

   Uses: lem-sfb-classical-adic-rational-hull.

10. There is a canonical scalar-compatible isomorphism $F_T\otimes^L_{O_T}Re_{*,O}M[0]\cong
   Re_{*,F}(F_S\otimes_{O_S}M)[0]$. To see it, express $F_V=O_V[1/\ell]$ by the specified
   repeated-$\ell$ telescope. Flatness identifies tensor with its exact termwise telescope on
   $M$ and on a bounded-below representative of $P$. Bounded direct-image continuity identifies
   the telescope of $Re_{*,O}M$ with $Re_{*,O}$ of the telescope of $M$. The
   coefficient-restriction comparison identifies the latter with restriction of $Re_{*,F}$ of
   the localized module. The resulting map is $F_T$-linear: its $m$-th telescope leg is induced
   by $x\mapsto\ell^{-m}\otimes x$, so multiplication by $\ell$ and every $O$-scalar commutes
   with all legs. Restricted scalar functors reflect isomorphisms. This proves the comparison
   with the actual rational direct image and puts this direct image in the rational hull by step
   9.

   Uses: det-prop-sfb-qlbar-colimit-x-invert-ell,
   lem-pe-bounded-continuity-coefficient-restriction, lem-weil-pbc-ring-sheaf-change-adjunction,
   lem-sfb-internal-section-scalar-adjunction, lem-weil-pbc-unbounded-derived-iso-cohomology,
   lem-sfb-internal-module-operations-transport.

11. Finally let $JL$ be an arbitrary rational supported finite scalar model on $S$, for $F=E$ or
   $\mathbf Q_\ell$. The supported rational lattice-generation theorem expresses $(JL)[0]$ as a
   finite iterated triangle extension of objects $(F_S\otimes_{O_S}J_OH)[0]$, where $H$ is an
   integral finite scalar local model on the source of an admissible support chain over $S$. Its
   support paths represent exactly our support chains, by adjoining complementary siblings. No
   global lattice for $L$ or scalar lift of its connecting maps is required. The ring-object map
   $a:O^c\to F^c$ supplied by that theorem need not be the standard inclusion, only an
   $\ell$-localization coefficient. Its predicate provides, on every scheme, the
   $\ell$-telescope cocone of $F_V$ over $O_V$ with zeroth leg $a_V$, hence flatness (a filtered
   colimit of free modules). These are the only properties of the inclusion that step 10 uses,
   so step 10 applies verbatim to $F_S\otimes_{O_S,a}J_OH$. The triangulated functor $Re_{*,F}$
   sends this finite extension construction to one whose generators lie in $\mathcal G_T(F)$ by
   step 10. Finite extension and repleteness closure finish the rational cases. Zero objects,
   rank zero, empty chains and empty schemes persist in every step. At no point has ordinary
   direct image along an open been replaced by lower shriek.

   Uses: lem-sfb-supported-rational-lattice-generation,
   lem-pc-right-derived-functor-triangulated, lem-sfb-supported-coefficient-localization.
-/
theorem etale_supported_model_coinduction
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
    (S T : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace T] [QuasiSeparatedSpace T]
    (e : S ⟶ T) [Etale e]
    (W : Scheme.{u}) (p : ScalarModelSupportChain S W)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hL : HasFiniteConstantLocalModel Λ W L) :
    supportedModelHull Λ T
      ((CondensedRing.moduleObjectDerivedPushforward Λ e).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale
