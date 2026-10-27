/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.PadicIntegersInvertEll
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.FiniteModelSheafQuotientConstructible
import Sheaf.Paper.FiniteScalarLocalModelComplete
import Sheaf.Paper.IntegralAmbientTowerComparison
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Paper.LocalizedDirectImageComparison
import Sheaf.Paper.QcqsConstructibleIntegralLeafModels
import Sheaf.Paper.QcqsLatticeTreeReconstruction
import Sheaf.Paper.SupportedKernelImageExtensionComplete
import Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-! # Conditional ind-etale continuity for the supported model hull

Source: agent-formulated hull-continuity obligation below blueprint latest,
sec-six-functors-basics/sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle,
refinement paragraph, via refinement (2). Hemo--Richarz--Scholbach Sections 3--4
supply the ambient setting; Lemma 5.3(1) supplies bounded input continuity only.
Exact reference WANTED; no inverse-limit continuity in the source is attributed to it.
(blueprint: lem-sfb-indetale-supported-hull-continuity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Conditional supported-model hull continuity for a qcqs map admitting finite affine
ind-etale charts. The etale premise is quantified over all qcqs schemes for the fixed
coefficient. No local model or adic transition map is assumed to descend to one stage.
All operations take place in the ordinary uncompleted module-object derived category.

Source: agent-formulated obligation subordinate to blueprint latest
`det-sf-comp-coherence-cocycle`, refinement paragraph, via refinement (2);
Hemo--Richarz--Scholbach Sections 3--4 for the ambient setting and Lemma 5.3(1)
for bounded input continuity only. Exact reference WANTED.
(blueprint: lem-sfb-indetale-supported-hull-continuity).

Proof plan (the eight steps of the DAG):

1. Put $M=JL$. It is finite scalar-model constructible on $U$, for each of the five
coefficients. Complete the finite support chain to a binary open-closed tree by adjoining the
complementary sibling at each edge. Every vertex is qcqs: a qc open of a qcqs scheme is qcqs and
a closed subscheme is qcqs. On the selected leaf $M$ restricts to $L$, and on each complementary
leaf to zero: apply $j^*j_!=1$, $i^*i_*=1$, $i^*j_!=0$, $j^*i_*=0$ successively, transporting
the section-ring statements to internal modules. Thus this finite partition witnesses the
required local scalar models, including the zero presentation on the other leaves. Its leaves
are constructible in $U$: at an open edge the inclusion is retrocompact, and at a closed edge
its complement is retrocompact; the two constructible-image lemmas apply inductively. This is a
direct construction of a witnessing partition, not a claim that support extensions are globally
locally constant.

Uses: lem-weil-pbc-proetale-ringed-open-closed, lem-sfb-internal-module-operations-transport,
lem-weil-pbc-constructible-image-retrocompact-open,
lem-weil-pbc-constructible-image-closed-retrocompact-complement.

2. For finite $\Lambda=A$, the finite discrete encoding and the fixed-module
constructible-origin theorem turn $M$ into $\nu_U^*F$ for a constructible etale $A$-module $F$.
Apply bounded-below direct-image comparison to $b$ and $F[0]$. Its hypotheses are exactly the
qcqs hypothesis on $b$ and the lower bound zero on $F[0]$; the coefficient-direct-image
conjugation identifies the internal module functor with that comparison. Hence the actual
$Rb_{*,A}M[0]$ is isomorphic to the internal encoding of $\nu_V^*Rb_{\mathrm{et},*,A}F[0]$. The
etale derived image is bounded below: a nonnegative injective resolution of $F$ computes it.
Apply the new classical-complex hull lemma with $(R,B)=(A,A)$ to obtain membership in $\mathcal
G_V(A)$. This includes open-immersion boundary contributions.

Uses: lem-sf-finite-discrete-encoding-constructibility,
lem-weil-pbc-fixed-module-constructible-origin, sk-thm-pe-direct-image-comparison,
lem-weil-pbc-finite-discrete-coefficient-direct-image-conjugation,
lem-sfb-classical-finite-scalar-restriction-hull.

3. Now fix $O=\mathcal O_F$, including $O=\mathbf Z_\ell$ by $F=\mathbf Q_\ell$, and let $H$ be
any supported integral finite scalar local model on $U$. Its source finite scalar local model is
derived complete by the finite-scalar completeness theorem. View its support chain as the tree
path constructed in step 1; supported-extension completeness with the identity pro-etale
restriction makes $H[0]$ derived complete on $U$. Step 1 also gives finite scalar-model
constructibility of $H$. Therefore the finite-model quotient theorem applies to
$K_n=H[0]\otimes^L_{O_U}(O/\pi^n)_U$: these are bounded constructible with cohomology only in
$[-1,0]$, uniformly in $n$. Encode them in fixed finite-coefficient coordinates. The
fixed-module origin theorem gives constructible etale origins for every cohomology sheaf, and
the bounded-constructible-origin theorem yields $K_n\cong\nu_U^*L_n$ with $L_n$ a bounded etale
complex, which can be taken in degrees $\geq-1$. These are derived quotients, so torsion in $H$
is retained in degree $-1$.

Uses: lem-sfb-finite-scalar-local-model-complete, lem-sfb-supported-extension-derived-complete,
lem-sfb-finite-model-sheaf-quotient-constructible,
lem-sf-finite-discrete-encoding-constructibility,
lem-weil-pbc-fixed-module-constructible-origin,
lem-weil-pbc-fixed-module-bounded-constructible-origin,
lem-sf-module-object-ordinary-coefficient-equivalence.

4. Set $P=Rb_{*,O}H[0]$. Apply the integral ambient tower comparison to the complete $H[0]$ of
step 3 and the qcqs map $b$. It says that $P$ is complete, with the canonical
transition-compatible isomorphisms $P\otimes^L_O(O/\pi^n)\cong Rb_{*,O/\pi^n}K_n$ and $P\cong
R\lim_n\operatorname{Res}_nRb_{*,O/\pi^n}K_n$. Its final clause, using the etale origins $L_n$
of step 3, identifies these finite-coefficient images with
$\nu_V^*Rb_{\mathrm{et},*,O/\pi^n}L_n$. These etale images are bounded below, uniformly by $-1$
(resolve each bounded-below complex by an injective complex with the same lower bound). Also $P$
is bounded below by zero, from a nonnegative injective resolution of the sheaf $H$. No
properness or cohomological-dimension hypothesis is used.

Uses: lem-sfb-integral-ambient-tower-comparison.

5. Apply the classical-complex hull lemma on $V$ to $Rb_{\mathrm{et},*,O/\pi^n}L_n$ with the
canonical pair $(R,B)=(O,O/\pi^n)$. Each $\operatorname{Res}_nRb_{*,O/\pi^n}K_n$ belongs to
$\mathcal G_V(O)$. The strict-tower homotopy-limit theorem supplies the Roos distinguished
triangle with the two derived products of these terms and first vertex their derived inverse
limit. Product, triangle and shift closure put that first vertex in $\mathcal G_V(O)$. The
actual completion isomorphism of step 4 identifies it with $P$. Taking $H=M$ proves the integral
cases. This uses products in the ordinary ambient derived category and does not interchange
rationalization with a product.

Uses: lem-sfb-classical-finite-scalar-restriction-hull,
lem-weil-pbc-ringed-strict-tower-homotopy-limit.

6. For rational coefficient $F$ ($F=\mathbf Q_\ell$ or $E$), step 1 makes $M$ constructible with
finite scalar local models. The qcqs integral-leaf-model theorem produces a finite qcqs
open-closed tree and, on every leaf, a lisse $O_F$-module $B_W$ whose scalar extension along the
canonical inclusion equals the leaf restriction of $M$. Canonical integral-to-rational scalar
extension is flat by the coefficient-localization theorem; thus the hypotheses of lattice-tree
reconstruction hold at every vertex. Reconstruction expresses $M[0]$ as finite triangle
extensions of $F_U\otimes^L_{O_U}J_WB_W[0]$, with $J_W$ the supported extension along the leaf
path. Each $B_W$ is a finite scalar local model since it is locally finite free. The coefficient
map in these objects is the canonical inclusion, not a newly chosen scalar map. If $F$ was given
abstractly rather than as a finite subfield of an algebraic closure, choose a $\mathbf
Q_\ell$-embedding and transport these statements along the induced topological coefficient
isomorphism; finite models, products, strict bounded-below colimits and actual direct images
transport under that exact equivalence.

Uses: lem-sfb-qcqs-constructible-integral-leaf-models, lem-sfb-qcqs-lattice-tree-reconstruction,
det-prop-sfb-qlbar-colimit-x-invert-ell.

7. For each integral supported $H=J_WB_W$ from step 6, repeat steps 3-4. Then $P=Rb_{*,O}H[0]$
is bounded below and derived complete, and each of its finite derived reductions is $\nu_V^*$ of
a bounded-below etale complex. These are precisely the hypotheses of the classical-adic
rational-hull lemma, which gives $F_V\otimes^L_{O_V}P\in\mathcal G_V(F)$. The
localized-direct-image comparison applies because $b$ is qcqs and $H[0]$ is bounded below. For
the actual canonical coefficient inclusion it gives the isomorphism $F_V\otimes^L_{O_V}P\cong
Rb_{*,F}(F_U\otimes^L_{O_U}H[0])$. Thus the direct image of each generator of the finite
extension construction in step 6 lies in $\mathcal G_V(F)$. This rational-hull input is separate
from the integral hull conclusion of step 5.

Uses: lem-sfb-classical-adic-rational-hull, lem-sfb-localized-direct-image-comparison.

8. The actual module-derived direct image is triangulated. Apply it to the finite
distinguished-triangle extension construction in step 6. Step 7 puts every generator image in
$\mathcal G_V(F)$, and finite extension and repleteness closure then give
$Rb_{*,F}M[0]\in\mathcal G_V(F)$. Together with steps 2 and 5 this proves all five coefficients.
Empty trees, rank-zero scalar models, zero coefficients, zero objects and empty schemes yield
zero or the same identity/finite-extension argument, so introduce no nonempty hypothesis. In
fact the argument proves the conclusion for every qcqs $b$. Consequently it proves the requested
conditional assertion without using the etale-coinduction premise or the local affine ind-etale
presentation; no common-stage descent is asserted. Those hypotheses remain in the statement
unchanged.

Uses: lem-pc-right-derived-functor-triangulated.
-/
theorem indetale_supported_hull_continuity
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
    (hetale : ∀ (S T : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      [CompactSpace T] [QuasiSeparatedSpace T] (e : S ⟶ T)
      [Etale e] [QuasiCompact e] [QuasiSeparated e]
      (W : Scheme.{u}) (p : ScalarModelSupportChain S W)
      (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)),
      HasFiniteConstantLocalModel Λ W L →
        supportedModelHull Λ T
          ((CondensedRing.moduleObjectDerivedPushforward Λ e).obj
            ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L))))
    (U V : Scheme.{u})
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (b : U ⟶ V) [QuasiCompact b] [QuasiSeparated b]
    (hcharts : ∃ (n : ℕ) (D : Fin n → U.Opens),
      (∀ x : U, ∃ a : Fin n, x ∈ D a) ∧
      ∀ a : Fin n, IsAffineOpen (D a) ∧
        ∃ (Va : V.Opens) (f : (D a).toScheme ⟶ Va.toScheme),
          IsAffineOpen Va ∧ proAffineEtale f ∧ (D a).ι ≫ b = f ≫ Va.ι)
    (W : Scheme.{u}) (p : ScalarModelSupportChain U W)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W))
    (hL : HasFiniteConstantLocalModel Λ W L) :
    supportedModelHull Λ V
      ((CondensedRing.moduleObjectDerivedPushforward Λ b).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale
