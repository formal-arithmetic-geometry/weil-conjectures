module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Maps.Basic
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Complement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Compactification.StrictTransform
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! # Finite type of a Noetherian subalgebra detected by universal submersivity

Source: Alper, Adequate moduli spaces, arXiv:1005.2398v3, Theorem 6.2.1,
printed pp.31--32, with S = Spec k, X = Spec E and Y = Spec R
(blueprint: lem-sfb-noetherian-subring-finite-type-submersion).

The base-change map is the spectrum of the canonical inclusion of the right tensor
factor. Its quotient-map property means surjectivity and detection of open subsets.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Subalgebra

/-- A Noetherian subalgebra of a finite type algebra over a field is of finite type
if the induced spectrum map is universally submersive. No module-finiteness is assumed.
Source: Alper, arXiv:1005.2398v3, Theorem 6.2.1, printed pp.31--32
(blueprint: lem-sfb-noetherian-subring-finite-type-submersion).

Proof:
1. First consider any map B → C with B a Noetherian domain and C finite type over k.
The affine base-change tests give universal submersivity on every scheme base change.
The map of spectra is finite type and quasi-separated. Generic flatness and presentation
(lem-sbc-generic-flat-finite-presentation) give a nonempty principal flat open U.
Affines are qcqs (lem-weil-pbc-affine-scheme-qcqs). Admissible flattening
(lem-trf-flattening-by-admissible-blowup) gives a blowup T → Spec B with flat finitely
presented strict transform X' → T.
2. The centre ideal I is nonzero. Choose nonzero generators f_i. By
lem-sfb-integral-blowup-projective-geometry the blowup is integral. Its finite chart cover
(prop-nagata-affine-blowup-chart-cover) has rings B_i = B[I/f_i] in Frac B
(def-nagata-blowup-chart-ring). These are Noetherian by
lem-weil-pbc-finite-type-algebra-noetherian. The blowup is Noetherian, and its inverse
image of U is a nonempty dense open by thm-nagata-global-blowup-complement.
3. The base-changed map to T remains finite type (lem-sfb-finite-type-composition-base-change)
and universally submersive. Put V = Spec B minus V(I). Since I restricts to the unit
ideal on U, U is contained in V. The strict transform (def-nagata-strict-transform) is
the scheme-theoretic closure over V, so its support contains the inverse image of U.
Apply lem-sfb-submersive-dense-open-closed-surjectivity to conclude X' → T is surjective.
4. Over each chart, X' is a closed subscheme (def-weil-closed-immersion) of
Spec (C ⊗[B] B_i). This tensor algebra is generated over C by the finitely many ratios
f_j/f_i. Hence X' is locally of finite type over k. Flat finitely presented surjective
source descent (lem-a1-lft-flat-lfp-source-descent) makes T locally of finite type over k.
The affine criterion (lem-weil-pbc-lft-affine-pairs) makes each B_i finite type over k.
5. Express finite k-algebra generators of each B_i as polynomials in the ratios with
coefficients in B. Let A be generated over k by these finitely many coefficients and
all f_j. For J = (f_j) in A, the chart algebras A[J/f_i] equal B_i: they contain the
chosen k-algebra generators and are contained in B_i.
6. The blowup charts over A and B therefore agree. Their overlap identifications agree
inside Frac B after inverting f_j/f_i, by def-nagata-affine-blowup-chart-map and
lemma-nagata-proj-chart-ring-cocycle. The chart identities glue to an isomorphism
T ≅ Bl_J Spec A over Spec A, using prop-nagata-affine-blowup-chart-cover.
7. A is Noetherian by finite-type permanence. By lem-sfb-projective-affine-base-blowup
(applied to the identity, projective via projective zero-space), T is H-projective over A.
Its structure sheaf is coherent by pqf-lem-coherent-ft-locnoeth. The degree-zero case of
lem-pc-projective-coherent-finiteness makes M = Γ(T, O_T) a finite A-module.
8. The map B → M is injective, since on any chart it is the inclusion into
B_i ⊆ Frac B. The Noetherian submodule lemma (lem-weil-pbc-noetherian-submodule-finite)
makes B finite over A. Algebra generators of A and module generators of B then generate
B as a k-algebra. This proves the domain case without requiring B → C injective.
9. For each prime p of R, apply this domain case to B = R/p and C = E/pE.
The latter is finite type over k and its spectrum map is a base change of the given map,
so universally submersive. Thus R/p is finite type; no injection into E/pE is needed.
10. Take a finite prime filtration of the R-module R
(lem-weil-pbc-noetherian-module-prime-filtration). Lift finite algebra generators of all
its factors R/p_i and let D be their generated k-subalgebra of R. Every factor is cyclic
over D. Lifting a cyclic generator at each filtration step shows R is finite over D.
The algebra generators of D and these module generators generate R over k. The empty
filtration gives R = 0, so nilpotents, all components and the zero ring are included. -/
theorem finiteType_of_isNoetherianRing_of_universallySubmersive
    (k : Type u) [Field k] (E : Type v) [CommRing E] [Algebra k E]
    (hE : (algebraMap k E).FiniteType) (R : Subalgebra k E) [IsNoetherianRing R]
    (hsub : ∀ (L : Type (max u v w)) [CommRing L] [Algebra R L],
      Topology.IsQuotientMap
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : L →ₐ[R] E ⊗[R] L).toRingHom))) :
    (algebraMap k R).FiniteType := by
  sorry

end Subalgebra
