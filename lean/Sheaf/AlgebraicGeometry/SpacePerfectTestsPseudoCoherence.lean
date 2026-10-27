/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Perfect tensor tests detect pseudo-coherence on flat algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tags 0GFJ
(lemma-characterize-pseudo-coh-improved) and 0DII
(lemma-relative-pseudo-coherent-is-moot).
(blueprint: lem-sfb-space-perfect-tests-pseudocoherence).

The tensor and scalar global sections are the existing K-flat and K-injective
constructions on the equivalent small affine etale ringed model.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Perfect tensor tests with pseudo-coherent A-valued derived sections detect
pseudo-coherence on a separated, flat, finitely presented algebraic space over A.
Source: Stacks Project, Tags 0GFJ and 0DII
(blueprint: lem-sfb-space-perfect-tests-pseudocoherence).

Proof:
1. Spec A is quasi-compact and quasi-separated by lem-weil-pbc-affine-scheme-qcqs.
   Finite presentation includes quasi-compactness and quasi-separatedness of f, so
   lem-sfb-space-fp-qcqs-source makes X quasi-compact and quasi-separated.
2. Each perfect tensor test has a bounded-above finite-free A-model by
   def-pc-ring-pseudo-coherent-complex. Its cohomology vanishes above the last
   nonzero term. Apply lem-sfb-space-perfect-tensor-tests-upper-bound to obtain
   an upper cohomological bound for K; the test bounds need not be uniform.
3. Apply lem-sfb-space-perfect-to-pseudocoherent-tests using this bound and the
   given perfect tests. The derived sections of E tensor K are then pseudo-coherent
   over A for every pseudo-coherent E.
4. Separatedness and finite presentation allow
   lem-sfb-space-pseudocoherent-tests-relative to conclude that K is pseudo-coherent
   relative to Spec A (Tag 0GFJ, via Tag 0CTT).
5. Apply lem-sfb-space-flat-relative-pseudocoherence, with base and target Spec A.
   Flatness and local finite presentation identify this relative pseudo-coherence
   with absolute pseudo-coherence (Tag 0DII). This is the existing etale-local
   bounded-above finite-free model condition, with locally varying bounds. -/
theorem isPseudoCoherent_of_perfect_tensor_tests
    (A : Type u) [CommRing A] (X : AlgebraicSpace (Spec (.of A)))
    [HasDerivedCategory.{w} X.SmallModules]
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A)))))
    (_hsep : MapIsSeparated f) (_hflat : MapIsFlat f)
    (_hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (K : X.DerivedModules) (_hK : X.derivedQCohProperty K)
    (_htest : ∀ E : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf E →
      DerivedCategory.IsPseudoCoherent
        ((affineDerivedSections A (Over.mk (𝟙 (Spec (.of A)))) (Iso.refl _) X f).obj
          (X.derivedDualityModel.closed.tensor.obj (E, K)))) :
    X.IsPseudoCoherent K := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
