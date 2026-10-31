/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Closed subspaces and quasi-coherent ideals

Source: Stacks Project, Morphisms of Spaces, Tag 03MB and the paragraph following
`definition-inverse-image-closed-subspace`
(blueprint: lem-sfb-space-ideal-closed-subspace-correspondence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed subspaces correspond contravariantly to quasi-coherent ideals, with their
kernel, vanishing, quotient and base-change characterizations. The image after arbitrary
base change is specified by an epimorphism onto its ideal subobject. For etale base change
the ideal inclusion itself is the restriction, as expressed on every chart section.
Source: Stacks Project, Morphisms of Spaces, Tag 03MB and the paragraph following
`definition-inverse-image-closed-subspace`
(blueprint: lem-sfb-space-ideal-closed-subspace-correspondence).

Proof:
1. For schemes, construct the closed subscheme from its quasi-coherent ideal using
lem-weil-pbc-quasi-coherent-ideal-closed-subscheme. The tensor adjunction of
 def-pc-module-pullback rewrites vanishing as the hypothesis of
lem-weil-pbc-closed-immersion-lift-ideal-kills-sections, giving the unique lift.
The quotient ring maps prove the converse. Transport this through
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.
2. Factor a module map through its image. Tensor pullback preserves its epimorphic
factor by lem-weil-pbc-left-adjoint-preserves-colimits. Vanishing after further pullback
therefore depends only on the image. The composition comparison is
lem-trf-space-chart-adjunction-tensor-realization, with b tensor (a tensor m) sent to ba
 tensor m; it does not assert preservation of monomorphisms under arbitrary pullback.
3. Define V(I) on scheme tests by the vanishing of the pulled-back ideal map. For a scheme
U over X, the image ideal on U is quasi-coherent by
lem-sfb-space-module-pullback-quasicoherent and lem-sfb-space-qcoh-kernels-colimits.
Steps 1 and 2 identify the base change of V(I) with its scheme closed subscheme.
4. Apply lem-sfb-presheaf-space-target-bootstrap and def-trf-scheme-algebraic-space:
V(I) is an algebraic space and its inclusion is representable by closed immersions.
5. For a closed subspace, lem-trf-space-etale-module-pushforward-restriction identifies
the structural direct image and structure map on an etale scheme chart. Scheme closed
immersions have a surjective structure map with quasi-coherent kernel. Use
lem-weil-pbc-closed-immersion-integral-separated-uc for the separated quasi-compact
comparison and the Zariski-etale equivalence. Kernels and cokernels are computed in all
modules by lem-sfb-space-qcoh-kernels-colimits,
lem-weil-pbc-quasi-coherent-module-kernel and
lem-weil-pbc-quasi-coherent-module-cokernel-image. Thus the assertion descends to X.
6. On etale charts tensor pullback is restriction, so the ideal in step 3 is I restricted.
Step 5 then identifies the kernel ideal of V(I) with I and proves surjectivity.
7. For an algebraic-space source, choose an etale scheme atlas. By
lem-trf-space-chart-adjunction-tensor-realization and
lem-trf-space-etale-module-pushforward-restriction, vanishing can be checked on these
charts. The unique scheme lifts of step 3 agree on overlaps, which are schemes by
lem-trf-space-representable-etale-scheme-tests. Glue in the fppf sheaf V(I).
The converse follows on charts; zero maps are detected on a covering.
8. Recover every closed subspace from its kernel by
lem-weil-pbc-closed-immersions-equal-ideal-isomorphic on etale charts, gluing the unique
lifts using lem-trf-space-fibre-products-etale-covers. Inclusion of ideals reverses
vanishing loci; the converse uses lem-weil-pbc-closed-immersion-factor-ideal-inclusion
on charts. Thus the two operations are inverse and reverse order in both directions.
9. For h:Y to X take the image J of h^* I to O_Y. It is quasi-coherent by the two
quasi-coherent module lemmas of step 3. Step 2 identifies V(J) on every scheme test with
the sheaf fibre product Y times_X V(I). Step 6 identifies its ideal with J. If h is
etale, pullback is restriction, so the inclusion stays monic and its image is precisely
the restricted ideal, with the same inclusion on every chart.
10. Under def-trf-space-etale-module-functors the map h^* I to O_Y is adjoint to
I to O_X to h_* O_Y, by the local tensor formula of
lem-trf-space-chart-adjunction-tensor-realization. The hom-set bijection takes zero to
zero, giving the equivalent direct-image criterion. -/
theorem ideal_closedSubspace_correspondence (S : Scheme.{u}) :
    ∃ corr : ∀ X : AlgebraicSpace S, ClosedSubspace X ≃ QuasiCoherentIdeal X,
      (∀ (X : AlgebraicSpace S) (C : ClosedSubspace X),
        (corr X C).val = kernelSubobject (moduleStructureMap C.val.arrow) ∧
          Epi (moduleStructureMap C.val.arrow)) ∧
      (∀ (X : AlgebraicSpace S) (C D : ClosedSubspace X),
        C ≤ D ↔ corr X D ≤ corr X C) ∧
      (∀ (X : AlgebraicSpace S) (I : QuasiCoherentIdeal X)
          (Y : AlgebraicSpace S) (h : Y ⟶ X),
        ((∃ l : Y ⟶ ((corr X).symm I).val,
            l ≫ ((corr X).symm I).val.arrow = h) ↔ idealTensorMap h I = 0) ∧
          (idealTensorMap h I = 0 ↔ I.val.arrow ≫ moduleStructureMap h = 0)) ∧
      (∀ (X Y : AlgebraicSpace S) (I : QuasiCoherentIdeal X) (h : Y ⟶ X),
        ∃ (P : ClosedSubspace Y)
            (a : (P.val : AlgebraicSpace S) ⟶ (((corr X).symm I).val : AlgebraicSpace S)),
          IsPullback a P.val.arrow ((corr X).symm I).val.arrow h ∧
          (∃ q : (moduleTensorPullback h).obj (I.val : X.Modules) ⟶
              ((corr Y P).val : Y.Modules),
            Epi q ∧ q ≫ (corr Y P).val.arrow = idealTensorMap h I) ∧
          ∀ hh : IsEtale h.hom.hom,
            ∃ r : ((corr Y P).val : Y.Modules) ≅
                (pullback h hh).obj (I.val : X.Modules),
              ∀ (V : Y.EtaleSite) (m : ((corr Y P).val : Y.Modules).val.obj (op V)),
                (corr Y P).val.arrow.val.app (op V) m =
                  I.val.arrow.val.app (op ((etaleMap h hh).obj V))
                    (r.hom.val.app (op V) m)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
