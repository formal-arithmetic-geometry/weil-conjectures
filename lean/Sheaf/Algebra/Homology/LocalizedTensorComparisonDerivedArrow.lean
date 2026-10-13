/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.AffineTensorCohomologyLifts
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence
import Sheaf.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import Sheaf.Algebra.Homology.BaseTensorDerivedChainComparison
import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso

/-! # Derived naturality of localized tensor comparisons

The missing structural step in retract closure is functoriality of the comparison
arrow, rather than invertibility of any comparison. Source: Stacks Project, Tags
06Y6, 0DJ7 and 0DJA(1).
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat
variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized tensor comparisons are values of one functor to the arrow category.

Source: Stacks Project, Tag 06Y6 (derived change of rings), Tag 0BYJ
(associativity), and the comparison in Tag 0DJ7, used in Tag 0DJA(1).

Proof: on D(A), tensor with Q using A-K-flat resolutions. For the source,
restrict this tensor to R, apply derived extension to B, and take degree-i
cohomology. The commuting A and B actions give the canonical A-tensor-R-B
module. Extend this module to C. For the target, apply derived extension
from A to C, tensor over C with N, and take degree-i cohomology. Extension
of an A-K-flat complex is C-K-flat, so the target is computed by the
ordinary total tensor with N, even when N is not K-flat. The coefficient
comparison followed by the map induced by t defines a natural
transformation from source to target: on resolutions it is the ordinary
coefficient map, rebracketing, then identity tensor t. Naturality on chain
maps and homotopies gives naturality on K-flat homotopy categories;
quasi-isomorphisms between K-flat representatives induce isomorphisms on
both sides, so localization descends the transformation to D(A). Regard
it as a functor H to the arrow category. For each K-flat U, its tensor
with Q computes the derived tensor since Q is K-flat. Uniqueness of the
universal derived counit gives the source identification for every model
mU; naturality at A-multiplication makes this identification tensor-
algebra-linear. Its comparison_eq and localized_eq equations identify
the source arrow with mU.localizedComparison. The target identification
comes from the K-flat computation above; naturality of the monoidal
scalar-extension isomorphism identifies the rest of the arrow with the
displayed homology map. These two identifications give an arrow
isomorphism. No comparison is assumed invertible. Flatness of C allows
extension of source cohomology to be computed before taking cohomology.
The construction works for unbounded and zero complexes and zero rings.
(blueprint: lem-pc-localized-tensor-comparison-derived-arrow). -/
theorem exists_localizedTensorComparison_derived_arrow
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) (i : ℤ) :
    ∃ H : DerivedCategory (ModuleCat.{u} A) ⥤ Arrow (ModuleCat.{u} C),
      ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
      ∀ mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C,
      let F := (extendScalars.{u, u, u}
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
          (.up ℤ)
      Nonempty (Arrow.mk (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) ≅
          H.obj (DerivedCategory.Q.obj U)) := by sorry

end ModuleCat
