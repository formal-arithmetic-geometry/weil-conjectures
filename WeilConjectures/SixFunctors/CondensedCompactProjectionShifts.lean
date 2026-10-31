/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
import WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
import WeilConjectures.AlgebraicGeometry.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
import WeilConjectures.CategoryTheory.FormalExactProjectionMate
import WeilConjectures.AlgebraicGeometry.RingedProjectionFirstShift
import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.AdjunctionSquareShiftMate
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-!
# Native condensed compact-support projection and shifts

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
fix-lem-tensor-adjunction.proof.md, Step 1 and the final shift assertion
(blueprint: lem-sf-condensed-compact-projection-shifts).

The projection is the published counit-defined proper projection followed by the inverse
open projection comparison and the pullback compositor. Tensor and shift structures are
those of the ordinary relative K-flat derived category, including the signed second slot.
The four coefficient cases are specified up to isomorphism of condensed rings. Finite
extensions are represented by finite intermediate fields in the fixed standard closure;
this does not impose a choice of model on the input condensed ring.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxHeartbeats 1000000 in
-- Native derived-functor instance expressions are large.
set_option maxHeartbeats 1000000 in
-- Allow elaboration of the two explicit geometric shift squares.
/-- The actual compactification-defined projection commutes separately with every integer
shift of either finite-Tor input, using the native signed tensor comparisons and the
unit/counit-compatible derived-adjoint comparisons. The two equalities are the squares
`τ_[r] ≫ s_G = s_F ≫ τ[r]`, in Lean's left-to-right composition convention.

Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1 (inverse projection)
and final shift assertion (blueprint: lem-sf-condensed-compact-projection-shifts).

Proof plan:
1. Use lem-pe-internal-section-tensor-comparison and
lem-sfb-internal-module-operations-transport, followed by
lem-pd-section-derived-pushpull-normalization and
lem-pd-section-derived-tensor-normalization, to compute in the section-ring sheaves.
These exact equivalences identify the actual units, counits, tensorators and compositors
for arbitrary schemes and condensed rings, and reflect equality of arrows.
2. On total-complex summands the first tensor shift is reindexing and the second is
multiplication by (-1)^(r*a) in first degree a. Uniqueness in
lem-weil-pbc-derived-tensor-shift-descent and
lem-weil-pbc-pullback-tensor-canonical-shift-unit identifies the native derived comparisons.
Use lem-sfb-kflat-derived-adjunction-transport-shifts for units and counits and
lem-sfb-module-derived-functor-compositor-shifts for pullback compositors and inverses.
3. For c = (j,p), the proper component at M = Dj_! K is the adjunct of the actual
oplax tensor comparison followed by counit tensor identity. Its second shift square is
lem-weil-pbc-formal-exact-projection-mate; its first is
lem-sfb-ringed-projection-first-shift. Iterate the [1] square for positive integers,
use the identity for zero, and cancel invertible comparisons to obtain negative shifts.
4. By lem-sf-open-tensor-normalization, the inverse open comparison q is the adjunction
mate of the inverse pullback tensor comparison after the open unit tensor identity.
The exact termwise open adjunction has shift-compatible unit and counit; descend using
lem-pur-site-restriction-module-adjunction-exact,
lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-localization-universal-property, with the pullback comparison from step 2.
5. For fixed second input use lem-weil-pbc-adjunction-square-shift-mate to obtain q's
first square. For fixed first input expand q as open counit after extension of its
adjunct. Tensoring its fixed unit commutes with the signed second shift by step 2;
compose and whisker using lem-weil-pbc-commshift-nattrans-comp-whisker.
6. Cancel q and its shifted inverse to obtain both squares for gamma = q inverse.
Precompose the second input by Lp^*, insert Lj^* Lp^* = Lf^*, and use step 2 for
that compositor and its inverse.
7. The map in the statement is exactly Rp_*(gamma) after the proper projection,
as specified in def-fix-six-functor-datum. Paste the two squares, cancelling the
intermediate comparison, separately in K and L. Restrict the resulting ambient equality
to ConstantModelConstructibleFiniteTor. This applies to each of the four ordinary
condensed coefficient stages, without a completed tensor or a detection argument. -/
theorem condensedCompactProjection_shifts
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ :
      (∃ (E : PadicAlgCl.FiniteIntermediateField C.l)
        (π : PadicAlgCl.integers C.l E) (m : ℕ),
        Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers C.l E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
          (completedResidue C.l E π m)))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField C.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj C.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField C.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj C.l)))
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left)
    (K : ConstantModelConstructibleFiniteTor Λ X.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.left) (r : ℤ) :
    (exceptionalProjectionMorphismOfCompactification Λ c (K.obj⟦r⟧) L.obj ≫
        (((curriedTensor _).flip.obj ((L((f.left)^*⟦Λ⟧)).obj L.obj) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app K.obj =
      ((Rf_!(c)⟦Λ⟧ ⋙ (curriedTensor _).flip.obj L.obj).commShiftIso r).hom.app K.obj ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj L.obj)) ∧
    (exceptionalProjectionMorphismOfCompactification Λ c K.obj (L.obj⟦r⟧) ≫
        (((L((f.left)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K.obj) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app L.obj =
      (((curriedTensor _).obj ((Rf_!(c)⟦Λ⟧).obj K.obj)).commShiftIso r).hom.app L.obj ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj L.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
