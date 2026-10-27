/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.OpenCohomologyZeroSections
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentZeroDimensionalSupport
import Sheaf.AlgebraicGeometry.CoherentFiniteSupportSkyscrapers

/-! # The quotient of a finite curve modification

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant),
normalization exact-sequence argument generalized to finite surjective modifications;
Tag 0AYT (lemma-chi-tensor-finite), parts (2)--(4)
(blueprint: lem-trf-finite-curve-quotient-stalk-euler).

The helpers expose the actual categorical cokernel and its sections and stalks with
scalars restricted along the structure map from the base field. No choices of maps
or of scalar structures enter these definitions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The sheaf cokernel of the canonical structure map `O_X → f_* O_Y`.
Source: Stacks Project, Varieties, Tag 0C1R, normalization exact sequence
(blueprint: lem-trf-finite-curve-quotient-stalk-euler). -/
noncomputable abbrev finiteCurveQuotient {X Y : Scheme.{u}} (f : Y ⟶ X) : X.Modules :=
  cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- The global sections of the modification quotient, regarded as a vector space over
its base field by the structure morphism.
Source: Stacks Project, Varieties, Tag 0AYT (2)--(4)
(blueprint: lem-trf-finite-curve-quotient-stalk-euler). -/
noncomputable def finiteCurveQuotientSections (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] (f : Y ⟶ X) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (globalSectionsRingHom k (X := X))).obj
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (finiteCurveQuotient f))

/-- The stalk of the modification quotient, with the base-field action induced by
`k → O_X(X) → O_{X,x}`. Its underlying abelian group is the usual filtered colimit stalk.
Source: Stacks Project, Varieties, Tags 0C1R and 0AYT
(blueprint: lem-trf-finite-curve-quotient-stalk-euler). -/
noncomputable def finiteCurveQuotientStalk (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] (f : Y ⟶ X) (x : X) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((X.presheaf.germ ⊤ x (Set.mem_univ x)).hom.comp
      (globalSectionsRingHom k (X := X)))).obj
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (finiteCurveQuotient f))

/-- The defect of a finite surjective modification of a proper reduced pure curve is
coherent with finite closed support. Its global sections are canonically the direct
sum of its stalks via germs; its positive cohomology vanishes and its Euler
characteristic is the sum of the dimensions of those stalks.

Source: Stacks Project, Varieties, Tag 0C1R, normalization exact-sequence argument
for the stated finite modification, and Tag 0AYT (2)--(4)
(blueprint: lem-trf-finite-curve-quotient-stalk-euler).

Proof:
1. Apply lem-trf-proper-field-invertible-coherent to the trivial invertible module.
   This makes X Noetherian and O_X coherent. The finite map makes f_* O_Y
   quasi-coherent of finite type; pqf-lem-coherent-ft-locnoeth makes it coherent.
   Its cokernel is coherent by lem-weil-pbc-coherent-kernel-cokernel-locnoeth.
2. Finiteness implies affineness and hence quasi-compactness and quasi-separatedness
   (lem-weil-pbc-affine-morphism-permanence). Surjectivity gives dense image.
   Reducedness and lemma-nagata-reduced-dense-image-schematic give schematic density;
   def-nagata-scheme-theoretic-image identifies the kernel with zero.
3. The abelian cokernel sequence is therefore short exact
   (def-weil-pbc-exact-sequence). Over N its first arrow is an isomorphism, so the
   quotient is zero there and its support lies in X minus N.
4. Every point of X minus N is closed: a proper specialization would give a chain
   of length two inside a one-dimensional component. Sobriety
   (lem-sc-scheme-sober) gives strictness of the closures. The Noetherian component
   theorem (lem-sc-noetherian-closed-subset-finite-components) decomposes the closed
   boundary into finitely many components, each a singleton. Thus the support is finite.
5. Apply lem-trf-coherent-finite-support-skyscrapers and evaluate on X. The finite
   direct sum of the stalk skyscrapers gives exactly the coordinate germs map;
   the scalar action through structure-sheaf germs makes it k-linear.
6. Apply lem-sfb-coherent-zero-dimensional-support for positive-cohomology vanishing.
   Proper coherent finiteness (lem-pc-coherent-hi) and the degree-zero sections
   comparison (lem-sc-open-cohomology-zero-sections) make the global sections
   finite-dimensional. Every supported stalk is a summand of them, and every
   unsupported stalk is zero.
7. By def-pc-euler-characteristic only degree zero remains. The dimension of a
   finite direct sum is the sum of the dimensions. Extending the sum to all closed
   points adds only zero terms. Empty support gives the zero space and zero sums.
-/
theorem finite_curve_quotient_stalk_euler (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsReduced X] (hdim : X.IsPureDimension 1)
    (f : Y ⟶ X) [f.IsOver (Spec (.of k))] [IsFinite f] [Surjective f]
    (N : X.Opens)
    (hN : ∀ (Z : Set X), Z ∈ irreducibleComponents X →
      ∀ x : X, IsGenericPoint x Z → x ∈ N)
    (hiso : IsIso (morphismRestrict f N)) :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ∧
    RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) ∧
    RingedSpace.IsCoherent X.toRingedSpace (finiteCurveQuotient f) ∧
    (ShortComplex.mk (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
      (cokernel.condition _)).ShortExact ∧
    (∀ x : X, FiniteDimensional k (finiteCurveQuotientStalk k f x)) ∧
    (∀ q : ℕ, 0 < q → IsZero
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (finiteCurveQuotient f))) ∧
    ∃ S : Finset X,
      (∀ x : X, x ∈ S ↔ ¬ Subsingleton ((finiteCurveQuotient f).presheaf.stalk x)) ∧
      (∀ x ∈ S, IsClosed ({x} : Set X)) ∧
      (∃ e : finiteCurveQuotientSections k f ≃ₗ[k]
          ⨁ x : {x : X // x ∈ S}, finiteCurveQuotientStalk k f x.val,
        ∀ (s : finiteCurveQuotientSections k f) (x : {x : X // x ∈ S}),
          e s x = (finiteCurveQuotient f).presheaf.germ ⊤ x.val (Set.mem_univ x.val) s) ∧
      (finiteCurveQuotient f).eulerChar k =
        ∑ x ∈ S, (Module.finrank k (finiteCurveQuotientStalk k f x) : ℤ) ∧
      (finiteCurveQuotient f).eulerChar k =
        ∑ᶠ x : {x : X // IsClosed ({x} : Set X)},
          (Module.finrank k (finiteCurveQuotientStalk k f x.val) : ℤ) ∧
      (Set.Finite {x : {x : X // IsClosed ({x} : Set X)} |
        (Module.finrank k (finiteCurveQuotientStalk k f x.val) : ℤ) ≠ 0}) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
