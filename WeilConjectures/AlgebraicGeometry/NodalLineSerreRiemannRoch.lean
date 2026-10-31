/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Linear
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

import WeilConjectures.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.DegreeWeightedIrreducibleComponents
import WeilConjectures.TraceFormula.ReducedCurveNormalizationGenus
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ProperCurveBundlePullbackDegree
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Serre duality and Riemann--Roch for a projective nodal curve

Source: Stacks Project, curves.tex, Tags 0BS2, 0BS4 and 0BS6;
moduli-curves.tex, Tag 0E6R; varieties.tex, Tags 0AYR, 0AYW and 0AYZ
(blueprint: lem-sfb-nodal-line-serre-riemann-roch).

Cohomology is the recorded right derived functor on O-modules, with scalars
restricted along the structure morphism. Coherent modules are expressed using
IsQuasiCoherentFiniteType: the projective scheme over a field is locally Noetherian,
where this is precisely coherence. Component schemes in the finite enumeration
are reduced closed components; their normalizations and pullbacks are canonical.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Nodal Serre duality, its representing-pair uniqueness, and the numerical
Riemann--Roch and normalized-component degree formulas for every line bundle.

Source: Stacks Project, curves.tex, Tags 0BS2 (5), 0BS4 and 0BS6;
moduli-curves.tex, Tag 0E6R; varieties.tex, Tags 0AYR, 0AYW and 0AYZ
(blueprint: lem-sfb-nodal-line-serre-riemann-roch).

Proof:
1. Projectivity implies properness (lem-kun-projective-implies-proper). Finite type
   over the Noetherian field implies X is Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Finite type is finite presentation
   over a Noetherian ring (lem-weil-pbc-finite-type-noetherian-finite-presentation);
   quasi-separatedness is lem-weil-pbc-locally-noetherian-quasi-separated. Flatness
   is lem-pc-flat-field; these give the hypotheses of relative nodal duality.
2. Over the algebraically closed field the geometric fibre is X itself.
   lem-sfb-gorenstein-curve-relative-dualizing gives an invertible representing
   module. lem-sfb-reduced-curve-dualizing-module gives the natural linear duality;
   uniqueness of representing pairs identifies these modules. Yoneda gives the
   unique isomorphism preserving the duality maps.
3. By lem-pc-tensor-dual-invertible the dual and tensor product of line bundles
   are invertible. On a locally Noetherian scheme these modules are coherent
   (pqf-lem-coherent-ft-locnoeth). Proper cohomology finiteness and dimension
   vanishing (lem-pc-euler-characteristic-well-defined and
   lem-sc-noetherian-cohomology-above-dimension) give finite dimensions and
   chi(L) = h0(L) - h1(L).
4. Locally send w tensor e-dual to the homomorphism a e maps to a w.
   Its inverse sends phi to phi(e) tensor e-dual. Replacing e by v e multiplies
   the two factors by v and its inverse, so the maps glue. Compose the resulting
   H0(omega tensor M-dual) = Hom(M,omega) with duality and take dimensions.
   Taking M = O gives h0(omega) = h1(O).
5. lem-sc-global-functions gives H0(O) = k. Thus chi(O) = 1 - g and the
   definition def-pc-degree-line-bundle gives Riemann--Roch by rearrangement.
6. lem-trf-degree-weighted-irreducible-components gives the degree sum with
   generic lengths. Reducedness makes the generic local rings fields
   (lem-sfb-reduced-curve-dualizing-module), each of length one.
7. lem-trf-reduced-curve-normalization-genus gives smooth proper component
   normalizations. lem-sc-normalization-properties gives finite birational
   normalization. Its function-field extension is the identity by
   def-sc-normalization. Apply lem-sfb-proper-curve-bundle-pullback-degree with
   degree one and use pullback composition
   (lem-weil-pbc-invertible-pullback-tensor) in the component sum.
-/
theorem exists_nodal_line_serre_riemann_roch
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) →
      x ∉ (X ↘ Spec (.of k)).smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}))) :
    ∃ (ω : X.Modules), ω.IsInvertible ∧
      ∃ (e : ∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
        (F ⟶ ω) ≃ₗ[k]
          Module.Dual k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1)),
        (∀ (F G : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
          (hG : G.IsQuasiCoherentFiniteType) (a : F ⟶ G) (φ : G ⟶ ω)
          (x : Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1),
          e F hF (a ≫ φ) x = e G hG φ
            (Scheme.Modules.scalarCohomologyMap (X ↘ Spec (.of k)) a 1 x)) ∧
        (∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
          FiniteDimensional k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1)) ∧
        FiniteDimensional k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) ω 0) ∧
        FiniteDimensional k
          (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) (Scheme.Modules.unit X) 1) ∧
        (Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) ω 0) =
          Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k))
            (Scheme.Modules.unit X) 1)) ∧
        (∀ (M : X.Modules), M.IsInvertible →
          FiniteDimensional k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 0) ∧
          FiniteDimensional k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 1) ∧
          FiniteDimensional k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k))
            (ω ⊗ Scheme.Modules.dual M) 0) ∧
          Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k))
            (ω ⊗ Scheme.Modules.dual M) 0) =
              Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 1) ∧
          (Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 0) : ℤ) -
            Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 1) =
              Scheme.Modules.degree k M + 1 -
                Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k))
                  (Scheme.Modules.unit X) 1) ∧
          Scheme.Modules.degree k M =
            Scheme.Modules.eulerChar k M -
              Scheme.Modules.eulerChar k (Scheme.Modules.unit X) ∧
          ∃ (m : ℕ) (Z : Fin m → Scheme.{u}) (hZ : ∀ i, IsIntegral (Z i))
            (j : ∀ i, Z i ⟶ X),
            (∀ i, IsClosedImmersion (j i)) ∧
            Function.Injective (fun i ↦ Set.range (j i)) ∧
            (∀ C : Set X, C ∈ irreducibleComponents X ↔ ∃ i, Set.range (j i) = C) ∧
            Scheme.Modules.degree k M = ∑ i : Fin m,
              @Scheme.Modules.degree k _ (@Scheme.normalization (Z i) (hZ i))
                ⟨@Scheme.fromNormalization (Z i) (hZ i) ≫ j i ≫ X ↘ Spec (.of k)⟩
                ((Scheme.Modules.tensorPullback
                  (@Scheme.fromNormalization (Z i) (hZ i) ≫ j i)).obj M)) ∧
        (∀ (ω' : X.Modules), ω'.IsQuasiCoherentFiniteType →
          ∀ (e' : ∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
            (F ⟶ ω') ≃ₗ[k]
              Module.Dual k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1)),
            (∀ (F G : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
              (hG : G.IsQuasiCoherentFiniteType) (a : F ⟶ G) (φ : G ⟶ ω')
              (x : Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1),
              e' F hF (a ≫ φ) x = e' G hG φ
                (Scheme.Modules.scalarCohomologyMap (X ↘ Spec (.of k)) a 1 x)) →
            ∃! i : ω ≅ ω', ∀ (F : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
              (φ : F ⟶ ω) (x : Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1),
              e' F hF (φ ≫ i.hom) x = e F hF φ x) := by
  sorry

end AlgebraicGeometry
