/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sober

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.GroupTheory.CosetCover
import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.ClosedSubcurveDualizingAdjunction
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper

/-! # The generic support dichotomy for nodal-curve duality

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve,
Section 4, Proposition 4.1 proof, printed p.48, first two support cases;
Stacks Project, curves.tex, Tags 0BS2, 0BS3 and 0E33
(blueprint: lem-sfb-nodal-dual-support-dichotomy).

The duality module is supplied with its natural representing isomorphisms, as in
nodal Serre duality. The completed local presentations respect the structural
k-action. The subcurve is described by a reduced closed immersion with image a
nonempty proper union of irreducible components; it need not be connected.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A line bundle with nonzero first cohomology has either a dual map nonzero on
all component-generic stalks, or a proper reduced subcurve carrying the same h1.

Source: Franciosi--Tenni, Section 4, Proposition 4.1 proof, printed p.48;
Stacks Project, curves.tex, Tags 0BS2(5), 0BS3 and 0E33(2)
(blueprint: lem-sfb-nodal-dual-support-dichotomy).

Proof:
1. Projectivity implies properness (lem-kun-projective-implies-proper).
   Proper-field coherence (lem-trf-proper-field-invertible-coherent) and
   Noetherian finite-component finiteness give finitely many components.
   Nodal Serre duality identifies V = Hom(M,omega) with H1(X,M)-dual.
   Thus V has positive finite dimension. The algebraically closed field is
   infinite: the product of T-a over a hypothetical finite field, minus 1,
   would be a positive-degree polynomial without a root.
2. For each component let K_j be the kernel of the generic stalk map on V.
   These are k-subspaces. If all are proper, finite linear avoidance
   (lem-pc-finite-linear-avoidance) gives a map outside their union, case (1).
   Otherwise select precisely the components for which K_j is proper.
3. If none were selected, generic detection for maps into the dualizing module
   (lem-sfb-reduced-curve-dualizing-module) would make V zero. Their reduced
   union Y is therefore nonempty and proper. Nodal subcurve duality makes Y
   projective, reduced, pure of dimension one and nodal, without connectedness.
   Pullback preserves invertibility, and proper-field coherence applies to i*M.
4. Let J be the quasi-coherent defining ideal of Y. The ideal-product and
   coherent-submodule theorems make JM coherent. At a selected generic point
   J is zero, since both reduced schemes agree near that point; at any other
   generic point J is the whole local ring, since that point is outside Y.
5. Every map M to omega vanishes on JM, by generic detection. Closed-subcurve
   dualizing adjunction (lem-sfb-closed-subcurve-dualizing-adjunction) identifies
   i_*omega_Y with the annihilator of J in omega. Thus every map factors
   uniquely through i_*omega_Y. On a frame m, a map m maps to w in this
   annihilator descends by a-bar times i*m maps to aw. Since Jw = 0 this is
   well-defined; uniqueness glues the local formulas. Composition gives the
   inverse k-linear isomorphism Hom_Y(i*M,omega_Y) = V.
6. Reduced-curve duality on Y and proper coherent-cohomology finiteness give
   h1(Y,i*M) = dim Hom_Y(i*M,omega_Y) = dim V = h1(X,M), case (2).
   The finite-dimensional dual has the same dimension by the dual basis.
-/
theorem nodal_dual_support_dichotomy
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, x ∉ (X ↘ Spec (.of k)).smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)
            (X.presheaf.Γgerm x (Scheme.Modules.scalarMap (X ↘ Spec (.of k)) ⊤ a))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C a))
    (M : X.Modules) [M.IsInvertible]
    (hM : Nontrivial (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 1))
    (ω : X.Modules) [ω.IsInvertible]
    (duality : ∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
      (F ⟶ ω) ≃ₗ[k]
        Module.Dual k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1))
    (hduality : ∀ (F G : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
      (hG : G.IsQuasiCoherentFiniteType) (a : F ⟶ G) (φ : G ⟶ ω)
      (x : Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) F 1),
      duality F hF (a ≫ φ) x = duality G hG φ
        (Scheme.Modules.scalarCohomologyMap (X ↘ Spec (.of k)) a 1 x)) :
    (∃ φ : M ⟶ ω, ∀ (C : Set X), C ∈ irreducibleComponents X →
      ∀ η : X, IsGenericPoint η C →
        (RingedSpace.moduleStalkFunctor X.toRingedSpace η).map φ ≠ 0) ∨
    (∃ (Y : Scheme.{u}) (i : Y ⟶ X),
      IsClosedImmersion i ∧ IsReduced Y ∧ Nonempty Y ∧
      Set.range i ≠ Set.univ ∧
      (∃ S : Set (Set X), S ⊆ irreducibleComponents X ∧ Set.range i = ⋃₀ S) ∧
      Module.finrank k (Scheme.Modules.scalarCohomology (X ↘ Spec (.of k)) M 1) =
        Module.finrank k (Scheme.Modules.scalarCohomology (i ≫ X ↘ Spec (.of k))
          ((Scheme.Modules.tensorPullback i).obj M) 1)) := by
  sorry

end AlgebraicGeometry
