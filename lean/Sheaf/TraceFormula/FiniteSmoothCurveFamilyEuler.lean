/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Euler characteristic of finite images of smooth proper curves

Source: Stacks Project, coherent.tex, Tag 089W (lemma-relative-affine-cohomology);
varieties.tex, Tag 08AA (lemma-euler-characteristic-additive); curves.tex, Tag 0BY7
(definition-genus) (blueprint: lem-trf-finite-smooth-curve-family-euler).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of a direct-image structure module to one coproduct summand.
The first map is restriction of functions, followed by the canonical composition and
coproduct-descent identifications. Source: the sheaf axiom on a disjoint union, as used
with Stacks Tag 089W (blueprint: lem-trf-finite-smooth-curve-family-euler). -/
def finiteCurveFamilyRestrictionComponent {I : Type v} [Fintype I]
    (C : I → Scheme.{u}) {X : Scheme.{u}} (h : ∀ i, C i ⟶ X) (i : I) :
    (pushforward (Sigma.desc h)).obj (unit (∐ C)) ⟶ (pushforward (h i)).obj (unit (C i)) :=
  (pushforward (Sigma.desc h)).map
      (SheafOfModules.unitToPushforwardObjUnit (Sigma.ι C i).toRingCatSheafHom) ≫
    (pushforwardComp (Sigma.ι C i) (Sigma.desc h)).hom.app (unit (C i)) ≫
    (pushforwardCongr (Sigma.ι_desc h i)).hom.app (unit (C i))

/-- The canonical restriction map from functions on the coproduct to the product of
functions on its summands, pushed forward to `X`.
Source: the sheaf axiom on a disjoint union, as used with Stacks Tag 089W
(blueprint: lem-trf-finite-smooth-curve-family-euler). -/
def finiteCurveFamilyRestriction {I : Type v} [Fintype I]
    (C : I → Scheme.{u}) {X : Scheme.{u}} (h : ∀ i, C i ⟶ X) :
    (pushforward (Sigma.desc h)).obj (unit (∐ C)) ⟶
      ∏ᶜ (fun i ↦ (pushforward (h i)).obj (unit (C i))) :=
  Pi.lift (finiteCurveFamilyRestrictionComponent C h)

/-- Finite images of a finite family of smooth proper connected curves have coherent
structure direct images; restriction gives their product/direct-sum decomposition.
The actual identity-h-map edge maps are k-linear isomorphisms in every degree, the
structure map identifies degree-zero curve cohomology with k, higher curve cohomology
vanishes above one, and the Euler characteristics are one minus genus and their sum.
The zero-degree structure map is specified through the canonical map from sections to
right-derived degree zero. All cohomology objects in these clauses use module resolutions.

Source: Stacks Project, coherent.tex, Tag 089W; varieties.tex, Tag 08AA;
curves.tex, Tag 0BY7 (blueprint: lem-trf-finite-smooth-curve-family-euler).

Proof:
1. The identity trivialization makes each structure module invertible
   (def-sc-invertible-module). Apply lem-trf-proper-field-invertible-coherent to obtain
   Noetherianity and coherence. Finite pushforward preserves coherence by
   lem-weil-pbc-finite-pushforward-coherent, and pqf-lem-coherent-ft-locnoeth supplies
   quasi-coherence of the curve structure modules.
2. On each open of X, the inverse images in the summands form a disjoint open cover.
   The sheaf axiom identifies sections with their product by restriction and gluing.
   These identifications respect restrictions and the O_X-action. A finite product is
   also the direct sum. Iterating lem-weil-pbc-coherent-kernel-cokernel-locnoeth gives
   coherence of the sum; the empty sum is the coherent zero module.
3. A finite map is affine. Apply lem-weil-pbc-affine-morphism-cohomology-edge to the
   structure module. Its edge map is moduleCohomologyEdgeMap, induced by the identity.
   Restrict scalars along k to global functions; the k-morphism equation identifies
   the scalar actions and gives the claimed k-linear isomorphism.
4. Apply lem-sc-global-functions to each smooth proper connected curve. Its structure
   map is the degree-zero isomorphism. The dimension is one by def-sc-curves, so
   lem-sc-noetherian-cohomology-above-dimension gives vanishing for q greater than one.
5. By lem-pc-euler-characteristic-well-defined the coherent Euler sums are finite.
   The linear edge isomorphisms identify their dimensions. Degree zero has dimension
   one, degree one has dimension genus (def-sc-genus), and all remaining terms vanish.
   Thus both Euler characteristics are 1 minus genus (def-pc-euler-characteristic).
6. Apply lem-pc-euler-additive to the split short exact sequences adjoining one
   summand. Induction gives the cardinality minus the sum of the genera. For the empty
   family the sheaf axiom on the empty cover gives the zero module, with zero cohomology
   and Euler characteristic, supplying the induction base.
-/
theorem finite_smooth_curve_family_euler
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (I : Type v) [Fintype I] (C : I → Scheme.{u})
    [∀ i, (C i).Over (Spec (.of k))]
    [∀ i, IsConnectedCurve (C i ↘ Spec (.of k))]
    [∀ i, Smooth (C i ↘ Spec (.of k))]
    [∀ i, IsProper (C i ↘ Spec (.of k))]
    (h : ∀ i, C i ⟶ X) [∀ i, IsFinite (h i)] [∀ i, (h i).IsOver (Spec (.of k))] :
    (∀ i, RingedSpace.IsCoherent X.toRingedSpace ((pushforward (h i)).obj (unit (C i)))) ∧
    RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward (Sigma.desc h)).obj (unit (∐ C))) ∧
    IsIso (finiteCurveFamilyRestriction C h) ∧
    Nonempty ((∏ᶜ (fun i ↦ (pushforward (h i)).obj (unit (C i)))) ≅
      ∐ (fun i ↦ (pushforward (h i)).obj (unit (C i)))) ∧
    (∀ (i : I) (q : ℕ),
      ∃ e : (ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
            ((pushforward (h i)).obj (unit (C i)))) ≅
        (ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := C i))).obj
          ((RingedSpace.moduleCohomology (C i).toRingedSpace q).obj (unit (C i))),
        (forget₂ (ModuleCat k) AddCommGrpCat).map e.hom =
          moduleCohomologyEdgeMap (h i) (unit (C i)) q) ∧
    (∀ i : I,
      (∃ e : k ≃ₗ[k]
          (ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := C i))).obj
            ((RingedSpace.moduleCohomology (C i).toRingedSpace 0).obj (unit (C i))),
        ∀ a : k, e a =
          ((RingedSpace.globalSectionsFunctor (C i).toRingedSpace).toRightDerivedZero.app
            (unit (C i))) (Scheme.globalSectionsRingHom k (X := C i) a)) ∧
      (∀ q : ℕ, 1 < q →
        Subsingleton ((RingedSpace.moduleCohomology (C i).toRingedSpace q).obj
          (unit (C i)))) ∧
      (C i ↘ Spec (.of k)).genus =
        Module.finrank k
          ((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := C i))).obj
            ((RingedSpace.moduleCohomology (C i).toRingedSpace 1).obj (unit (C i)))) ∧
      eulerChar k ((pushforward (h i)).obj (unit (C i))) = eulerChar k (unit (C i)) ∧
      eulerChar k (unit (C i)) = 1 - ((C i ↘ Spec (.of k)).genus : ℤ)) ∧
    eulerChar k ((pushforward (Sigma.desc h)).obj (unit (∐ C))) =
      (Fintype.card I : ℤ) - ∑ i : I, ((C i ↘ Spec (.of k)).genus : ℤ) ∧
    (IsEmpty I →
      IsZero ((pushforward (Sigma.desc h)).obj (unit (∐ C))) ∧
      eulerChar k ((pushforward (Sigma.desc h)).obj (unit (∐ C))) = 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
