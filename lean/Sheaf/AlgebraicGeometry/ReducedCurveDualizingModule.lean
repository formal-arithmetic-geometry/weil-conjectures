/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.Linear
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Sheaf.AlgebraicGeometry.ProperDualizingClosedStalkNormalized
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Topology.Separation.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Dualizing modules on proper reduced curves

Source: Stacks Project, curves.tex, Tags 0BS2 (lemma-duality-dim-1),
0BS3 (lemma-duality-dim-1-CM), 0BS5 (lemma-euler), and 0E3E
(lemma-vanishing-on-gorenstein).
(blueprint: lem-sfb-reduced-curve-dualizing-module).

The representing pair includes the natural linear duality, rather than just its module.
The cohomology below is the recorded right derived functor of module global sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Module cohomology with scalars restricted along the structure morphism of a k-scheme.
This is the existing module cohomology functor followed by restriction of scalars;
it introduces neither a new cohomology theory nor a choice of scalar action.
Source: Stacks Project, curves.tex, Tag 0BS2(5).
(blueprint: lem-sfb-reduced-curve-dualizing-module). -/
abbrev Scheme.Modules.moduleCohomologyOverField (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] (p : ℕ) : C.Modules ⥤ ModuleCat.{u} k :=
  RingedSpace.moduleCohomology C.toRingedSpace p ⋙
    ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := C))

/-- The representing pair in coherent Serre duality in dimension one. Naturality is
contravariant in coherent test modules and uses the actual induced cohomology map.
Source: Stacks Project, curves.tex, Tag 0BS2(5) and its uniqueness footnote.
(blueprint: lem-sfb-reduced-curve-dualizing-module). -/
structure ReducedCurveDualizingPair (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] where
  omega : C.Modules
  coherent : RingedSpace.IsCoherent C.toRingedSpace omega
  duality : ∀ (F : C.Modules), RingedSpace.IsCoherent C.toRingedSpace F →
    (F ⟶ omega) ≃ₗ[k] Module.Dual k ((Scheme.Modules.moduleCohomologyOverField k C 1).obj F)
  naturality : ∀ (F G : C.Modules)
    (hF : RingedSpace.IsCoherent C.toRingedSpace F)
    (hG : RingedSpace.IsCoherent C.toRingedSpace G) (a : F ⟶ G) (b : G ⟶ omega),
    duality F hF (a ≫ b) =
      (duality G hG b).comp ((Scheme.Modules.moduleCohomologyOverField k C 1).map a).hom

/-- A proper nonempty reduced curve of pure dimension one has a coherent dualizing module.
The representing pair is unique compatibly with its duality. Its component-generic
stalks are one dimensional over the local fields; it has no coherent submodule vanishing
there, and component-generic stalks detect maps into it. Its Euler characteristic is
minus that of the structure module.

Source: Stacks Project, curves.tex, Tags 0BS2(2),(5), 0BS3(1),(2),(4), 0BS5,
and the finite-support argument of 0E3E.
(blueprint: lem-sfb-reduced-curve-dualizing-module).

Proof (the node's steps):
1. Properness gives finite type and hence Noetherianity over k. Flatness over a field
   and finite presentation over a Noetherian base allow the proper polynomial-model
   duality theorem. For K = f^! k[0], proper-field algebraic duality gives bounded
   coherent cohomology and dualizing stalk complexes.
2. Reduced local rings satisfy S1 by the reducedness Serre criterion. Their dimensions
   are at most one, so the depth/support-dimension inequality makes them Cohen-Macaulay.
   Closed points have dimension one by purity and the primes/localization correspondence.
3. Closed-stalk normalization and normalized CM concentration place K in degree -1 at
   every closed point. Exact stalks and closed coherent supports, together with sobriety
   and existence of closed points in quasi-compact Kolmogorov spaces, give global
   concentration. The concentrated-single theorem identifies K with omega[1].
4. Fully faithful degree-zero embedding and adjunction identify Hom(F,omega) with
   Hom(RGamma(F)[1],k[0]). Field-complex splitting identifies this naturally and linearly
   with the dual of H^1(C,F).
5. For two representing pairs form the natural bijection T between their Hom functors.
   Set u = T_omega(id) and v = T_omega'^{-1}(id). Naturality gives T_F(h) = h >> u,
   and then vu = id and uv = id; any compatible isomorphism must equal u.
6. Reduced Noetherian total fractions make component-generic local rings fields.
   Stalk duality gives the homothety isomorphism from this field to End(omega_eta).
   Field-complex splitting makes acyclic complexes contractible, so omega_eta[1]
   is K-injective and computes this derived internal Hom. The stalk is nonzero.
   Extend a prescribed value on a nonzero vector to an endomorphism; surjectivity
   of homothety shows every vector is a scalar multiple of it, giving rank one.
7. A coherent submodule with zero generic stalks has closed support of dimension zero.
   The finite-support finite-scheme theorem and affine vanishing give H^1(C,N)=0.
   Duality makes Hom(N,omega)=0, so its monic inclusion is zero and N is zero.
8. Images are coherent by coherent kernels/cokernels on a locally Noetherian scheme.
   Exactness of stalks identifies generic image stalks with the images of stalk maps.
   Apply step 7 to get the morphism criterion; its converse recovers step 7.
9. Shifted adjunction, the structure-sheaf Hom/hypercohomology identification and
   field splitting give H^j(omega) dual to H^{1-j}(O_C). Higher groups vanish.
   Proper coherent cohomology is finite, and dual dimensions agree, so the Euler
   characteristics are opposite, using all of H^0(O_C) without identifying it with k. -/
theorem exists_reducedCurveDualizingPair (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsReduced C] [Nonempty C]
    (hPure : C.IsPureDimension 1) :
    ∃ D : ReducedCurveDualizingPair k C,
      (∀ D' : ReducedCurveDualizingPair k C,
        ∃! e : D.omega ≅ D'.omega,
          ∀ (F : C.Modules) (hF : RingedSpace.IsCoherent C.toRingedSpace F)
            (a : F ⟶ D.omega), D'.duality F hF (a ≫ e.hom) = D.duality F hF a) ∧
      (∀ (Z : Set C), Z ∈ irreducibleComponents C → ∀ η : C, IsGenericPoint η Z →
        IsField (C.presheaf.stalk η) ∧
          Nonempty (((RingedSpace.moduleStalkFunctor C.toRingedSpace η).obj D.omega) ≃ₗ[
            C.presheaf.stalk η] C.presheaf.stalk η)) ∧
      (∀ (N : C.Modules), RingedSpace.IsCoherent C.toRingedSpace N →
        ∀ i : N ⟶ D.omega, Mono i →
          (∀ (Z : Set C), Z ∈ irreducibleComponents C →
            ∀ η : C, IsGenericPoint η Z →
              Subsingleton ((RingedSpace.moduleStalkFunctor C.toRingedSpace η).obj N)) →
          IsZero N) ∧
      (∀ (F : C.Modules), RingedSpace.IsCoherent C.toRingedSpace F →
        ∀ a : F ⟶ D.omega,
          (a = 0 ↔ ∀ (Z : Set C), Z ∈ irreducibleComponents C →
            ∀ η : C, IsGenericPoint η Z →
              (RingedSpace.moduleStalkFunctor C.toRingedSpace η).map a = 0)) ∧
      D.omega.eulerChar k =
        -Scheme.Modules.eulerChar k (SheafOfModules.unit C.ringCatSheaf) := by
  sorry

end AlgebraicGeometry
