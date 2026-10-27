/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel
import Sheaf.AlgebraicGeometry.ProperDualizingClosedStalkNormalized
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import Sheaf.RingTheory.AssociatedLocalizationFg
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Sheaf.Algebra.Homology.NormalizedDualizingDepthDetection
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftComparison
import Sheaf.Paper.RHomCohomologyExtRing
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Topology.Separation.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.RingTheory.Nakayama

/-! # Torsion-free biduality on a reduced curve

Source: Stacks Project, dualizing.tex, Tag 0B5A (lemma-local-CM), final assertion
and proof; curves.tex, Tags 0BS2 and 0BS3, for the dualizing module.
(blueprint: lem-sfb-reduced-curve-torsionfree-biduality).

The evaluation morphism is specified by its values on every open and every smaller
open. Existence and uniqueness are part of the conclusion, as is its invertibility.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Canonical biduality with respect to the dualizing module of a reduced proper curve.
The dual is coherent and its sections are detected at component-generic points.
The uniquely specified evaluation morphism is an isomorphism, including for F = 0.

Source: Stacks Project, dualizing.tex, Tag 0B5A (lemma-local-CM), final assertion
and proof, in the sheaf form using curves.tex, Tags 0BS2 and 0BS3.
(blueprint: lem-sfb-reduced-curve-torsionfree-biduality).

Proof (the node's steps):
1. Properness gives Noetherianity by finite type over a field. Reducedness gives S1
   by the Serre criterion; local dimension is at most one, so the depth/support
   dimension inequality gives Cohen-Macaulay local rings. Purity makes closed
   points have local dimension one, and every nongeneric point is closed.
2. Flatness over a field and finite presentation over the Noetherian base permit
   proper polynomial-model duality. The proper-field algebraic-dualizing theorem
   makes K = f^! k[0] bounded coherent with dualizing stalks. Closed-stalk
   normalization gives the residue-field normalization.
3. Normalized CM concentration puts K in degree -1 at closed points. Stalk
   exactness and closed coherent supports, with sobriety and a closed point in
   every nonempty closed subset of a quasi-compact Kolmogorov space, give global
   concentration K = W[1] by the concentrated-single theorem.
4. Fully faithful single embedding, proper adjunction and field-complex splitting
   give natural linear bijections Hom(G,W) = Hom_k(H^1(G),k). Uniqueness in
   lem-sfb-reduced-curve-dualizing-module identifies W with D.omega, compatibly
   with the representing bijections. Its closed stalks therefore have depth one.
5. Coherent internal Hom is coherent. Local finite presentation identifies Hom
   stalks with ordinary linear Hom, sending a local morphism to its stalk map.
   Coherent affine sections are finite and their stalks are localizations.
6. Generic detection on an affine makes M -> product M_q over minimal primes
   injective. If Ann(z) = p is nonminimal, choose a in p outside each minimal q;
   it kills z and is invertible at q. All generic germs vanish, contradicting
   injectivity. Hence every associated prime of M is minimal.
7. At a closed point with nonzero stalk, associated-prime localization excludes
   the maximal ideal as an associated prime. The nonzerodivisor theorem supplies
   a regular element in that ideal. Nakayama makes its quotient nonzero, so depth
   is at least one; the support-dimension bound makes it exactly one.
8. For an affine section of omega with a nonminimal prime annihilator, its nonzero
   localization has maximal annihilator, contradicting the depth-one result.
   Injectivity into associated-prime localizations gives generic detection for
   omega. Affine subopens and sheaf separation give this on every open.
9. A local section phi of Hom(F,omega) with zero generic germs evaluates on every
   smaller open to an omega-section with zero generic germs, by the normalized
   Hom-stalk comparison. Step 8 makes all its values zero, so phi is zero.
10. For s on U define evaluation on every V -> U by phi |-> phi(s|_V).
    Linearity and restriction compatibility give the evaluation morphism.
    These values determine it uniquely. The two Hom-stalk comparisons identify
    its stalk with m |-> (phi |-> phi(m)).
11. At a closed point a zero F-stalk is handled directly. Otherwise depth one and
    normalized-dualizing depth detection concentrate RHom(M,K_x) in degree -1.
12. Derived Hom shift comparison, degree-zero Ext and the fully faithful single
    embedding identify its degree -1 cohomology with N = Hom(M,omega_x).
    Concentration gives RHom(M,K_x) = N[1], normalized on this cohomology.
13. Finite-module canonical derived biduality, the simultaneous shift comparison
    and degree-zero Ext make the very evaluation map M -> Hom(N,omega_x)
    invertible. The sign is 1, since the evaluated element has degree zero.
14. Coherent kernel and cokernel have zero closed stalks by stalk exactness.
    Closed supports and the same quasi-compact Kolmogorov closed-point argument
    make them zero. Thus evaluation is an isomorphism. Steps 5 and 9 supply the
    other two conclusions. -/
theorem reducedCurve_torsionfree_biduality (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsReduced C] [Nonempty C]
    (hPure : C.IsPureDimension 1) (D : ReducedCurveDualizingPair k C)
    (F : C.Modules) (hF : RingedSpace.IsCoherent C.toRingedSpace F)
    (hDetect : ∀ (U : C.Opens) (s : F.val.obj (op U)),
      (∀ (Z : Set C), Z ∈ irreducibleComponents C →
        ∀ η : C, IsGenericPoint η Z → ∀ hη : η ∈ U,
          TopCat.Presheaf.germ F.val.presheaf U η hη s = 0) → s = 0) :
    RingedSpace.IsCoherent C.toRingedSpace (SheafOfModules.homObj (R := C.sheaf) F D.omega) ∧
    (∀ (U : C.Opens) (s : (SheafOfModules.homObj (R := C.sheaf) F D.omega).val.obj (op U)),
      (∀ (Z : Set C), Z ∈ irreducibleComponents C →
        ∀ η : C, IsGenericPoint η Z → ∀ hη : η ∈ U,
          TopCat.Presheaf.germ (SheafOfModules.homObj (R := C.sheaf) F D.omega).val.presheaf
            U η hη s = 0) → s = 0) ∧
    ∃ δ : F ⟶ SheafOfModules.homObj (R := C.sheaf)
        (SheafOfModules.homObj (R := C.sheaf) F D.omega) D.omega,
      (∀ (U : C.Opens) (s : F.val.obj (op U)) (V : C.Opens) (i : V ⟶ U)
        (φ : (SheafOfModules.homObj (R := C.sheaf) F D.omega).val.obj (op V)),
        (((δ.val.app (op U)) s).app (op (Over.mk i))) φ =
          (φ.app (op (Over.mk (𝟙 V)))) (F.val.map i.op s)) ∧
      IsIso δ ∧
      ∀ δ' : F ⟶ SheafOfModules.homObj (R := C.sheaf)
          (SheafOfModules.homObj (R := C.sheaf) F D.omega) D.omega,
        (∀ (U : C.Opens) (s : F.val.obj (op U)) (V : C.Opens) (i : V ⟶ U)
          (φ : (SheafOfModules.homObj (R := C.sheaf) F D.omega).val.obj (op V)),
          (((δ'.val.app (op U)) s).app (op (Over.mk i))) φ =
            (φ.app (op (Over.mk (𝟙 V)))) (F.val.map i.op s)) → δ' = δ := by
  sorry

end AlgebraicGeometry
