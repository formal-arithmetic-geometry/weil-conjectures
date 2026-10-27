/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProperUpperShriekComposition
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.FiniteDualityDerivedHom

/-! # Normalized dualizing stalks at closed points of a proper scheme

Source: Stacks Project, duality.tex, Tag 0AWL (lemma-good-dualizing-normalized),
specialized to Spec(k), and Tag 0AWI (example-proper-over-local).
(blueprint: lem-sfb-proper-dualizing-closed-stalk-normalized).

The direct image to D(k) uses the canonical affine global-sections identification.
Stalks apply the existing stalk functor termwise to a localization representative.
The homothety is the transpose of the identity under the derived tensor-Hom adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wX wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The derived direct image to D(k), including its canonical affine coefficient transport.
Global sections on Spec(k) are restricted to k using the inverse of Gamma-Spec.
Source: Stacks Project, Tags 0AWL and 06Z0
(blueprint: lem-sfb-proper-dualizing-closed-stalk-normalized). -/
def properFieldDerivedDirectImage (k : Type u) [Field k] (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace))]
    (f : X ⟶ Spec (.of k)) :
    schemeDerivedQCohCategory X ⥤ DerivedCategory (ModuleCat.{u} k) :=
  (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f ⋙
    (RingedSpace.globalSectionsFunctor (Spec (.of k)).toRingedSpace ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctor

/-- The stalk of a derived complex, computed by applying the exact module stalk functor
termwise to its localization representative. Other representatives give isomorphic objects.
This uses the supplied localization of sheaves, without replacing it by the standard one.
Source: Stacks Project, Tags 0AWL and 01AG
(blueprint: lem-sfb-proper-dualizing-closed-stalk-normalized). -/
def properDualizingStalk (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (x : X) (K : schemeDerivedCategory X) :
    DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) :=
  DerivedCategory.Q.obj
    (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage K))

/-- The stalk of a proper adjoint dualizing complex is algebraic dualizing and normalized
at every closed point. The homothety is `curry' (𝟙 K_x)`, whose source is the derived
monoidal unit A[0]. The residue field has its canonical A-action via the residue map.
Source: Stacks Project, duality.tex, Tag 0AWL (lemma-good-dualizing-normalized),
with Tag 0AWI (example-proper-over-local).
(blueprint: lem-sfb-proper-dualizing-closed-stalk-normalized).

Proof:
1. Properness implies finite type. A field is Noetherian, and finite type over a
   Noetherian base makes X Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   Apply lem-sfb-proper-field-algebraic-dualizing to the given right adjoint to obtain
   finite injective dimension at each stalk and the homothety isomorphism.
   Its bounded coherent cohomology gives finite stalk cohomology: stalks are exact
   (lem-weil-pbc-module-stalk-exact), and a local finite generating surjection for a
   coherent sheaf (pqf-def-coherent) remains surjective on stalks.
2. For a closed x, put L = kappa(x). The extension L/k is finite by
   lem-kun-closed-point-field(a). Its inclusion i : Spec(L) to X is a closed immersion
   (lem-trf-closed-point-residue-immersion), hence finite and proper
   (lem-weil-pbc-closed-immersion-finite, lem-weil-pbc-closed-immersion-proper).
   The composite pi = f i is finite and flat (lem-pc-flat-field); the required right
   adjoints exist by lem-pc-noetherian-derived-direct-image-right-adjoint.
3. Finite flat duality (lem-sc-finite-flat-duality-evaluation) identifies pi! k[0]
   with Hom_k(L,k)[0], with L acting by (b lambda)(c) = lambda(bc). Use the affine
   equivalence of lem-pc-affine-qcoh-derived-equivalence to read this in D(L).
4. Proper composition (lem-sc-proper-upper-shriek-composition) gives
   i! a(k[0]) isomorphic to pi! k[0].
5. The sheaf F = i_* O is coherent (lem-weil-pbc-finite-pushforward-coherent).
   Finite duality (lem-sc-finite-duality-derived-hom), followed by the derived stalk
   comparison (lem-sfb-coherent-bounded-below-rhom-stalk), identifies RHom_A(L,K_x)
   with Hom_k(L,k)[0] in D(A). The closed skyscraper pushforward is exact and its
   stalk at x is its original L-module with scalars restricted to A; hence F_x = L.
6. Choose a nonzero k-linear functional lambda on L. The map
   b maps to (c maps to lambda(bc)) is L-linear and injective: for b nonzero choose
   d with lambda(d) nonzero and evaluate at b inverse times d. The two vector
   spaces have equal finite k-dimension, so this is an isomorphism. Restriction
   of scalars to A and the degree-zero embedding give the asserted normalization.
   No separability, rationality, smoothness, dimension or reducedness is used. -/
theorem proper_dualizing_closed_stalk_normalized
    (k : Type u) [Field k] (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace))]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (a : DerivedCategory (ModuleCat.{u} k) ⥤ schemeDerivedQCohCategory X)
    (_adj : properFieldDerivedDirectImage k X f ⊣ a)
    (x : X) (_hx : IsClosed ({x} : Set X)) :
    IsNoetherianRing (X.presheaf.stalk x) ∧
    (∃ I : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ,
      (∃ p q : ℤ, ∀ n : ℤ, n < p ∨ q < n → IsZero (I.X n)) ∧
      (∀ n : ℤ, Injective (I.X n)) ∧
      Nonempty (DerivedCategory.Q.obj I ≅ properDualizingStalk X x
        (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
          (ModuleCat.of k k))).obj)) ∧
    (∀ j : ℤ, Module.Finite (X.presheaf.stalk x)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) j).obj
        (properDualizingStalk X x
          (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k))).obj))) ∧
    IsIso (MonoidalClosed.curry' (𝟙 (properDualizingStalk X x
      (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        (ModuleCat.of k k))).obj))) ∧
    Nonempty ((ordinaryModuleDerivedInternalHom (X.presheaf.stalk x)).obj
      (op ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((ModuleCat.restrictScalars (X.residue x).hom).obj
          (ModuleCat.of (X.residueField x) (X.residueField x)))),
       properDualizingStalk X x
        (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
          (ModuleCat.of k k))).obj) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((ModuleCat.restrictScalars (X.residue x).hom).obj
          (ModuleCat.of (X.residueField x) (X.residueField x)))) := by
  sorry

end AlgebraicGeometry
