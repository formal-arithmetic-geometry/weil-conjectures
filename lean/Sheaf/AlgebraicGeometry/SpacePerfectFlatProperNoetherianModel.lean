/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceForgetAmbientBase
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceFinitePresentationModuleLimit
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType

/-! # Etale local Noetherian models of perfect and flat proper-support data

Source: Stacks Project, spaces-perfect.tex, Tag 0A1P,
lemma-base-change-tensor-perfect, Noetherian approximation before K_i;
spaces-limits.tex, Tags 07SK, 07V7, 08K0, 08K2; spaces-perfect.tex, Tag 09RJ;
spaces-cohomology.tex, Tag 07UB
(blueprint: lem-sfb-space-perfect-flat-proper-model).

The cartesian square specifies the isomorphism of the restricted space with the
model's scalar extension. The perfect-object comparison lives in the derived
category. The coefficient comparison is an isomorphism of ordinary complexes.
The absolute module equivalence permits the model to have no S-structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Etale locally on Y, the perfect object and the bounded finitely presented
relatively flat proper-support complex descend together to a Noetherian model.
The model and the cartesian square are over Spec Z, not over the original S.

Source: Stacks Project, spaces-perfect.tex, Tag 0A1P, the approximation paragraph
before K_i; spaces-limits.tex, Tags 07SK, 07V7, 08K0, 08K2;
spaces-perfect.tex, Tag 09RJ; spaces-cohomology.tex, Tag 07UB
(blueprint: lem-sfb-space-perfect-flat-proper-model).

Proof:
1. Choose an affine etale scheme atlas of Y by lem-a1-space-affine-etale-cover.
   Base change gives the finitely presented map X_a to U_a, and v_a is etale.
   The enlarged-site localization in lem-trf-space-enlarged-etale-ringed-site-model
   identifies restriction with exact etale module restriction; the corresponding
   geometric local rings and stalks agree. Hence finite presentations, relative
   flatness and local bounded finite-free-retract models restrict. For proper
   support use lem-sfb-space-module-proper-carrier-support: pull a proper carrier
   back, and tensor its annihilating ideal relations with the restricted module.
   The resulting module is a finite type module on that proper carrier, so the
   reverse carrier implication gives proper annihilator support. This does not
   assert that annihilators commute with arbitrary base change.
2. Fix U_a = Spec R. Use lemma-nagata-noetherian-inverse-system-affine to write it
   as the limit of spectra of finitely generated integer subrings R_i of R.
   The index set is small, nonempty and directed: it is a subset of the power
   set of R, contains the image of Z, and adjoining two finite generating sets
   gives an upper bound. Z is Noetherian by the least-positive-element argument
   for its nonzero ideals and the empty generating set for the zero ideal.
   Thus lem-weil-pbc-finite-type-algebra-noetherian makes every R_i Noetherian.
3. Descend X_a to a finitely presented X_i by lem-sfb-fp-space-limit-category.
   Its later base changes are finitely presented by
   lem-sfb-space-flat-proper-fp-locality, and qcqs by lem-sfb-space-fp-qcqs-source.
   The base-change clause of lem-sfb-space-affine-limits-schematic-stages gives
   X_a = lim X_i. Transitions are affine by the affine-spectrum tensor formula
   lem-weil-pbc-fibre-product-affine-spectra, tested on affine scheme charts.
4. Choose a finite degree interval containing the nonzero terms of G.
   Descend its finitely many terms by lem-sfb-space-fp-module-limit-category,
   its differentials by that node's morphism clause, and the equations d d = 0
   by its equality clause, each time taking a common upper bound. Put zero
   terms and zero boundary differentials outside the interval. This gives an
   isomorphism of complexes after ordinary termwise tensor pullback. Local
   finite presentations imply quasi-coherence by def-trf-space-quasi-coherent-module.
   Every further stage preserves the chain isomorphism and its equations.
5. Descend the restricted perfect E by lem-sfb-space-perfect-limit-category.
   Move the coefficient complex to this stage. Apply
   lem-sfb-space-module-eventually-flat to its finitely many terms and then
   lem-sfb-space-module-eventually-proper-support to each term, moving to common
   upper bounds. Flatness persists at later stages by the flatness node.
   Proper support persists by the carrier equivalence, proper base change in
   lem-sfb-space-flat-proper-fp-locality, and the quotient-module construction
   of step 1. Module continuity preserves finite presentation; perfect
   continuity preserves perfectness. The resulting stage has all required
   properties and both specified comparisons simultaneously.
6. Spec R_i is locally Noetherian by pqf-def-locnoeth. Every etale chart of X_i
   is locally of finite type over it, so pqf-lem-locnoeth-lft makes the chart
   locally Noetherian. By pqf-lem-affine-open-locnoeth its affine open rings
   are Noetherian. The Zariski/etale comparison
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and the finiteness
   comparison lem-sfb-scheme-etale-module-exact-finiteness-comparison retain
   finite presentation. Then lem-weil-pbc-quasi-coherent-finite-type-affine
   identifies the sections on affine opens with finitely presented, hence
   finitely generated ring modules. This is exactly the stated coherence.
   Forget the original ambient base using def-sfb-space-absolute-module-transport;
   no S-structure was descended. -/
theorem exists_etale_noetherian_perfect_flat_proper_model
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ (B : Scheme.{u}) (Z : AlgebraicSpace B), HasDerivedCategory.{w} Z.SmallModules]
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (E : X.DerivedModules)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E)
    (G : CochainComplex X.Modules ℤ)
    (hbounded : ∃ b c : ℤ, ∀ n : ℤ, n < b ∨ c < n → IsZero (G.X n))
    (hG : ∀ n : ℤ, (G.X n).IsQuasicoherent ∧ (G.X n).IsFinitePresentation ∧
      ModuleIsFlatOver f (G.X n) ∧ HasProperAnnihilatorSupport f (G.X n)) :
    ∃ (I : Type u) (R : I → CommRingCat.{u})
      (s : ∀ a : I, Spec (R a) ⟶ S)
      (ua : ∀ a : I, schemeSpace (Over.mk (s a)) ⟶ Y),
      (∀ a : I, IsEtale (ua a).hom.hom) ∧
      IsJointlySurjective (fun a : I ↦ (ua a).hom.hom) ∧
      ∀ a : I, ∃ (Xa : AlgebraicSpace S) (va : Xa ⟶ X)
        (ta : Xa ⟶ schemeSpace (Over.mk (s a))),
        IsPullback va ta f (ua a) ∧
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
          Xa.smallStructureSheaf ((derivedTensorPullback va).obj E) ∧
        (∀ n : ℤ, ModuleIsFlatOver ta ((moduleTensorPullback va).obj (G.X n))) ∧
        ∃ (R0 : CommRingCat.{u}) (_ : IsNoetherianRing R0) (r : R0 ⟶ R a)
          (X0 : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
          (f0 : X0 ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec R0))))
          (E0 : X0.DerivedModules) (G0 : CochainComplex X0.Modules ℤ),
          (MapIsLocallyOfFinitePresentation f0 ∧ MapIsQuasiCompact f0.hom.hom ∧
            MapIsQuasiCompact (pullback.diagonal f0.hom.hom)) ∧
          SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
            X0.smallStructureSheaf E0 ∧
          (∃ b c : ℤ, ∀ n : ℤ, n < b ∨ c < n → IsZero (G0.X n)) ∧
          (∀ n : ℤ, (G0.X n).IsQuasicoherent ∧ (G0.X n).IsFinitePresentation ∧
            ModuleIsFlatOver f0 (G0.X n) ∧ HasProperAnnihilatorSupport f0 (G0.X n)) ∧
          (∀ T : X0.EtaleSite, IsLocallyNoetherian (X0.etaleForget.obj T)) ∧
          (∀ (n : ℤ) (T : X0.EtaleSite), IsAffine (X0.etaleForget.obj T) →
            IsNoetherianRing Γ(X0.etaleForget.obj T, ⊤) ∧
            Module.Finite Γ(X0.etaleForget.obj T, ⊤)
              (((schemeRestriction X0 T).obj (G0.X n)).val.obj (op ⊤))) ∧
          ∃ p : absoluteSpace Xa ⟶ X0,
            IsPullback p (absoluteSchemeTargetMap (Over.mk (s a)) ta) f0
              (ObjectProperty.homMk ⟨yoneda.map
                (Over.homMk (Spec.map r) (specULiftZIsTerminal.hom_ext _ _))⟩) ∧
            Nonempty ((derivedTensorPullback p).obj E0 ≅
              (absoluteDerivedTransport Xa).obj ((derivedTensorPullback va).obj E)) ∧
            Nonempty (((moduleTensorPullback p).mapHomologicalComplex (.up ℤ)).obj G0 ≅
              (((moduleTensorPullback va).mapHomologicalComplex (.up ℤ)) ⋙
                (absoluteModuleEquivalence Xa).inverse.mapHomologicalComplex (.up ℤ)).obj G) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
