/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.NormalScheme
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataRing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# Generic finite normal trivialization of a constructible etale module sheaf

Source: ILO, Expose XVII, proof of Lemma 3.5.7, printed p.276; Stacks Project,
Tags 0DV5(3) and 0AVK (blueprint: lem-per-generic-finite-normal-trivialization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible sheaf over a finite commutative ring on a Noetherian excellent
integral scheme becomes a finite constant module sheaf on a nonempty open after a
finite surjective cover by an integral normal scheme. The cover is etale over that open.
No hypothesis of finite type over a field is used.

Source: ILO, Expose XVII, proof of Lemma 3.5.7, printed p.276; Stacks Project,
Tags 0DV5(3) and 0AVK (blueprint: lem-per-generic-finite-normal-trivialization).

Proof:
1. Take the constructible stratum containing the generic point. Its locally closed
   image is open, since any closed subset containing the generic point is the whole
   integral scheme. Immersion independence identifies its pullback with restriction,
   so the sheaf is finite locally constant on a nonempty open
   (def-weil-pbc-etale-constructible-sheaf, lemma-constructible-immersion-independence).
2. Choose a nonempty affine open there. Excellence makes its regular locus open,
   containing the generic point, whose local ring is a field. Shrink to a nonempty
   principal open U in that locus. It is regular, hence normal, integral and connected
   (def-exc-excellent-ring, lem-sc-integral-function-field-affine-fraction,
   lem-weil-pbc-field-regular-ring, rem-pc-regular-normal).
3. The finite-set monodromy torsor gives a connected finite etale surjection P to U.
   Module-constant-of-set-pullback makes the pullback constant with value N. A geometric
   stalk identifies N with a finite stalk of the original sheaf, hence N is finite
   (lem-weil-pbc-finite-set-monodromy-torsor, lem-weil-pbc-module-constant-of-set-pullback,
   lem-weil-pbc-constant-sheaf-geometric-stalk, lem-weil-pbc-inverse-image-stalk-germ,
   lem-weil-pbc-etale-module-pullback-forget-naturality,
   lem-weil-pbc-finite-locally-constant-module-values).
4. The finite cover P of the affine Noetherian U is affine Noetherian. Its normal
   integral clopen components reduce to one by connectedness and nonemptiness.
   Its function field L is finite separable over k(X), by the generic etale residue
   field calculation (lem-weil-pbc-finite-algebra-noetherian,
   lem-fin-etale-normal-components, lem-weil-pbc-etale-algebra-residue-field-separable).
5. Normalize X in L. The normalization Y is integral normal. Excellent rings are
   Nagata and their domain coordinate rings are Japanese, so the integral closures
   in L are finite. Hence Y to X is finite. Its image is closed and contains the
   generic point, so it is surjective (lem-weil-pbc-normalization-in-residue-field-extension,
   def-fin-normalization-extension, lem-exc-quasi-excellent-nagata,
   def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain, lem-weil-pbc-finite-proper).
6. Write P = Spec B over U = Spec R. Finiteness makes B integral over R. Conversely
   an element of L integral over R is integral over every local ring of P, hence
   lies in all those normal local rings. Function-field sections glue, so it lies
   in B. Thus B is exactly the integral closure and the normalization over U is P
   (lem-weil-pbc-finite-algebra-is-integral,
   lem-sc-integral-scheme-stalks-in-function-field, lem-sc-function-field-sections-glue).
7. Ordinary inverse-image composition identifies the restricted pullback on Y with
   the constant module sheaf on P from step 3. Naturality with respect to every scalar
   endomorphism makes this identification A-linear
   (lem-weil-pbc-inverse-image-composition,
   lem-weil-pbc-etale-module-pullback-forget-naturality). -/
theorem exists_generic_finite_normal_trivialization
    (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]
    (hExcellent : ∀ V : X.affineOpens, IsExcellent Γ(X, V))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (U : X.Opens) (N : ModuleCat.{u + 1} A),
      IsFinite f ∧ Surjective f ∧ Nonempty U ∧ Finite N ∧ IsIntegral Y ∧
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) ∧
      Nonempty
        ((Etale.upperStar (ModuleCat.{u + 1} A) (f ⁻¹ᵁ U).ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} A) f).obj F) ≅
          (constantSheaf (f ⁻¹ᵁ U).toScheme.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj N) := by
  sorry

end AlgebraicGeometry.Scheme
