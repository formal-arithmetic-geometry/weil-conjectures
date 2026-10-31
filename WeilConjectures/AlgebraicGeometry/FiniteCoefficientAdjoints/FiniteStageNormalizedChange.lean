/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateInvertible
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.NormalizedChangeSiteReflection
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! # Invertible normalized comparison for one coefficient arrow

Source: current blueprint reduction-exceptional, Locality and Charts, and the
ordinary closed-support argument in the parent node, proof steps 5--6.
(blueprint: lem-pur-finite-stage-normalized-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

private theorem origin_ctf
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T w.complex.obj := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property.1
  obtain ⟨a, b, ht⟩ := (ctf A T).prop_of_iso e.symm K.property |>.2
  have hLt : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T L :=
    ⟨a, b, (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b L).mp ht⟩
  have hLplus := hL.1.1
  let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T L hLplus
  let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T w.complex.obj w.complex.property
  let d : L ≅ w.complex.obj :=
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L) ≪≫
      (rnu A T).mapIso (e ≪≫ w.iso.symm) ≪≫
      (asIso ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} A) T).unit.app w.complex.obj)).symm
  exact (Etale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} A) T).prop_of_iso d ⟨hL, hLt⟩

section FormalChange

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  {f : X ⟶ Y} {c : Compactification f} (φ : A →+* B)
  (dA : AdjointDatum A c) (dB : AdjointDatum B c)
  (hX : ∀ K, ctf A X K → ctf B X ((tensor φ X).obj K))
  (hY : ∀ K, ctf A Y K → ctf B Y ((tensor φ Y).obj K))
  (q : (ctf A X).ι ⋙ lower A c ⋙ tensor φ Y ≅
    (ctf A X).ι ⋙ tensor φ X ⋙ lower B c)

end FormalChange

-- Preserve the existing unique-existence binder, which is absent from its True predicate.
set_option linter.unusedVariables false in
end AlgebraicGeometry.FiniteCoefficientAdjoints
