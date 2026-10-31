/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces

/-! # Finite scalar counits of exact strict coefficient transports

Source: Zheng, Construction 4.1 and Construction 5.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem transport_evaluated_counit_isIso
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB) (n : ℕ)
    (K : CochainComplex (strictEtaleCoefficientSystem T O ell) ℤ) :
    IsIso ((U.level n).counit.app
      (((coefficientEvaluation (J := T.smallEtaleTopology)
        (O := O) (ell := ell) (index n)).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let t := (U.derivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
    (U.level n).derived.map ((PA.evaluationFactors (index n)).hom.app K)
  have h := U.property.2.2.2 n K
  have ht : IsIso t := by dsimp only [t]; infer_instance
  have hc : IsIso (t ≫ (U.level n).counit.app
      (((coefficientEvaluation (J := T.smallEtaleTopology)
        (O := O) (ell := ell) (index n)).mapHomologicalComplex (.up ℤ)).obj K)) := by
    dsimp only [t]
    rw [Category.assoc, h]
    infer_instance
  exact IsIso.of_isIso_comp_left t _

/-- Every selected finite scalar counit of a strict coefficient transport is invertible.
Source: Zheng, Construction 4.1 and Construction 5.15.
(blueprint: lem-pur-strict-etale-transport-scalar-counit).

Proof: the transport representative equation expresses its scalar counit, on the
complex obtained by evaluating a strict system, as a composite of isomorphisms.
Cancel its two preceding comparison isomorphisms. An arbitrary complex P at level
index(n) is isomorphic to evaluation of the termwise single-level extension of P:
the below comparison at the reflexive index and the tensor identity provide this
isomorphism. Naturality of the scalar counit across it transports invertibility
from that evaluated complex to P. No flatness or boundedness assumption is used. -/
theorem strictEtaleTransport_scalarCounit_isIso
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB) (n : ℕ)
    (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ) :
    IsIso ((U.level n).counit.app P) := by
  let ext := PA.extension (index n)
  let : ext.Additive := PA.extensionAdditive (index n)
  let ev := coefficientEvaluation (J := T.smallEtaleTopology)
    (O := O) (ell := ell) (index n)
  let α : ext ⋙ ev ≅ 𝟭 _ := PA.below (Nat.le_refl (index n)) ≪≫ PA.tensorUnit (index n)
  let e : (ev.mapHomologicalComplex (.up ℤ)).obj
      ((ext.mapHomologicalComplex (.up ℤ)).obj P) ≅ P :=
    ((Functor.mapHomologicalComplexCompIso α (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
  have h := transport_evaluated_counit_isIso U n
    ((ext.mapHomologicalComplex (.up ℤ)).obj P)
  have hn : (DerivedCategory.Q ⋙ (U.level n).derived).map e.hom ≫
      (U.level n).counit.app P =
    (U.level n).counit.app ((ev.mapHomologicalComplex (.up ℤ)).obj
      ((ext.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ((siteCoefficientTensor (a.sheaf T n)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q).map e.hom := (U.level n).counit.naturality e.hom
  have hc : IsIso ((DerivedCategory.Q ⋙ (U.level n).derived).map e.hom ≫
      (U.level n).counit.app P) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ (U.level n).derived).map e.hom) _

end AlgebraicGeometry
