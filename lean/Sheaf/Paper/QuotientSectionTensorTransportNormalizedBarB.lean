/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData

/-! # Underlying quotient section tensor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

private theorem tensor_iso_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ D) (e' : C' ≌ D')
    (B : C × C ⥤ C) (B' : C' × C' ⥤ C')
    (S : D × D ⥤ D) (S' : D' × D' ⥤ D')
    (F : C ⥤ C') (G : D ⥤ D')
    (d : F ⋙ e'.functor ≅ e.functor ⋙ G)
    (b : B ⋙ F ≅ (F.prod F) ⋙ B')
    (t : B ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ S)
    (t' : B' ⋙ e'.functor ≅ (e'.functor.prod e'.functor) ⋙ S') :
    Nonempty (S ⋙ G ≅ (G.prod G) ⋙ S') := by
  let E := e.prod e
  have h : E.functor ⋙ (S ⋙ G) ≅ E.functor ⋙ ((G.prod G) ⋙ S') :=
    calc
      E.functor ⋙ (S ⋙ G) ≅ (E.functor ⋙ S) ⋙ G :=
        (Functor.associator _ _ _).symm
      _ ≅ (B ⋙ e.functor) ⋙ G := Functor.isoWhiskerRight t.symm G
      _ ≅ B ⋙ (e.functor ⋙ G) := Functor.associator _ _ _
      _ ≅ B ⋙ (F ⋙ e'.functor) := Functor.isoWhiskerLeft B d.symm
      _ ≅ (B ⋙ F) ⋙ e'.functor := (Functor.associator _ _ _).symm
      _ ≅ ((F.prod F) ⋙ B') ⋙ e'.functor := Functor.isoWhiskerRight b e'.functor
      _ ≅ (F.prod F) ⋙ (B' ⋙ e'.functor) := Functor.associator _ _ _
      _ ≅ (F.prod F) ⋙ ((e'.functor.prod e'.functor) ⋙ S') :=
        Functor.isoWhiskerLeft (F.prod F) t'
      _ ≅ ((F ⋙ e'.functor).prod (F ⋙ e'.functor)) ⋙ S' :=
        (Functor.associator _ _ _).symm
      _ ≅ ((e.functor ⋙ G).prod (e.functor ⋙ G)) ⋙ S' :=
        Functor.isoWhiskerRight (NatIso.prod d d) S'
      _ ≅ E.functor ⋙ ((G.prod G) ⋙ S') :=
        Functor.associator E.functor (G.prod G) S'
  exact ⟨((Functor.whiskeringLeft _ _ _).obj E.functor).preimageIso h⟩

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

set_option linter.unusedVariables false in
/-- The balanced section tensor comparison exists before its normalization equations.
Source: Stacks 03EK, 03EL, 06YS, 07A4 and 0G7D; parent proof steps 1--5.
(blueprint: lem-sfb-quotient-section-tensor-transport-normalized-barB).

Proof: construct the sectionwise balancing map on flat-term K-flat representatives,
then descend it through the section localization and the resolving-class equivalence.
The signed total and the tensor counits give a natural derived isomorphism. -/
theorem section_tensor_transport_normalized_barB_exists (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b) :
    Nonempty (tensor Λ T ⋙ c.model.T ≅
        (c.model.T.prod c.model.T) ⋙ tensor Λ' T) := by
  -- Existence uses only the comparison isomorphisms; normalization is needed later.
  exact tensor_iso_transport (derivedEquivalence Λ T) (derivedEquivalence Λ' T)
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ' T))
    (tensor Λ T) (tensor Λ' T) (D a T) c.model.T c.derived b
    (tensorComparison Λ T) (tensorComparison Λ' T)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
