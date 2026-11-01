/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedMappingAction.Step.DerivedMappingSingleStepConstruction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Algebraic compatibility of the normalized single-step mapping arrow

Source: Stacks Project, Differential Graded Algebra, Example 09L9; Step 5 of
lem-sf-derived-functor-mapping-complex-action.
(blueprint: lem-sf-derived-mapping-single-step-algebra)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.DerivedMappingAction

variable {B : Type b} [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
  {A A' : Type u} [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A] [Category.{v} A'] [Abelian A'] [Linear B A']
  [HasDerivedCategory.{w} A']
  {e : Step (B := B) A A'} {S : HomModel (B := B) A} {T : HomModel (B := B) A'}

/-- The normalized natural arrow preserves the unit on every derived object.
Source: Stacks 070I and 09L9
(blueprint: lem-sf-derived-mapping-single-step-algebra).
Proof: represent the object by a K-injective complex. Naturality of the arrow and unit
coherence in both models transport the already proved representative identity. -/
theorem Step.MappingArrow.preservesUnit [Abelian.HasKInjectiveResolutions A]
    (a : e.MappingArrow S T) (hS : S.IsoCoherent) (hT : T.IsoCoherent)
    (P : DerivedCategory A) :
    S.unit P ≫ a.transformation.app (op P, P) = T.unit (e.derived.obj P) := by
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective P
  have : I.IsKInjective := hI
  let q := i.symm
  let v := T.hom.mapIso (Iso.prod (e.derived.mapIso q).symm.op (e.derived.mapIso q))
  have hn := a.transformation.naturality (X := (op (DerivedCategory.Q.obj I),
    DerivedCategory.Q.obj I)) (Y := (op P, P)) (q.inv.op, q.hom)
  change S.hom.map (q.inv.op, q.hom) ≫ a.transformation.app (op P, P) =
    a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj I) ≫
      v.hom at hn
  calc
    _ = S.unit (DerivedCategory.Q.obj I) ≫ S.hom.map (q.inv.op, q.hom) ≫
        a.transformation.app (op P, P) := by rw [← Category.assoc, hS.unit q]
    _ = S.unit (DerivedCategory.Q.obj I) ≫
        a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj I) ≫
          v.hom := by rw [hn]
    _ = T.unit (e.derived.obj (DerivedCategory.Q.obj I)) ≫
        v.hom := by
          rw [← Category.assoc, a.unit_resolved hT I]
    _ = _ := hT.unit (e.derived.mapIso q)

/-- Isomorphism coherence extends the representative composition equation to all objects.
Source: Stacks 070I and 09L9
(blueprint: lem-sf-derived-mapping-single-step-algebra).
Proof: choose K-injective representatives of the three objects and cancel the tensor
of their Hom comparison isomorphisms. Naturality transports each action arrow; the
composition coherence equations in the two models identify both sides with the
representative equation. -/
theorem Step.MappingArrow.preservesComposition [Abelian.HasKInjectiveResolutions A]
    (a : e.MappingArrow S T) (hS : S.IsoCoherent) (hT : T.IsoCoherent)
    (P Q R : DerivedCategory A) :
    S.comp P Q R ≫ a.transformation.app (op P, R) =
      (a.transformation.app (op Q, R) ⊗ₘ a.transformation.app (op P, Q)) ≫
        T.comp (e.derived.obj P) (e.derived.obj Q) (e.derived.obj R) := by
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective P
  obtain ⟨J, hJ, ⟨j⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Q
  obtain ⟨K, hK, ⟨k⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective R
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  have : K.IsKInjective := hK
  let f := S.hom.mapIso (Iso.prod j.op k.symm)
  let g := S.hom.mapIso (Iso.prod i.op j.symm)
  let z := S.hom.mapIso (Iso.prod i.op k.symm)
  let f' := T.hom.mapIso (Iso.prod (e.derived.mapIso j).op (e.derived.mapIso k).symm)
  let g' := T.hom.mapIso (Iso.prod (e.derived.mapIso i).op (e.derived.mapIso j).symm)
  let z' := T.hom.mapIso (Iso.prod (e.derived.mapIso i).op (e.derived.mapIso k).symm)
  have hs := hS.comp i.symm j.symm k.symm
  change (f.hom ⊗ₘ g.hom) ≫ S.comp P Q R =
    S.comp (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj K) ≫
      z.hom at hs
  have ht := hT.comp (e.derived.mapIso i).symm (e.derived.mapIso j).symm
    (e.derived.mapIso k).symm
  change (f'.hom ⊗ₘ g'.hom) ≫ T.comp _ _ _ =
    T.comp (e.derived.obj (DerivedCategory.Q.obj I))
      (e.derived.obj (DerivedCategory.Q.obj J)) (e.derived.obj (DerivedCategory.Q.obj K)) ≫
        z'.hom at ht
  have hf := a.transformation.naturality
    (X := (op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj K))
    (Y := (op Q, R)) (j.hom.op, k.inv)
  change f.hom ≫ a.transformation.app (op Q, R) =
    a.transformation.app (op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj K) ≫
      f'.hom at hf
  have hg := a.transformation.naturality
    (X := (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J))
    (Y := (op P, Q)) (i.hom.op, j.inv)
  change g.hom ≫ a.transformation.app (op P, Q) =
    a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) ≫
      g'.hom at hg
  have hz := a.transformation.naturality
    (X := (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj K))
    (Y := (op P, R)) (i.hom.op, k.inv)
  change z.hom ≫ a.transformation.app (op P, R) =
    a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj K) ≫
      z'.hom at hz
  apply (cancel_epi (f.hom ⊗ₘ g.hom)).mp
  calc
    _ = S.comp (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj K) ≫ z.hom ≫ a.transformation.app (op P, R) := by
      rw [← Category.assoc, hs, Category.assoc]
    _ = S.comp (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj K) ≫
          a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj K) ≫
            z'.hom := by rw [hz]
    _ = (a.transformation.app (op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj K) ⊗ₘ
        a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J)) ≫
          T.comp (e.derived.obj (DerivedCategory.Q.obj I))
            (e.derived.obj (DerivedCategory.Q.obj J))
            (e.derived.obj (DerivedCategory.Q.obj K)) ≫ z'.hom := by
      rw [← Category.assoc, a.composition_resolved hT I J K, Category.assoc]
    _ = (a.transformation.app (op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj K) ⊗ₘ
        a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J)) ≫
          (f'.hom ⊗ₘ g'.hom) ≫
            T.comp (e.derived.obj P) (e.derived.obj Q) (e.derived.obj R) := by rw [ht]
    _ = ((f.hom ≫ a.transformation.app (op Q, R)) ⊗ₘ
        (g.hom ≫ a.transformation.app (op P, Q))) ≫
          T.comp (e.derived.obj P) (e.derived.obj Q) (e.derived.obj R) := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, ← hf, ← hg]
    _ = _ := by rw [← tensorHom_comp_tensorHom, Category.assoc]

/-- The full target-shift square is determined on K-injective representative pairs.
Source: Stacks 070I and 070Y
(blueprint: lem-sf-derived-mapping-single-step-algebra).
Proof: precompose with the invertible map from shifted representative Hom. Naturality
of the arrow and RF's shift comparison moves this precomposition across the left side.
Shift coherence in T reduces to the representative square; shift coherence in S and
naturality of the arrow then give the right side. -/
theorem Step.MappingArrow.target_shift_of_resolved [Abelian.HasKInjectiveResolutions A]
    (a : e.MappingArrow S T) (hS : S.IsoCoherent) (hT : T.IsoCoherent)
    (hr : ∀ (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] (n : ℤ),
      a.transformation.app (op (DerivedCategory.Q.obj I), (DerivedCategory.Q.obj J)⟦n⟧) ≫
        T.hom.map (X := (op (e.derived.obj (DerivedCategory.Q.obj I)),
          e.derived.obj ((DerivedCategory.Q.obj J)⟦n⟧)))
          (Y := (op (e.derived.obj (DerivedCategory.Q.obj I)),
            (e.derived.obj (DerivedCategory.Q.obj J))⟦n⟧))
          (𝟙 _, (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj J)) ≫
        (T.shift (e.derived.obj (DerivedCategory.Q.obj I))
          (e.derived.obj (DerivedCategory.Q.obj J)) n).hom =
      (S.shift (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) n).hom ≫
        (a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J))⟦n⟧')
    (P Q : DerivedCategory A) (n : ℤ) :
    a.transformation.app (op P, Q⟦n⟧) ≫
      T.hom.map (X := (op (e.derived.obj P), e.derived.obj (Q⟦n⟧)))
        (Y := (op (e.derived.obj P), (e.derived.obj Q)⟦n⟧))
        (𝟙 _, (e.derived.commShiftIso n).hom.app Q) ≫
      (T.shift (e.derived.obj P) (e.derived.obj Q) n).hom =
    (S.shift P Q n).hom ≫ (a.transformation.app (op P, Q))⟦n⟧' := by
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective P
  obtain ⟨J, hJ, ⟨j⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Q
  have : I.IsKInjective := hI
  have : J.IsKInjective := hJ
  let q := i.symm
  let r := j.symm
  let u := S.hom.mapIso (Iso.prod q.symm.op r)
  let un := S.hom.mapIso (Iso.prod q.symm.op ((shiftFunctor _ n).mapIso r))
  let v := T.hom.mapIso (Iso.prod (e.derived.mapIso q).symm.op (e.derived.mapIso r))
  let vn := T.hom.mapIso (Iso.prod (e.derived.mapIso q).symm.op
    ((shiftFunctor _ n).mapIso (e.derived.mapIso r)))
  let w := T.hom.mapIso (Iso.prod (e.derived.mapIso q).symm.op
    (e.derived.mapIso ((shiftFunctor _ n).mapIso r)))
  let t : T.hom.obj (op (e.derived.obj P), e.derived.obj (Q⟦n⟧)) ⟶
      T.hom.obj (op (e.derived.obj P), (e.derived.obj Q)⟦n⟧) :=
    T.hom.map (𝟙 _, (e.derived.commShiftIso n).hom.app Q)
  let t₀ : T.hom.obj (op (e.derived.obj (DerivedCategory.Q.obj I)),
      e.derived.obj ((DerivedCategory.Q.obj J)⟦n⟧)) ⟶
      T.hom.obj (op (e.derived.obj (DerivedCategory.Q.obj I)),
        (e.derived.obj (DerivedCategory.Q.obj J))⟦n⟧) :=
    T.hom.map (𝟙 _, (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj J))
  have hn := a.transformation.naturality (X := (op (DerivedCategory.Q.obj I),
    DerivedCategory.Q.obj J)) (Y := (op P, Q)) (q.inv.op, r.hom)
  change u.hom ≫ a.transformation.app (op P, Q) =
    a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J) ≫ v.hom at hn
  have hnn := a.transformation.naturality
    (X := (op (DerivedCategory.Q.obj I), (DerivedCategory.Q.obj J)⟦n⟧))
    (Y := (op P, Q⟦n⟧)) (q.inv.op, (shiftFunctor _ n).map r.hom)
  change un.hom ≫ a.transformation.app (op P, Q⟦n⟧) =
    a.transformation.app (op (DerivedCategory.Q.obj I),
      (DerivedCategory.Q.obj J)⟦n⟧) ≫ w.hom at hnn
  have ht : w.hom ≫ t = t₀ ≫ vn.hom := by
    dsimp only [w, t, t₀, vn, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.op_hom]
    rw [← T.hom.map_comp, ← T.hom.map_comp]
    apply congrArg T.hom.map
    ext
    · simp
    · change e.derived.map ((shiftFunctor _ n).map r.hom) ≫
        (e.derived.commShiftIso n).hom.app Q =
        (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj J) ≫
          (shiftFunctor _ n).map (e.derived.map r.hom)
      exact (e.derived.commShiftIso n).hom.naturality r.hom
  have hs := hS.shift q r n
  change un.hom ≫ (S.shift P Q n).hom =
    (S.shift (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) n).hom ≫ u.hom⟦n⟧' at hs
  have hts := hT.shift (e.derived.mapIso q) (e.derived.mapIso r) n
  change vn.hom ≫ (T.shift (e.derived.obj P) (e.derived.obj Q) n).hom =
    (T.shift (e.derived.obj (DerivedCategory.Q.obj I))
      (e.derived.obj (DerivedCategory.Q.obj J)) n).hom ≫ v.hom⟦n⟧' at hts
  apply (cancel_epi un.hom).mp
  change un.hom ≫ (a.transformation.app (op P, Q⟦n⟧) ≫ t ≫ _) = _
  calc
    _ = a.transformation.app (op (DerivedCategory.Q.obj I),
        (DerivedCategory.Q.obj J)⟦n⟧) ≫ w.hom ≫ t ≫
          (T.shift (e.derived.obj P) (e.derived.obj Q) n).hom := by
      rw [← Category.assoc, hnn]
      simp only [Category.assoc]
    _ = a.transformation.app (op (DerivedCategory.Q.obj I),
        (DerivedCategory.Q.obj J)⟦n⟧) ≫ t₀ ≫
          (T.shift (e.derived.obj (DerivedCategory.Q.obj I))
            (e.derived.obj (DerivedCategory.Q.obj J)) n).hom ≫ v.hom⟦n⟧' := by
      rw [reassoc_of% ht, hts]
    _ = (S.shift (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) n).hom ≫
        (a.transformation.app (op (DerivedCategory.Q.obj I),
          DerivedCategory.Q.obj J))⟦n⟧' ≫ v.hom⟦n⟧' := by
      simpa only [Category.assoc, t₀] using
        congrArg (fun f ↦ f ≫ v.hom⟦n⟧') (hr I J n)
    _ = (S.shift (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) n).hom ≫
        u.hom⟦n⟧' ≫ (a.transformation.app (op P, Q))⟦n⟧' := by
      rw [← Functor.map_comp, ← hn, Functor.map_comp]
    _ = _ := by rw [← Category.assoc, ← hs, Category.assoc]

end CategoryTheory.DerivedMappingAction
