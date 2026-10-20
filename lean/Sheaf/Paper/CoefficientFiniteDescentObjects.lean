/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel

/-!
# Finite coefficient descent of bounded constructible objects

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-objects.md and its proof
(blueprint: det-lem-coefficient-finite-descent-objects).

The constructibility convention is the finite constant local model convention of
`det-def-sfb-constructible-tor-amplitude`. The scalar extensions are the specified left
derived functors on the unbounded categories of internal modules over pulled-back
condensed rings. Isomorphisms are in these ambient derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_hasConstantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      Mod.IsFree (condensedRingObj Λ (U.X i))
        ((CondensedRing.upperStar Λ (U.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ Y M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

open MonoidalCategory MonObj in
private lemma constantModel_eq_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      IsConstantModelConstructible Λ X M ↔
        IsConstructibleModuleObject (condensedRingObj Λ X) M := by
    rw [show IsConstantModelConstructible Λ X M = IsFiniteConstantStratified Λ X M from
      if_pos ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := hLF _ _ h
      apply free_hasConstantModel Λ _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom Λ (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hmod _


/-- Every bounded constructible algebraic-closure coefficient complex has a finite-field
model, and every such model remains a model after any finite enlargement of the field.
Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit,
sk-lem-coefficient-finite-descent-objects.md, both assertions
(blueprint: det-lem-coefficient-finite-descent-objects).

Proof plan, following the node's five steps:
1. A standing scheme is Noetherian: Spec k is Noetherian and finite type preserves this
(lem-weil-pbc-finite-type-over-noetherian). Its locally closed strata are Noetherian and
qcqs, so the hypotheses of lisse descent and finite constructible generation hold.
2. Models persist by lem-sfb-extend-subfield-constructible and the transitivity comparison
of def-sfb-derived-extend-comp-iso. Scalar extensions are exact by lem-sfb-subfield-flat,
lem-sfb-qlbar-flat and the right exact tensor adjunction sk-def-sfb-change-of-scalars.
The exact-functor identification of sk-def-sfb-derived-categories and
lem-weil-pbc-exact-functor-derived-factorization makes these specified derived functors
termwise, triangulated and compatible with shifts. Thus shifts of models are models by
det-cor-coefficient-heart-ii-triangulated. Finite composita put any two models over a common
field (def-weil-finite-subextension-directed-set). This proves the second assertion.
3. For a triangle A → K → B → A[1], put models of A and B over a common E. Transport the
connecting map to their extensions. By det-lem-coefficient-finite-descent-hom (3), with
r = 1, it is represented over some finite F containing E. Complete that representative to
a triangle B_F → A_F[1] → C_F → B_F[1] using TR1 of def-weil-triangulated-category.
Two inverse rotations give A_F → C_F[-1] → B_F → A_F[1], with the original connecting map
and no sign change. Set K_F = C_F[-1]; triangulated closure puts it in Dbc(X,F). After
scalar extension, rotate to compare connecting maps. TR3 and lem-sf-triangle-morphism-iso
give an isomorphism to the given triangle. Hence K descends. Rotation also gives descent
of cones between descended objects.
4. For a generator a_!L[n] of det-cor-coefficient-heart-ii-generation, its locally closed
stratum is qcqs by step 1. Apply det-lem-coefficient-finite-descent-lisse (1) there to get
L_E. The converse generation assertion puts a_!L_E[n] in Dbc(X,E).
The identification in def-sfb-derived-extend-to-qlbar is the same condensed inclusion on
both schemes. Thus det-prop-scalar-six-pullback (2), including the closed immersion factor,
and shift compatibility identify its extension with a_!L[n].
5. Apply the finite generating sequence of det-cor-coefficient-heart-ii-generation to K.
Induct through it using step 4 for generators, step 3 for cones, step 2 for common fields
and shifts, and composition for isomorphisms. Zero has its zero model over the base field,
also a rank-zero generator. Finitely many choices and composita yield one finite field E;
no infinite enlargement occurs. -/
theorem coefficient_finite_descent_objects
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj) →
      ∀ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ∧
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ≅ K.obj)) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  have hE (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
        boundedConstructible (padicSubfieldRingObj X ℓ E) :=
    constantModel_eq_of_localFree _ (finite_lf ℓ E) X
  have hΩ : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
      boundedConstructible (padicAlgClRingObj X ℓ) :=
    constantModel_eq_of_localFree _ (algcl_lf ℓ) X
  constructor
  · intro K
    let K' : PadicAlgClConstructible X ℓ := ⟨K.obj, (congrFun hΩ K.obj).mp K.property⟩
    obtain ⟨E, L, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ K'
    exact ⟨E, ⟨L.obj, (congrFun (hE E) L.obj).mpr L.property⟩,
      ⟨(boundedConstructible (padicAlgClRingObj X ℓ)).ι.mapIso e⟩⟩
  · intro K E K_E hK F h
    constructor
    · exact (congrFun (hE F) _).mpr
        (boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K_E.obj
          ((congrFun (hE E) K_E.obj).mp K_E.property))
    · obtain ⟨e⟩ := hK
      exact ⟨(derivedExtendScalarsCompIso X ℓ h).app K_E.obj ≪≫ e⟩

end AlgebraicGeometry.ProEtale
