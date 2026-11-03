/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement

/-!
# The specified finite constant-scalar comparison

Source: the finite coefficient interpretation of the etale-origin witness in the
proper-base-change blueprint; Bhatt--Scholze, Lemma 4.2.12.
(blueprint: lem-route-finite-origin-constant-comparison-is-iso).

Ring sheaves are expressed as ring objects of tensor abelian sheaves. All scalar
maps below are constructed from constant functions and sheafification adjunctions.
The auxiliary coefficient sheaf is the published connected-component presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteOriginCoefficients

variable (T : Scheme.{u}) (Λ : Type u) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

private abbrev pointAb :=
  Functor.whiskerRight (pointConstants Λ) (forget₂ RingCat.{u + 1} Ab.{u + 1})

private instance pointAb_locallySurjective :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (pointAb Λ) where
  imageSieve_mem {S} s := by
    let f : C(S, Λ) := s.down
    have hclosed (b : Λ) : IsClosed {x : S | f x = b} :=
      isClosed_singleton.preimage f.continuous
    let (b : Λ) : CompactSpace {x : S // f x = b} :=
      isCompact_iff_compactSpace.mp (hclosed b).isCompact
    let := Fintype.ofFinite Λ
    let e := (Fintype.equivFin Λ).symm
    let U (i : Fin (Fintype.card Λ)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card Λ)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card Λ), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance pointAb_locallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (pointAb Λ) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext a b (congrArg
        (fun t : ULift.{u + 1} C(S.unop, Λ) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private theorem pointComparison_isIso : IsIso (pointComparison Λ) := by
  let J := coherentTopology Profinite.{u}
  have h : J.W (A := Ab.{u + 1}) (pointAb Λ) := J.W_of_isLocallyBijective _
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (pointAb Λ)) := (J.W_iff _).mp h
  unfold pointComparison
  infer_instance

omit [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] in
private theorem constantRingMonObj {C : Type*} [Category C] :
    (Functor.const C).monObjObj (AddCommGrpCat.of (ULift.{u + 1} Λ)) =
      Functor.monObjCompForget₂
        ((Functor.const C).obj (RingCat.of (ULift.{u + 1} Λ))) := by
  apply MonObj.ext
  ext S
  rfl

omit [Finite Λ] in
private theorem constantComparison_isMonHom : IsMonHom (constantComparison T Λ) := by
  let J := coherentTopology Profinite.{u}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} Λ))
  have hψ : IsMonHom (pointComparison Λ) := by unfold pointComparison; infer_instance
  have hm : (constantSheaf J Ab.{u + 1}).monObjObj
      (AddCommGrpCat.of (ULift.{u + 1} Λ)) =
      Sheaf.monObj_presheafToSheaf_obj J (P ⋙ forget₂ RingCat Ab) := by
    have h := Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
      (presheafToSheaf J Ab.{u + 1}) (AddCommGrpCat.of (ULift.{u + 1} Λ))
    refine h.trans ?_
    exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf J Ab.{u + 1}) _ _ m) (constantRingMonObj Λ)
  have hψ' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of (ULift.{u + 1} Λ))) _ (pointComparison Λ) :=
    IsMonHom.of_eq _ hm.symm rfl (hf := hψ)
  let := hψ'
  have hi := Functor.isMonHom_compAlgHom
    (constantSheaf J Ab.{u + 1}) (upperStarFromPoint T) (constantSchemeIso T).inv
    (AddCommGrpCat.of (ULift.{u + 1} Λ))
  let mP := (upperStarFromPoint T).monObjObj
    ((constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} Λ)))
  let mQ := (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} Λ))
  have hh := monHomInvExplicit mP mQ
    ((constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} Λ))).symm hi
  have hmap : @IsMonHom _ _ _ _ _ mP _ ((upperStarFromPoint T).map (pointComparison Λ)) :=
    inferInstance
  have hcomp := monHomCompExplicit mQ mP _ _ _ hh hmap
  exact IsMonHom.of_eq _ (by
    have h := Functor.monObjObj_comp (Functor.const T.ProEtᵒᵖ)
      (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (AddCommGrpCat.of (ULift.{u + 1} Λ))
    exact h.trans (congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _ m)
      (constantRingMonObj Λ))) rfl (hf := hcomp)

private theorem functionComparison_isMonHom : IsMonHom (functionComparison T Λ) := by
  unfold functionComparison
  rw [Adjunction.homEquiv_counit]
  change IsMonHom
    ((presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
      (Functor.whiskerRight (finiteCoefficientScalarMap T (ULift.{u + 1} Λ))
        (forget₂ RingCat Ab)) ≫
      (Sheaf.sheafifyRingPresheafIso (Scheme.ProEt.topology T)
        (finiteCoefficientRingSheaf T (ULift.{u + 1} Λ))).hom)
  infer_instance

private theorem functionComparison_isIso : IsIso (functionComparison T Λ) := by
  let J := Scheme.ProEt.topology T
  let φ := Functor.whiskerRight (finiteCoefficientScalarMap T (ULift.{u + 1} Λ))
    (forget₂ RingCat Ab)
  have hi : Presheaf.IsLocallyInjective J φ :=
    ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
      (finiteCoefficientScalarMap T (ULift.{u + 1} Λ)) a b h⟩
  have hs : Presheaf.IsLocallySurjective J φ :=
    ⟨fun s ↦ Presheaf.imageSieve_mem J
      (finiteCoefficientScalarMap T (ULift.{u + 1} Λ)) s⟩
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  unfold functionComparison
  rw [Adjunction.homEquiv_counit]
  change IsIso ((presheafToSheaf J Ab.{u + 1}).map φ ≫
    (Sheaf.sheafifyRingPresheafIso J
      (finiteCoefficientRingSheaf T (ULift.{u + 1} Λ))).hom)
  infer_instance

private theorem commutative_of_iso {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {M N : C} [MonObj M] [MonObj N] [IsCommMonObj N]
    (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M := by
  constructor
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
    ← BraidedCategory.braiding_naturality, Category.assoc, IsCommMonObj.mul_comm]

/-- Both specified constants maps are isomorphisms of commutative ring sheaves,
and their quotient identifies the module categories by restriction of scalars.

Source: blueprint finite coefficient interpretation of the etale-origin witness;
Bhatt--Scholze Lemma 4.2.12
(blueprint: lem-route-finite-origin-constant-comparison-is-iso).

Proof: (1) On the profinite point, the fibres of a finite discrete continuous
function give a finite clopen covering on which it is constant. Constants are
locally injective, using the empty covering on the empty profinite set. Hence
sheafification inverts the specified constant-function map.
(2) The constant-sheaf and inverse-image adjunctions, with their terminal-section
identification, give constantSchemeIso. Pull back the point comparison and compose.
The monoidal comparisons preserve multiplication and the unit on constant sections.
(3) Functions on the connected-component quotient are exactly continuous functions
on the scheme with values in the discrete ring. Locally such functions are constant
on their open fibres, and the empty object is covered by the empty family.
The constants map is therefore locally bijective. Sheafification identifies its
extension with functionComparison, so this map too is an invertible ring morphism.
(4) Compose the inverse function comparison with the condensed comparison. This
isomorphism retains constants, and restriction along it is an equivalence of module
categories, with inverse restriction along its inverse. No step chooses a nonzero
scalar or a point. The zero ring, empty scheme, and empty or disconnected objects
are included. -/
theorem finiteOriginConstantComparison_isIso :
    IsMonHom (constantComparison T Λ) ∧ IsIso (constantComparison T Λ) ∧
      IsCommMonObj (functionRing T Λ) ∧
      IsMonHom (functionComparison T Λ) ∧
      ∃ hg : IsIso (functionComparison T Λ),
      let := hg
      ∃ e : functionRing T Λ ≅
          condensedRingObj (Profinite.continuousCoefficientRingObj Λ) T,
        ∃ h : IsMonHom e.hom,
          e.hom = inv (functionComparison T Λ) ≫ constantComparison T Λ ∧
          functionComparison T Λ ≫ e.hom = constantComparison T Λ ∧
          let := h
          (Mod.comap e.hom : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (Profinite.continuousCoefficientRingObj Λ) T) ⥤
              Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                (functionRing T Λ)).IsEquivalence := by
  let := pointComparison_isIso Λ
  let := constantComparison_isMonHom T Λ
  have hc : IsIso (constantComparison T Λ) := by unfold constantComparison; infer_instance
  let := hc
  let := functionComparison_isMonHom T Λ
  let := functionComparison_isIso T Λ
  let e := (asIso (functionComparison T Λ)).symm ≪≫ asIso (constantComparison T Λ)
  have he : IsMonHom e.hom := by dsimp only [e, Iso.trans_hom, Iso.symm_hom]; infer_instance
  let := he
  have hcomm : IsCommMonObj (functionRing T Λ) := commutative_of_iso e
  let := hcomm
  refine ⟨inferInstance, hc, hcomm, inferInstance, inferInstance, e, he, rfl, ?_, ?_⟩
  · simp [e]
  · exact (Mod.comapEquivalenceOfIsIso e.hom).isEquivalence_functor

end AlgebraicGeometry.ProEtale.FiniteOriginCoefficients
