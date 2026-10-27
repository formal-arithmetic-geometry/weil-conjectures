/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
import Sheaf.Paper.FiniteWeilIndPushExact

/-! Auxiliary finite compactification result.
Source: blueprint main-20261015, sk-l-dl-general-quasifinite.
(blueprint: lem-zl-finite-compactification-weil-exact).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

section Embedding
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem smallPairs_essSurj : (zlWeilSmallPairs D l hl Ω X₀).EssSurj := by
  let F := zlWeilSmallPairs D l hl Ω X₀
  constructor
  intro A
  let K : sfCommonStageWeilSheaf D l hl X₀ Ω :=
    ⟨IsoAlgebra.mk ((AsSmall.down.obj A.carrier) :
        sfCommonStageHeart l (D.geometricFiber X₀).left Ω).obj
      { hom := A.str.hom.down.hom
        inv := A.str.inv.down.hom
        hom_inv_id := congrArg (fun f ↦ f.down.hom) A.str.hom_inv_id
        inv_hom_id := congrArg (fun f ↦ f.down.hom) A.str.inv_hom_id },
      ((AsSmall.down.obj A.carrier) :
        sfCommonStageHeart l (D.geometricFiber X₀).left Ω).property⟩
  have hk := (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose_spec
  have hc : (F.obj K).carrier = A.carrier := hk.1 K
  have hs : HEq (F.obj K).str.hom.down.hom A.str.hom.down.hom := hk.2.1 K
  have obj_ext (B B' : IsoAlgebra (zlSmallFrobenius D l hl Ω X₀))
      (hc : B.carrier = B'.carrier)
      (hs : HEq B.str.hom.down.hom B'.str.hom.down.hom) : B = B' := by
    rcases B with ⟨⟨a, sa⟩, ha⟩
    rcases B' with ⟨⟨b, sb⟩, hb⟩
    change a = b at hc
    cases hc
    have hstr : sa = sb := by
      apply ULift.ext
      apply ObjectProperty.hom_ext
      exact eq_of_heq hs
    cases hstr
    rfl
  have h : F.obj K = A := obj_ext _ _ hc hs
  exact ⟨K, ⟨eqToIso h⟩⟩

private theorem embedding_exact :
    PreservesFiniteLimits (zlWeilIndEmbedding D l hl Ω X₀) ∧
    PreservesFiniteColimits (zlWeilIndEmbedding D l hl Ω X₀) := by
  obtain ⟨ha, hlm, hco, he⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := ha
  let := hlm
  let := hco
  let := he
  let Φ := zlSmallFrobenius D l hl Ω X₀
  let J : zlSmallHeart D l Ω hl X₀ ⥤ Ind (zlSmallHeart D l Ω hl X₀) := Ind.yoneda
  have : PreservesFiniteLimits (Φ ⋙ J) :=
    preservesFiniteLimits_of_natIso (zlIndMapIso Φ)
  have : PreservesFiniteColimits (Φ ⋙ J) :=
    preservesFiniteColimits_of_natIso (zlIndMapIso Φ)
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_reflects_of_preserves Φ J
  have : PreservesFiniteColimits Φ := preservesFiniteColimits_of_reflects_of_preserves Φ J
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  let G := IsoAlgebra.mapOfNatIso (zlIndMapIso Φ)
  have hGlim : PreservesFiniteLimits G := inferInstance
  have hGcolim : PreservesFiniteColimits G := inferInstance
  let F := zlWeilSmallPairs D l hl Ω X₀
  obtain ⟨hfull, hfaith⟩ := zlWeilIndEmbedding_full_faithful D l hl Ω X₀
  have : (F ⋙ G).Full := hfull
  have : (F ⋙ G).Faithful := hfaith
  have : G.Faithful := by
    constructor
    intro K L a b h
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply J.map_injective
    exact congrArg (fun f ↦ f.hom.f) h
  have : F.Full := Functor.Full.of_comp_faithful F G
  have : F.Faithful := Functor.Faithful.of_comp F G
  let := smallPairs_essSurj D l hl Ω X₀
  have : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  change PreservesFiniteLimits (F ⋙ G) ∧ PreservesFiniteColimits (F ⋙ G)
  exact ⟨inferInstance, inferInstance⟩

section
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]

private theorem exactLift (E : B ⥤ A) [E.Full] [E.Faithful]
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (T : C ⥤ A) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hT : ∀ X, E.essImage (T.obj X)) :
    ∃ H : C ⥤ B, H.Additive ∧ PreservesFiniteLimits H ∧ PreservesFiniteColimits H ∧
      Nonempty (H ⋙ E ≅ T) := by
  let H := Functor.essImage.liftFunctor T E hT
  let e : H ⋙ E ≅ T := Functor.essImage.liftFunctorCompIso T E hT
  have : PreservesFiniteLimits (H ⋙ E) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (H ⋙ E) := preservesFiniteColimits_of_natIso e.symm
  have : PreservesFiniteLimits H := preservesFiniteLimits_of_reflects_of_preserves H E
  have : PreservesFiniteColimits H := preservesFiniteColimits_of_reflects_of_preserves H E
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  exact ⟨H, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

private theorem exactHigher (T : C ⥤ B) [T.Additive] [HasInjectiveResolutions C]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (X : C) (n : ℕ) (hn : 0 < n) : IsZero ((T.rightDerived n).obj X) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let I : InjectiveResolution X := Classical.choice (HasInjectiveResolution.out (Z := X))
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj T (q + 1))
  exact (T.map_isZero (I.cocomplex_exactAt_succ q).isZero_homology).of_iso
    ((I.cocomplex.sc (q + 1)).mapHomologyIso T)

end

end Embedding

/-- A finite compactification has concentrated compact-support images and an exact
heart-level degree-zero realization. This is a statement about the specified ind-derived
higher images, with their Weil structure; it has no weight or embedding hypothesis.

Source: blueprint main-20261015, `lem-zl-quasi-finite.proof.md`, clause (1);
Stacks Tags 03QP, 09A8; Bhatt--Scholze 6.8.14--6.8.15.
(blueprint: lem-zl-finite-compactification-weil-exact).

Proof: the finite-direct-image part is `sfFiniteWeilIndPushExact`. Its left
exactness follows from the defining inverse-image adjunction. The exact open extension
and the exact Yoneda fixed-pair embedding give an exact composite T on ind-objects.
To verify exactness of the embedding, the small-presentation functor is an equivalence:
its inverse on objects takes the same carrier and Weil isomorphism, and full faithfulness
follows by cancellation from that of the recorded embedding. The ind Frobenius comparison
and reflection along Yoneda show that the small Frobenius is exact. Thus transport to
fixed pairs along exact Yoneda preserves finite limits and colimits.

The zeroth-right-derived comparison identifies T(F) with the ind-object represented
by the specified zeroth higher image. Lift the entire functor through the fully faithful
target embedding using these representations. Its comparison is natural by construction,
so exactness reflects to the lift; finite-product preservation also gives additivity.
Full faithfulness lifts the object comparisons to the required Weil isomorphisms.

For positive degrees, compute the finite direct image on an injective resolution.
Exactness commutes with cohomology, so positive cohomology is the image of zero.
The specified representation isomorphism and faithful target embedding detect the
vanishing of the recorded higher image. This proves the statement for arbitrary
finite compactifications without a choice of new Weil action. Empty objects and
length-zero complexes obey the same argument. -/
theorem sfFiniteCompactificationWeilExact
    [QuasiSeparated Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)
    [IsFinite c.g] :
    ∃ H : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤ sfCommonStageWeilSheaf D l hl Y₀ Ω,
      H.Additive ∧ PreservesFiniteLimits H ∧ PreservesFiniteColimits H ∧
        (∀ F, Nonempty (H.obj F ≅ zlWeilHigherShriek D l hl Ω f₀ c 0 F)) ∧
        ∀ (F : sfCommonStageWeilSheaf D l hl X₀ Ω) (i : ℕ),
          0 < i → IsZero (zlWeilHigherShriek D l hl Ω f₀ c i F) := by
  let : IsFinite (zlCompactificationProper D f₀ c).left :=
    inferInstanceAs (IsFinite c.g)
  have hpush := sfFiniteWeilIndPushExact D l hl Ω
    (zlCompactificationProper D f₀ c)
  let EX := zlWeilIndEmbedding D l hl Ω X₀
  let EY := zlWeilIndEmbedding D l hl Ω Y₀
  let J := zlIndWeilOpenShriek D l hl Ω (zlCompactificationOpen D f₀ c)
  let P := zlIndWeilPush D l hl Ω (zlCompactificationProper D f₀ c)
  obtain ⟨hEXlim, hEXcolim⟩ := embedding_exact D l hl Ω X₀
  obtain ⟨hEYlim, hEYcolim⟩ := embedding_exact D l hl Ω Y₀
  let := hEXlim
  let := hEXcolim
  let := hEYlim
  let := hEYcolim
  have : EX.Additive := Functor.additive_of_preserves_binary_products EX
  have : EY.Additive := Functor.additive_of_preserves_binary_products EY
  obtain ⟨hfull, hfaith⟩ := zlWeilIndEmbedding_full_faithful D l hl Ω Y₀
  let := hfull
  let := hfaith
  obtain ⟨hJa, hJl, hJc⟩ :=
    zlIndWeilOpenShriek_exact D l hl Ω (zlCompactificationOpen D f₀ c)
  let := hJa
  let := hJl
  let := hJc
  let := hpush
  let := zlIndWeilPull_isLeftAdjoint D l hl Ω (zlCompactificationProper D f₀ c)
  have : P.IsRightAdjoint := by
    change (zlIndWeilPull D l hl Ω (zlCompactificationProper D f₀ c)).rightAdjoint.IsRightAdjoint
    infer_instance
  let T := EX ⋙ J ⋙ P
  have represent (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
      Nonempty (EY.obj (zlWeilHigherShriek D l hl Ω f₀ c 0 F) ≅ T.obj F) := by
    obtain ⟨e⟩ := (zlWeilHigherShriek_representable D l hl Ω f₀ c 0 F).choose_spec
    exact ⟨e ≪≫ P.rightDerivedZeroIsoSelf.app (J.obj (EX.obj F))⟩
  obtain ⟨H, hHa, hHl, hHc, ⟨eH⟩⟩ := exactLift EY T (fun F ↦
    ⟨zlWeilHigherShriek D l hl Ω f₀ c 0 F, represent F⟩)
  refine ⟨H, hHa, hHl, hHc, ?_, ?_⟩
  · intro F
    obtain ⟨e⟩ := represent F
    exact ⟨EY.preimageIso (eH.app F ≪≫ e.symm)⟩
  · intro F i hi
    obtain ⟨e⟩ := (zlWeilHigherShriek_representable D l hl Ω f₀ c i F).choose_spec
    have hz := (exactHigher P (J.obj (EX.obj F)) i hi).of_iso e
    apply (IsZero.iff_id_eq_zero _).mpr
    apply EY.map_injective
    rw [EY.map_id, EY.map_zero]
    exact (IsZero.iff_id_eq_zero _).mp hz

end WeilConjectures
