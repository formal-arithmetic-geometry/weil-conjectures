module

public import Sheaf.CategoryTheory.Triangulated.FixedPairTruncationCohomologyFunctors
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
-- The canonical interchange is an unexposed `asIso`; inspect its hom in the proof.
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Shifted cohomology and absorption on fixed pairs

Source: BBD, Proposition 1.3.3 and §§1.3.4–1.3.5, printed pp. 29–31;
blueprint `prop-weil-operations`, truncation and cohomology clauses
(blueprint: lem-pod-fixed-pair-postnikov-identifications).

The imported definition module owns the four existing transport functors.
The isomorphisms in the statement are natural isomorphisms of fixed pairs.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.Triangulated.TStructure

open Limits Endofunctor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairι (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    fixedPairTruncLE t P m ⟶ 𝟭 _ where
  app K := ObjectProperty.homMk
    { f := (t.truncLEι m).app K.carrier
      h := by
        change P.map ((t.truncLEι m).app K.carrier) ≫ K.obj.str =
          ((P.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
            (t.truncLE m).map K.obj.str) ≫ (t.truncLEι m).app K.carrier
        rw [Category.assoc, (t.truncLEι m).naturality, Functor.id_map, ← Category.assoc]
        erw [Functor.eTruncLTIso_hom_app,
          P.eTruncLTIsoApp_hom_eTruncLTι_app t t (m + 1 : ℤ)]
        rfl }
  naturality K L f := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((t.truncLEι m).naturality f.hom.f))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairπ (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    𝟭 _ ⟶ fixedPairTruncGE t P m where
  app K := ObjectProperty.homMk
    { f := (t.truncGEπ m).app K.carrier
      h := by
        change P.map ((t.truncGEπ m).app K.carrier) ≫
            ((P.eTruncGEIso t t m).hom.app K.carrier ≫
              (t.truncGE m).map K.obj.str) = K.obj.str ≫ (t.truncGEπ m).app K.carrier
        rw [← Category.assoc]
        erw [Functor.eTruncGEIso_hom_app, P.eTruncGEπ_app_eTruncGEIsoApp_hom t t m]
        exact ((t.truncGEπ m).naturality K.obj.str).symm }
  naturality K L f := ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((t.truncGEπ m).naturality f.hom.f))

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C] in
private lemma fixedPair_isIso {P : C ⥤ C} {K L : IsoAlgebra P} (f : K ⟶ L)
    (hf : IsIso f.hom.f) : IsIso f := by
  have := hf
  have : IsIso f.hom := Algebra.iso_of_iso f.hom
  exact (ObjectProperty.isIso_hom_iff f).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairLiftLE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ)
    {M K : IsoAlgebra P} [t.IsLE M.carrier m] (f : M ⟶ K) :
    M ⟶ (fixedPairTruncLE t P m).obj K :=
  ObjectProperty.homMk
    { f := t.liftTruncLE f.hom.f m
      h := by
        have := Functor.IsTExact.isLE_obj t t P M.carrier m
        apply t.to_truncLE_obj_ext
        change (P.map (t.liftTruncLE f.hom.f m) ≫
            ((P.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
              (t.truncLE m).map K.obj.str)) ≫ (t.truncLEι m).app K.carrier = _
        have hc : (P.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
            (t.truncLEι m).app (P.obj K.carrier) =
              P.map ((t.truncLEι m).app K.carrier) :=
          P.eTruncLTIsoApp_hom_eTruncLTι_app t t (m + 1 : ℤ) K.carrier
        rw [Category.assoc, Category.assoc, (t.truncLEι m).naturality,
          Functor.id_map, ← Category.assoc ((P.eTruncLTIso t t (m + 1 : ℤ)).hom.app _), hc]
        rw [← Category.assoc, ← P.map_comp, t.liftTruncLE_ι, Category.assoc]
        change P.map f.hom.f ≫ K.obj.str =
          M.obj.str ≫ t.liftTruncLE f.hom.f m ≫ (t.truncLEι m).app K.carrier
        rw [t.liftTruncLE_ι]
        exact f.hom.h }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairDescGE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ)
    {K M : IsoAlgebra P} [t.IsGE M.carrier m] (f : K ⟶ M) :
    (fixedPairTruncGE t P m).obj K ⟶ M :=
  ObjectProperty.homMk
    { f := t.descTruncGE f.hom.f m
      h := by
        apply (cancel_epi ((P.eTruncGEIso t t m).inv.app K.carrier)).mp
        apply t.from_truncGE_obj_ext
        have hn : P.map ((t.truncGEπ m).app K.carrier) ≫
            (P.eTruncGEIso t t m).hom.app K.carrier =
              (t.truncGEπ m).app (P.obj K.carrier) :=
          P.eTruncGEπ_app_eTruncGEIsoApp_hom t t m K.carrier
        have hπ : (t.truncGEπ m).app (P.obj K.carrier) ≫
            (P.eTruncGEIso t t m).inv.app K.carrier =
              P.map ((t.truncGEπ m).app K.carrier) := by
          rw [← hn, Category.assoc, Iso.hom_inv_id_app]
          change P.map ((t.truncGEπ m).app K.carrier) ≫ 𝟙 _ = _
          exact Category.comp_id _
        change (t.truncGEπ m).app (P.obj K.carrier) ≫
            ((P.eTruncGEIso t t m).inv.app K.carrier ≫
              (P.map (t.descTruncGE f.hom.f m) ≫ M.obj.str)) = _
        rw [← Category.assoc, hπ, ← Category.assoc, ← P.map_comp,
          t.π_descTruncGE, f.hom.h]
        change K.obj.str ≫ f.hom.f =
          (t.truncGEπ m).app (P.obj K.carrier) ≫
            (P.eTruncGEIso t t m).inv.app K.carrier ≫
              ((P.eTruncGEIso t t m).hom.app K.carrier ≫
                (t.truncGE m).map K.obj.str) ≫ t.descTruncGE f.hom.f m
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
        change K.obj.str ≫ f.hom.f =
          (t.truncGEπ m).app (P.obj K.carrier) ≫
            (t.truncGE m).map K.obj.str ≫ t.descTruncGE f.hom.f m
        rw [← Category.assoc]
        have hnat := (t.truncGEπ m).naturality K.obj.str
        simp only [Functor.id_map] at hnat
        rw [← hnat, Category.assoc, t.π_descTruncGE] }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairInterchangeMap (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) (K : IsoAlgebra P) :
    (fixedPairTruncGE t P m).obj ((fixedPairTruncLE t P m).obj K) ⟶
      (fixedPairTruncLE t P m).obj ((fixedPairTruncGE t P m).obj K) := by
  have : t.IsGE ((fixedPairTruncGE t P m).obj K).carrier m := by
    change t.IsGE ((t.truncGE m).obj K.carrier) m
    infer_instance
  have : t.IsLE
      ((fixedPairTruncGE t P m).obj ((fixedPairTruncLE t P m).obj K)).carrier m := by
    change t.IsLE ((t.truncGELE m m).obj K.carrier) m
    infer_instance
  exact fixedPairLiftLE t P m
    (fixedPairDescGE t P m ((fixedPairι t P m).app K ≫ (fixedPairπ t P m).app K))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairInterchange (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    fixedPairTruncLE t P m ⋙ fixedPairTruncGE t P m ≅
      fixedPairTruncGE t P m ⋙ fixedPairTruncLE t P m :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk ((t.truncGELEIsoLEGE m m).app K.carrier)
      (by
        have h := (fixedPairInterchangeMap t P m K).hom.h
        have hv : (fixedPairInterchangeMap t P m K).hom.f =
            ((t.truncGELEIsoLEGE m m).app K.carrier).hom := by
          change _ = (t.truncGELTToLTGE m (m + 1)).app K.carrier
          symm
          apply t.truncGELTToLTGE_app_pentagon_uniqueness
          change (t.truncGEπ m).app ((t.truncLE m).obj K.carrier) ≫
              t.liftTruncLE (t.descTruncGE
                ((t.truncLEι m).app K.carrier ≫ (t.truncGEπ m).app K.carrier) m) m ≫
                  (t.truncLEι m).app ((t.truncGE m).obj K.carrier) = _
          rw [t.liftTruncLE_ι, t.π_descTruncGE]
          rfl
        rw [hv] at h
        exact h))) (by
        intro K L f
        apply ObjectProperty.hom_ext _
        apply Algebra.Hom.ext
        exact (t.truncGELEIsoLEGE m m).hom.naturality f.hom.f)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedPairCancel (P : C ⥤ C) [P.CommShift ℤ] (m : ℤ) :
    fixedPairShift P m ⋙ fixedPairShift P (-m) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk ((shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).app K.carrier)
      (by
        change P.map ((shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).hom.app
            K.carrier) ≫ K.obj.str =
          ((P.commShiftIso (-m)).hom.app (K.carrier⟦m⟧) ≫
            ((P.commShiftIso m).hom.app K.carrier ≫ K.obj.str⟦m⟧')⟦-m⟧') ≫
              (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).hom.app K.carrier
        rw [P.map_shiftFunctorCompIsoId_hom_app, Functor.map_comp]
        simp only [Category.assoc]
        congr 2
        exact ((shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).hom.naturality
          K.obj.str).symm))) (by
          intro K L f
          apply ObjectProperty.hom_ext _
          apply Algebra.Hom.ext
          exact (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).hom.naturality f.hom.f)

set_option backward.isDefEq.respectTransparency false in
/-- Shifts and cohomology have the specified structures and underlying functors; the
normalized absorption, shift cancellation and interchange identifications lift to natural
isomorphisms of fixed pairs. No triangulated structure on `IsoAlgebra` is used.
Source: BBD 1.3.3–1.3.5, printed pp. 29–31, with the fixed-pair calculations expanded
in the DAG (blueprint: lem-pod-fixed-pair-postnikov-identifications).

Proof plan, following the seven steps of the node:
1. Naturality of `P.commShiftIso` makes shifted arrows equivariant; identities and
   composition are inherited from the shift functor.
2. The normalized comparisons of `lem-pod-texact-truncation-comparison` give exactly
   `τ(θ)c`. Equivariance of the truncation maps and injectivity of the truncation
   adjunctions identify these with the lifts of
   `lem-a1-fixed-pair-truncation-orthogonality`. Composing these lifts and the shift
   expands the structure into `Hⁱ(θ)e`, and gives the stated arrow and forgetful formulas.
3. Apply `lem-pod-truncation-interchange-pentagon` at equal indices to see that the
   double truncation is in both halves in degree `i`; shifting by `i` puts it in the heart.
4. Apply the lifted right adjunction twice and once to construct inverse arrows between
   the repeated upper truncation and `τ≤m-1`. Their composites to `K` agree; injectivity
   proves inverse laws and naturality, as in `lem-weil-heart-short-exact-triangles`.
5. Dually the lifted left adjunction constructs the lower absorption, normalized by
   its composite from `K`. Uniqueness gives the inverse laws and naturality.
6. Transpose the canonical map `τ≤m K → τ≥m K` through both lifted adjunctions.
   The resulting map satisfies the pentagon, so its underlying map is the canonical
   interchange by `lem-pod-truncation-interchange-pentagon`. Its inverse is equivariant
   by multiplying the equivariance equation by inverses.
7. Zero and addition coherence of `CommShift` make shift cancellation equivariant:
   naturality of cancellation gives `d θ[m][-m] s[m] s = θ P(d)`.
   Its inverse gives the first cohomology identification; compose with the inverse
   interchange for the second. All constructions are natural in the fixed pair. -/
theorem fixedPair_postnikov_identifications
    (t : TStructure C) (_ht : t.bounded = ⊤) (E : C ≌ C)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [E.functor.IsTExact t t] [E.inverse.IsTExact t t] :
    (∀ (r : ℤ) (K : IsoAlgebra E.functor),
      ((fixedPairShift E.functor r).obj K).str =
        (E.functor.commShiftIso r).app K.carrier ≪≫
          (shiftFunctor C r).mapIso K.str) ∧
    (∀ (r : ℤ) (K L : IsoAlgebra E.functor) (f : K ⟶ L),
      ((fixedPairShift E.functor r).map f).hom.f = f.hom.f⟦r⟧') ∧
    (∀ i : ℤ,
      fixedPairCohomology t E.functor i ⋙ IsoAlgebra.forget E.functor =
        IsoAlgebra.forget E.functor ⋙ (t.truncGELE i i ⋙ shiftFunctor C i)) ∧
    (∀ (i : ℤ) (K : IsoAlgebra E.functor),
      t.heart (((fixedPairCohomology t E.functor i).obj K).carrier) ∧
      ((fixedPairCohomology t E.functor i).obj K).str.hom =
        (E.functor.commShiftIso i).hom.app ((t.truncGELE i i).obj K.carrier) ≫
          ((E.functor.eTruncGEIso t t i).hom.app ((t.truncLE i).obj K.carrier) ≫
            (t.truncGE i).map
              ((E.functor.eTruncLTIso t t (i + 1 : ℤ)).hom.app K.carrier))⟦i⟧' ≫
          ((t.truncGELE i i).map K.str.hom)⟦i⟧') ∧
    (∀ (i : ℤ) (K L : IsoAlgebra E.functor) (f : K ⟶ L),
      ((fixedPairCohomology t E.functor i).map f).hom.f =
        ((t.truncGELE i i).map f.hom.f)⟦i⟧') ∧
    (∀ m : ℤ,
      ∃ a : fixedPairTruncLE t E.functor m ⋙ fixedPairTruncLE t E.functor (m - 1) ≅
          fixedPairTruncLE t E.functor (m - 1),
        ∀ K : IsoAlgebra E.functor,
          (a.hom.app K).hom.f ≫ (t.truncLEι (m - 1)).app K.carrier =
            (t.truncLEι (m - 1)).app ((t.truncLE m).obj K.carrier) ≫
              (t.truncLEι m).app K.carrier) ∧
    (∀ m : ℤ,
      ∃ b : fixedPairTruncGE t E.functor m ⋙ fixedPairTruncGE t E.functor (m + 1) ≅
          fixedPairTruncGE t E.functor (m + 1),
        ∀ K : IsoAlgebra E.functor,
          (t.truncGEπ m).app K.carrier ≫
              (t.truncGEπ (m + 1)).app ((t.truncGE m).obj K.carrier) ≫
              (b.hom.app K).hom.f = (t.truncGEπ (m + 1)).app K.carrier) ∧
    (∀ m : ℤ,
      ∃ c : fixedPairTruncLE t E.functor m ⋙ fixedPairTruncGE t E.functor m ≅
          fixedPairCohomology t E.functor m ⋙ fixedPairShift E.functor (-m),
        ∃ d : fixedPairTruncGE t E.functor m ⋙ fixedPairTruncLE t E.functor m ≅
            fixedPairCohomology t E.functor m ⋙ fixedPairShift E.functor (-m),
          ∀ K : IsoAlgebra E.functor,
            (c.hom.app K).hom.f =
              (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).inv.app
                ((t.truncGELE m m).obj K.carrier) ∧
            (d.hom.app K).hom.f = (t.truncGELEIsoLEGE m m).inv.app K.carrier ≫
              (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).inv.app
                ((t.truncGELE m m).obj K.carrier)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r K
    exact IsoAlgebra.mapOfNatIso_obj_str _ _
  · intro r K L f
    rfl
  · intro i
    rfl
  · intro i K
    constructor
    · change t.heart (((t.truncGELE i i).obj K.carrier)⟦i⟧)
      have := t.isLE_shift ((t.truncGELE i i).obj K.carrier) i i 0 (by omega)
      have := t.isGE_shift ((t.truncGELE i i).obj K.carrier) i i 0 (by omega)
      exact ⟨t.le_of_isLE _ _, t.ge_of_isGE _ _⟩
    · simp only [fixedPairCohomology, Functor.comp_obj, fixedPairShift,
        fixedPairTruncLE, fixedPairTruncGE, IsoAlgebra.mapOfNatIso_obj_str,
        Iso.trans_hom, Functor.mapIso_hom, IsoAlgebra.mapOfNatIso_obj_carrier,
        Functor.map_comp, Category.assoc]
      rfl
  · intro i K L f
    rfl
  · intro m
    -- Apply the smaller truncation to the counit; Mathlib proves this map invertible.
    let a := Functor.whiskerRight (fixedPairι t E.functor m)
      (fixedPairTruncLE t E.functor (m - 1))
    have : ∀ K, IsIso (a.app K) := by
      intro K
      apply fixedPair_isIso
      change IsIso ((t.truncLE (m - 1)).map ((t.truncLEι m).app K.carrier))
      exact t.isIso_truncLE_map_truncLEι_app _ _ (by omega) _
    have : IsIso a := NatIso.isIso_of_isIso_app a
    refine ⟨asIso a, ?_⟩
    intro K
    exact (t.truncLEι (m - 1)).naturality ((t.truncLEι m).app K.carrier)
  · intro m
    -- Apply the larger truncation to the unit, then invert the resulting map.
    let b := Functor.whiskerRight (fixedPairπ t E.functor m)
      (fixedPairTruncGE t E.functor (m + 1))
    have : ∀ K, IsIso (b.app K) := by
      intro K
      apply fixedPair_isIso
      change IsIso ((t.truncGE (m + 1)).map ((t.truncGEπ m).app K.carrier))
      exact t.isIso_truncGE_map_truncGEπ_app _ _ (by omega) _
    have : IsIso b := NatIso.isIso_of_isIso_app b
    refine ⟨(asIso b).symm, ?_⟩
    intro K
    have hi := congrArg (fun f ↦ f.hom.f) ((asIso b).hom_inv_id_app K)
    change (t.truncGE (m + 1)).map ((t.truncGEπ m).app K.carrier) ≫
      ((asIso b).inv.app K).hom.f = 𝟙 _ at hi
    change (t.truncGEπ m).app K.carrier ≫
      (t.truncGEπ (m + 1)).app ((t.truncGE m).obj K.carrier) ≫
      ((asIso b).inv.app K).hom.f = _
    have hn := (t.truncGEπ (m + 1)).naturality ((t.truncGEπ m).app K.carrier)
    simp only [Functor.id_map] at hn
    rw [← Category.assoc, hn, Category.assoc, hi, Category.comp_id]
    rfl
  · intro m
    let A := fixedPairTruncLE t E.functor m ⋙ fixedPairTruncGE t E.functor m
    let c : A ≅ fixedPairCohomology t E.functor m ⋙ fixedPairShift E.functor (-m) :=
      (Functor.rightUnitor A).symm ≪≫ Functor.isoWhiskerLeft A (fixedPairCancel E.functor m).symm
    refine ⟨c, (fixedPairInterchange t E.functor m).symm ≪≫ c, ?_⟩
    intro K
    constructor
    · change 𝟙 _ ≫ (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).inv.app
        ((t.truncGELE m m).obj K.carrier) = _
      rw [Category.id_comp]
    · change (t.truncGELEIsoLEGE m m).inv.app K.carrier ≫
        (𝟙 _ ≫ (shiftFunctorCompIsoId C m (-m) (add_neg_cancel m)).inv.app
          ((t.truncGELE m m).obj K.carrier)) = _
      rw [Category.id_comp]

end CategoryTheory.Triangulated.TStructure
