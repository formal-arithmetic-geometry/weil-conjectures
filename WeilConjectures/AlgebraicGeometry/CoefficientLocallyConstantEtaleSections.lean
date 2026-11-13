/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit

/-! # Etale-local sections of coefficient-sized locally constant set sheaves

Source: Bhatt--Scholze, Lemma 5.1.4; Stacks Project, Tags 099T and 099Y.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A section of a pointwise left Kan extension comes from an object of its source. -/
private theorem inhabited_lan_source
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) (P : Cᵒᵖ ⥤ Type w) (W : D)
    (s : (F.op.lan.obj P).obj (op W)) :
    ∃ V : C, Nonempty (W ⟶ F.obj V) ∧ Nonempty (P.obj (op V)) := by
  have hc := F.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op W)
  obtain ⟨j, x, _⟩ := Types.jointly_surjective_of_isColimit hc s
  exact ⟨j.left.unop, ⟨j.hom.unop⟩, ⟨x⟩⟩

/-- Joint local inhabitedness of a family of locally constant set sheaves can be
witnessed by etale objects. The values and the family may be coefficient-sized.

Source: Bhatt--Scholze, Lemma 5.1.4; Stacks Project, Tag 099T, and the discrete
Isom-sheaf argument in Tag 099Y. -/
theorem coefficientLocallyConstant_etaleSections (X : Scheme.{u})
    (K : Type (max v (u + 1)))
    (H : K → Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (Type (max v (u + 1))))
    (hH : ∀ a : K, ∃ (L : Type (max v (u + 1)))
      (W : L → Scheme.coefficientProEtaleSiteModel.{u, v} X),
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop W ∧
        ∀ j : L, ∃ Q : Type (max v (u + 1)),
          Nonempty ((H a).over (W j) ≅
            (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over (W j))
              (Type (max v (u + 1)))).obj Q))
    (I : Type (max v (u + 1)))
    (U : I → Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (hU : (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop U)
    (hsec : ∀ j : I, ∃ a : K, Nonempty ((H a).obj.obj (op (U j)))) :
    ∃ (L : Type (max v (u + 1)))
      (V : L → Scheme.smallModelComparisonEtaleSite.{u, v} X),
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop
        (fun j ↦ (Scheme.smallModelComparisonInclusion.{u, v} X).obj (V j)) ∧
      ∀ j : L, ∃ a : K, Nonempty ((H a).obj.obj
        (op ((Scheme.smallModelComparisonInclusion.{u, v} X).obj (V j)))) := by
  classical
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let J := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let G := fun a : K ↦ (Scheme.smallModelComparisonPushforward.{u, v} X).obj (H a)
  let P := fun a : K ↦ F.op.lan.obj (G a).obj
  let τ := fun a : K ↦ toSheafify J (P a) ≫
    ((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app (H a)).hom
  have hτ (a : K) : Presheaf.IsLocallySurjective J (τ a) := by
    have : IsIso ((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app (H a)) :=
      coefficientLocallyConstant_counit_isIso X (H a) (hH a)
    have : IsIso (((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app (H a)).hom) :=
      (sheafToPresheaf J (Type (max v (u + 1)))).map_isIso
        ((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app (H a))
    change Presheaf.IsLocallySurjective J
      (toSheafify J (P a) ≫
        ((Scheme.smallModelProEtaleComparison.{u, v} X).counit.app (H a)).hom)
    infer_instance
  let L := Σ V : Scheme.smallModelComparisonEtaleSite.{u, v} X,
    Σ a : K, (H a).obj.obj (op (F.obj V))
  let V : L → Scheme.smallModelComparisonEtaleSite.{u, v} X := fun j ↦ j.1
  refine ⟨L, V, ?_, fun j ↦ ⟨j.2.1, ⟨j.2.2⟩⟩⟩
  intro T
  apply J.transitive (hU T)
  rintro W f ⟨i, ⟨g⟩⟩
  obtain ⟨a, ⟨s⟩⟩ := hsec i
  have := hτ a
  apply J.superset_covering _ (Presheaf.imageSieve_mem J (τ a)
    ((H a).obj.map g.op s))
  rintro Z k ⟨t, _⟩
  obtain ⟨Y, ⟨b⟩, ⟨y⟩⟩ := inhabited_lan_source F (G a).obj Z t
  exact ⟨⟨Y, a, y⟩, ⟨b⟩⟩

end AlgebraicGeometry.ProEtale
