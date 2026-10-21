/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions
import Sheaf.Paper.IntegralLineTensorComparisonIso
import Sheaf.Paper.IntegralLineTensorComparisonRepresentative

/-! Integral line tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

private theorem normalization
    (P : (Good l E X none).FullSubcategory) (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none)
      ((integralLineSingle l E X).obj T))
    (hS : Good l E X none (integralLineComplex l E X P.obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) :
    (integralLineRepresentativeIso l E X P T hT C e).hom ≫
      (integralLineComparison l E X).app (C,T) ≫
      (completion l E X none).map
        (integralLineRepresentativeIso l E X P T hT C e).inv ≫
      (completionComparison l E X none).hom.app
        ⟨integralLineComplex l E X P.obj T, hS⟩ =
      DerivedCategory.Q.map (roosUnit l E X none (integralLineComplex l E X P.obj T)) := by
  let a := integralLineRepresentativeIso l E X P T hT C e
  have hn := (completionUnit l E X none).naturality a.inv
  have hu := (completionUnit_existsUnique l E X none).exists.choose_spec
    ⟨integralLineComplex l E X P.obj T, hS⟩
  have he := congrArg (fun f ↦ a.hom ≫ f ≫
    (completionComparison l E X none).hom.app
      ⟨integralLineComplex l E X P.obj T, hS⟩) hn.symm
  simp only [Functor.id_map, Category.assoc, Iso.hom_inv_id_assoc] at he
  change a.hom ≫ (completionUnit l E X none).app
    ((integralLineOrdinary l E X).obj (C, T)) ≫
    (completion l E X none).map a.inv ≫ _ = _
  exact he.trans hu


private theorem roosUnit_projection (S : Cx l E X none) (n : ℕ) :
    roosUnit l E X none S ≫ integralLineRoosProjection l E X S n =
      ((augmentation l E X none).app S).app (op n) := by
  unfold roosUnit integralLineRoosProjection
  rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst]
  simp [productAugmentation]

/-- Tensor by a locally free integral line commutes with the specified completion.
Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: lem-sf-integral-line-tensor-comparison).

Proof: use the line-completion invertibility result and the K-flat finite balancing
result. Naturality is naturality of completionUnit after the ordinary tensor functor.
For the good tensor model, naturality along the inverse representative isomorphism
and the characterization completionUnit_existsUnique give exactly the normalized
Roos equation. Composing with the inverse representative and the finite projection
gives the final equation, since mappingCocone.lift_fst makes roosUnit followed by
that projection the quotient augmentation. The finite pure-tensor formula comes
from the balancing result. -/
theorem integralLineTensorComparison
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : D l E X none) (hC : IsComplete l E X none C)
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    IsIso ((integralLineComparison l E X).app (C, T)) ∧
    (∀ (C' : D l E X none) (_hC' : IsComplete l E X none C') (f : C ⟶ C')
        (T' : Mod l E X none) [T'.IsFiniteLocallyFreeOfRank 1] (eT : T ≅ T'),
      (integralLineOrdinary l E X).map (f, eT.hom) ≫
          (integralLineComparison l E X).app (C', T') =
        (integralLineComparison l E X).app (C, T) ≫
          (integralLineCompleted l E X).map (f, eT.hom)) ∧
    ∀ (P : (Good l E X none).FullSubcategory) (e : DerivedCategory.Q.obj P.obj ≅ C),
      ∃ (hT : CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none)
          ((integralLineSingle l E X).obj T))
        (hS : Good l E X none (integralLineComplex l E X P.obj T)),
        (integralLineRepresentativeIso l E X P T hT C e).hom ≫
            (integralLineComparison l E X).app (C, T) ≫
            (completion l E X none).map
              (integralLineRepresentativeIso l E X P T hT C e).inv ≫
            (completionComparison l E X none).hom.app
              ⟨integralLineComplex l E X P.obj T, hS⟩ =
          DerivedCategory.Q.map (roosUnit l E X none (integralLineComplex l E X P.obj T)) ∧
        ∀ n : ℕ, ∃ β :
            (integralLineFiniteComplex l E X n).obj (integralLineComplex l E X P.obj T) ≅
              integralLineFiniteTensor l E X P.obj T n,
          (∀ (p q k : ℤ) (hpq : p + q = k) (V : X.ProEtᵒᵖ)
              (a : (finite l E X none n).obj.obj V)
              (x : (P.obj.X p).val.obj V)
              (y : (((integralLineSingle l E X).obj T).X q).val.obj V),
            (β.hom.f k).val.app V
                (generator l E X none n ((integralLineComplex l E X P.obj T).X k) V a
                  (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
                    p q k hpq V x y)) =
              coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
                ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
                p q k hpq V (generator l E X none n (P.obj.X p) V a x)
                (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)) ∧
          (integralLineComparison l E X).app (C, T) ≫
              (completion l E X none).map
                (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              (completionComparison l E X none).hom.app
                ⟨integralLineComplex l E X P.obj T, hS⟩ ≫
              DerivedCategory.Q.map
                (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
                  (integralLineFiniteRestrict l E X n).map β.hom) =
            (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              DerivedCategory.Q.map
                (((augmentation l E X none).app (integralLineComplex l E X P.obj T)).app
                    (op n) ≫ (integralLineFiniteRestrict l E X n).map β.hom) := by
  refine ⟨integralLineTensorComparison_iso l E X _hl C hC T, ?_, ?_⟩
  · intro C' hC' f T' _ eT
    let g : (C, T) ⟶ (C', T') := (f, eT.hom)
    have hn := (completionUnit l E X none).naturality
      ((integralLineOrdinary l E X).map g)
    simpa [g, integralLineComparison, integralLineOrdinary, integralLineCompleted,
      completedTensor, Functor.whiskerLeft] using hn
  · intro P e
    obtain ⟨hT, hS, hβ⟩ := integralLineTensorComparison_representative l E X T P
    have hn := normalization l E X P T hT hS C e
    refine ⟨hT, hS, hn, ?_⟩
    intro n
    obtain ⟨β, hβ⟩ := hβ n
    refine ⟨β, hβ, ?_⟩
    let a := integralLineRepresentativeIso l E X P T hT C e
    have hm := congrArg (fun f ↦ a.inv ≫ f) hn
    dsimp only [a] at hm
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hm
    simp only [Category.assoc] at hm
    have ht := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
      (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
        (integralLineFiniteRestrict l E X n).map β.hom)) hm
    have hp := congrArg
      (fun f ↦ f ≫ (integralLineFiniteRestrict l E X n).map β.hom)
      (roosUnit_projection l E X (integralLineComplex l E X P.obj T) n)
    simp only [Category.assoc] at hp
    simp only [Category.assoc, ← Functor.map_comp, hp] at ht
    exact ht

end WeilConjectures
