/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory

/-!
# Étale sum extension and unbounded tensor totalization

Source: literature/stacks-project/more-etale.tex, Tag 0GKF
(blueprint: lem-pur-etale-sum-tensor-totalization).
-/


@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

namespace AlgebraicGeometry

universe vC vD uC uD

section GenericHomotopies

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D]
  (F : C ⥤ C ⥤ C) (G : D ⥤ D ⥤ D)
  [F.Additive] [∀ M : C, (F.obj M).Additive]
  [G.Additive] [∀ M : D, (G.obj M).Additive]
  [∀ P H : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor P H F (.up ℤ)]
  [∀ P H : CochainComplex D ℤ, HomologicalComplex.HasMapBifunctor P H G (.up ℤ)]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]

/-- Comparison families for additive functors and total tensor bifunctors.
Source: literature/stacks-project/homology.tex, Tag 012Z, with more-etale.tex Tag 0GKF;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorComparison :=
  ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ),
    HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P) H G (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ))

/-- Naturality of a comparison in both chain-map variables.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF, natural projection;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorNaturality (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∀ (P P' : CochainComplex C ℤ) (H H' : CochainComplex D ℤ)
    (f : P ⟶ P') (g : H ⟶ H'),
    HomologicalComplex.mapBifunctorMap ((L.mapHomologicalComplex (.up ℤ)).map f)
      g G (.up ℤ) ≫ (Ψ P' H').hom =
      (Ψ P H).hom ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f
          ((R.mapHomologicalComplex (.up ℤ)).map g) F (.up ℤ))

/-- The comparison has the prescribed canonical component on every total summand.
Source: literature/stacks-project/homology.tex, Tag 012Z, coproduct terms;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorSummandNormalization (Ψ : TotalTensorComparison F G L R)
    (a : ∀ (M : C) (N : D),
      (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N))) : Prop :=
  ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ)
    (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n h ≫ (Ψ P H).hom.f n =
        a (P.X p) (H.X q) ≫ L.map
          (HomologicalComplex.ιMapBifunctor P ((R.mapHomologicalComplex (.up ℤ)).obj H)
            F (.up ℤ) p q n h)

/-- Intertwining of the actual degree-minus-one maps of Mathlib's canonical
first-variable total homotopy (`mapBifunctorMapHomotopy₁`).
Source: literature/stacks-project/homology.tex, Section 010V and Tag 012Z;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyComparison₁
    (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∀ (P P' : CochainComplex C ℤ) (H : CochainComplex D ℤ)
    (f f' : P ⟶ P') (h : Homotopy f f') (i j : ℤ),
    (HomologicalComplex.mapBifunctorMapHomotopy₁ (L.mapHomotopy h)
      (𝟙 H) G (.up ℤ)).hom i j ≫ (Ψ P' H).hom.f j =
      (Ψ P H).hom.f i ≫ L.map
        ((HomologicalComplex.mapBifunctorMapHomotopy₁ h
          (𝟙 ((R.mapHomologicalComplex (.up ℤ)).obj H)) F (.up ℤ)).hom i j)

/-- Intertwining of Mathlib's canonical second-variable signed total homotopy
(`mapBifunctorMapHomotopy₂`), with summand maps `(-1)^p (1 ⊗ k^q)`.
Source: literature/stacks-project/homology.tex, Section 010V and Tag 012Z;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyComparison₂
    (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∀ (P : CochainComplex C ℤ) (H H' : CochainComplex D ℤ)
    (g g' : H ⟶ H') (h : Homotopy g g') (i j : ℤ),
    (HomologicalComplex.mapBifunctorMapHomotopy₂
      (𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj P)) h G (.up ℤ)).hom i j ≫
        (Ψ P H').hom.f j =
      (Ψ P H).hom.f i ≫ L.map
        ((HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P)
          (R.mapHomotopy h) F (.up ℤ)).hom i j)

/-- The induced bifunctor `K(C) × K(D) ⥤ K(D)`, `(P,H) ↦ Tot(L P ⊗ H)`, on homotopy categories.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyLeft :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  (((whiskeringLeft₂ _).obj (L.mapHomotopyCategory (.up ℤ))).obj
    (𝟭 (HomotopyCategory D (.up ℤ)))).obj
    (G.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))

/-- The induced bifunctor `K(C) × K(D) ⥤ K(D)`, `(P,H) ↦ L Tot(P ⊗ R H)`, on homotopy categories.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyRight :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  ((CategoryTheory.Functor.postcompose₂.obj (L.mapHomotopyCategory (.up ℤ))).obj
    ((((whiskeringLeft₂ _).obj (𝟭 (HomotopyCategory C (.up ℤ)))).obj
      (R.mapHomotopyCategory (.up ℤ))).obj
      (F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))))

/-- Descent is a natural isomorphism between the actual induced bifunctors on
homotopy categories; its components on quotient objects are precisely `Q(Ψ)`.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyIso
    (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∃ η : TotalTensorHomotopyLeft G L ≅ TotalTensorHomotopyRight F L R,
    ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ),
      ((η.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj H)) =
          (HomotopyCategory.quotient D (.up ℤ)).map (Ψ P H).hom

/-- All clauses imposed on the comparison `Ψ`: the summand normalization by the component
maps `a`, naturality in both variables, intertwining of both canonical total homotopies,
and descent to a natural isomorphism of the induced homotopy-category bifunctors.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF, and homology.tex Section 010V
and Tag 012Z; (blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorClauses (Ψ : TotalTensorComparison F G L R)
    (a : ∀ (M : C) (N : D),
      (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N))) : Prop :=
  TotalTensorSummandNormalization F G L R Ψ a ∧
    TotalTensorNaturality F G L R Ψ ∧
    TotalTensorHomotopyComparison₁ F G L R Ψ ∧
    TotalTensorHomotopyComparison₂ F G L R Ψ ∧
    TotalTensorHomotopyIso F G L R Ψ

private noncomputable def totalTensorMapX
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).X n ⟶
      L.obj ((HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦
    (a (P.X p) (H.X q)).hom ≫ L.map
      (HomologicalComplex.ιMapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h))

private theorem totalTensorMapX_ι
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n h ≫ totalTensorMapX F G L R a P H n =
      (a (P.X p) (H.X q)).hom ≫ L.map
        (HomologicalComplex.ιMapBifunctor P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

private theorem totalTensorMapX_orZero
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) :
    HomologicalComplex.ιMapBifunctorOrZero ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n ≫ totalTensorMapX F G L R a P H n =
      (a (P.X p) (H.X q)).hom ≫ L.map
        (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n) := by
  by_cases h : p + q = n
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ G (.up ℤ) p q n h,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ F (.up ℤ) p q n h]
    exact totalTensorMapX_ι F G L R a P H p q n h
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ G (.up ℤ) p q n h,
      HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ F (.up ℤ) p q n h]
    simp

private noncomputable def totalTensorInvX
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    L.obj ((HomologicalComplex.mapBifunctor P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).X n) ⟶
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).X n :=
  Cofan.IsColimit.desc
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := L) (F := F) P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) n)
    (fun x ↦ (a (P.X x.1.1) (H.X x.1.2)).inv ≫
      HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        H G (.up ℤ) x.1.1 x.1.2 n x.2)

private theorem totalTensorInvX_ι
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n) :
    L.map (HomologicalComplex.ιMapBifunctor P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h) ≫
        totalTensorInvX F G L R a P H n =
      (a (P.X p) (H.X q)).inv ≫
        HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
          H G (.up ℤ) p q n h := by
  exact Cofan.IsColimit.fac
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := L) (F := F) P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) n)
    (fun x ↦ (a (P.X x.1.1) (H.X x.1.2)).inv ≫
      HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        H G (.up ℤ) x.1.1 x.1.2 n x.2) ⟨⟨p, q⟩, h⟩

private theorem totalTensorMapX_isIso
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    IsIso (totalTensorMapX F G L R a P H n) := by
  refine ⟨totalTensorInvX F G L R a P H n, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [← Category.assoc, totalTensorMapX_ι, Category.assoc,
      totalTensorInvX_ι, Iso.hom_inv_id_assoc, Category.comp_id]
  · apply HomologicalComplex.mapBifunctor.hom_ext_of_map L
    intro p q hpq
    rw [← Category.assoc, totalTensorInvX_ι, Category.assoc,
      totalTensorMapX_ι, Iso.inv_hom_id_assoc, Category.comp_id]

private theorem totalTensorMapX_comm
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n m : ℤ) :
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).d n m ≫ totalTensorMapX F G L R a P H m =
    totalTensorMapX F G L R a P H n ≫ L.map
      ((HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).d n m) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂, Preadditive.add_comp,
    ← Category.assoc _ (totalTensorMapX F G L R a P H n),
    totalTensorMapX_ι F G L R a P H p q n hpq,
    Category.assoc, ← CategoryTheory.Functor.map_comp,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    CategoryTheory.Functor.map_add, Preadditive.comp_add]
  congr 1
  · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (by rfl),
      HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (by rfl),
      Linear.units_smul_comp, Category.assoc, totalTensorMapX_orZero]
    convert congrArg (fun z ↦
      (ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) •
        (z ≫ L.map (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) (p + 1) q m)))
        (ha (P.d p (p + 1)) (𝟙 (H.X q))) using 1 <;>
      simp [Units.smul_def, CategoryTheory.Functor.map_comp, Category.assoc] <;> rfl
  · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ (by rfl),
      HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ (by rfl),
      Linear.units_smul_comp, Category.assoc, totalTensorMapX_orZero]
    convert congrArg (fun z ↦
      (ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) •
        (z ≫ L.map (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p (q + 1) m)))
        (ha (𝟙 (P.X p)) (H.d q (q + 1))) using 1 <;>
      simp [Units.smul_def, CategoryTheory.Functor.map_comp, Category.assoc] <;> rfl

private noncomputable def totalTensorIso
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g))) :
    TotalTensorComparison F G L R := by
  intro P H
  let f : HomologicalComplex.mapBifunctor
      ((L.mapHomologicalComplex (.up ℤ)).obj P) H G (.up ℤ) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)) :=
    { f := totalTensorMapX F G L R a P H
      comm' n m _ := (totalTensorMapX_comm F G L R a ha P H n m).symm }
  have (n : ℤ) : IsIso (f.f n) := totalTensorMapX_isIso F G L R a P H n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

private theorem totalTensorIso_normalization
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g))) :
    TotalTensorSummandNormalization F G L R (totalTensorIso F G L R a ha)
      (fun M N ↦ (a M N).hom) := by
  intro P H p q n h
  exact totalTensorMapX_ι F G L R a P H p q n h

private theorem totalTensor_normalization_orZero
    (Ψ : TotalTensorComparison F G L R)
    (a : ∀ M N, (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N)))
    (hn : TotalTensorSummandNormalization F G L R Ψ a)
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) :
    HomologicalComplex.ιMapBifunctorOrZero ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n ≫ (Ψ P H).hom.f n =
      a (P.X p) (H.X q) ≫ L.map
        (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n) := by
  by_cases h : p + q = n
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ G (.up ℤ) p q n h,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ F (.up ℤ) p q n h]
    exact hn P H p q n h
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h,
      HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h]
    simp

private theorem totalTensor_naturality
    (Ψ : TotalTensorComparison F G L R)
    (a : ∀ M N, (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ a M' N' =
        a M N ≫ L.map ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)))
    (hn : TotalTensorSummandNormalization F G L R Ψ a) :
    TotalTensorNaturality F G L R Ψ := by
  intro P P' H H' f g
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    Category.assoc, Category.assoc, hn P' H' p q n hpq,
    ← Category.assoc _ ((Ψ P H).hom.f n), hn P H p q n hpq,
    Category.assoc, ← CategoryTheory.Functor.map_comp,
    HomologicalComplex.ι_mapBifunctorMap, CategoryTheory.Functor.map_comp]
  convert congrArg (fun z ↦ z ≫ L.map
    (HomologicalComplex.ιMapBifunctor P'
      ((R.mapHomologicalComplex (.up ℤ)).obj H') F (.up ℤ) p q n hpq))
      (ha (f.f p) (g.f q)) using 1 <;>
    simp [CategoryTheory.Functor.map_comp, Category.assoc] <;> rfl

private theorem totalTensor_homotopies
    (Ψ : TotalTensorComparison F G L R)
    (a : ∀ M N, (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ a M' N' =
        a M N ≫ L.map ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)))
    (hn : TotalTensorSummandNormalization F G L R Ψ a) :
    TotalTensorHomotopyComparison₁ F G L R Ψ ∧
      TotalTensorHomotopyComparison₂ F G L R Ψ := by
  constructor
  · intro P P' H f f' h i j
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₁]
    rw [← Category.assoc,
      HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
        _ _ _ _ _ _ _ _ _ hpq rfl]
    rw [Linear.units_smul_comp, Category.assoc, Category.assoc,
      totalTensor_normalization_orZero F G L R Ψ a hn,
      ← Category.assoc _ ((Ψ P H).hom.f i), hn P H p q i hpq,
      Category.assoc, ← CategoryTheory.Functor.map_comp,
      HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
        _ _ _ _ _ _ _ _ _ hpq rfl]
    dsimp only [CategoryTheory.Functor.mapHomotopy]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
    simp only [Units.smul_def, CategoryTheory.Functor.map_zsmul, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    congr 1
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    convert congrArg (fun z ↦ z ≫ L.map
      (HomologicalComplex.ιMapBifunctorOrZero P'
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)
        ((ComplexShape.up ℤ).prev p) q j)) (ha (h.hom p _) (𝟙 (H.X q))) using 1 <;>
      simp [CategoryTheory.Functor.map_comp, Category.assoc] <;> rfl
  · intro P H H' g g' h i j
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    dsimp only [HomologicalComplex.mapBifunctorMapHomotopy₂]
    rw [← Category.assoc,
      HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
        _ _ _ _ _ _ _ _ _ hpq rfl]
    rw [Linear.units_smul_comp, Category.assoc, Category.assoc,
      totalTensor_normalization_orZero F G L R Ψ a hn,
      ← Category.assoc _ ((Ψ P H).hom.f i), hn P H p q i hpq,
      Category.assoc, ← CategoryTheory.Functor.map_comp,
      HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
        _ _ _ _ _ _ _ _ _ hpq rfl]
    dsimp only [CategoryTheory.Functor.mapHomotopy]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
    simp only [Units.smul_def, CategoryTheory.Functor.map_zsmul, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    congr 1
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    convert congrArg (fun z ↦ z ≫ L.map
      (HomologicalComplex.ιMapBifunctorOrZero P
        ((R.mapHomologicalComplex (.up ℤ)).obj H') F (.up ℤ)
        p ((ComplexShape.up ℤ).prev q) j)) (ha (𝟙 (P.X p)) (h.hom q _)) using 1 <;>
      simp [CategoryTheory.Functor.map_comp, Category.assoc] <;> rfl

private theorem totalTensor_descent
    (Ψ : TotalTensorComparison F G L R)
    (hn : TotalTensorNaturality F G L R Ψ) :
    TotalTensorHomotopyIso F G L R Ψ := by
  let Q := HomotopyCategory.quotient D (.up ℤ)
  refine ⟨NatIso.ofComponents (fun P ↦ NatIso.ofComponents
    (fun H ↦ Q.mapIso (Ψ P.as H.as)) ?_) ?_, ?_⟩
  · intro H H' g
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient D (.up ℤ)).map_surjective g
    change Q.map (HomologicalComplex.mapBifunctorMap
      (𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj P.as)) g G (.up ℤ)) ≫
        Q.map (Ψ P.as H'.as).hom =
      Q.map (Ψ P.as H.as).hom ≫ Q.map
        ((L.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.mapBifunctorMap
          (𝟙 P.as) ((R.mapHomologicalComplex (.up ℤ)).map g) F (.up ℤ)))
    simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp] using
      congrArg ((HomotopyCategory.quotient D (.up ℤ)).map)
        (hn P.as P.as H.as H'.as (𝟙 P.as) g)
  · intro P P' f
    apply NatTrans.ext
    funext H
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    change Q.map (HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f) (𝟙 H.as) G (.up ℤ)) ≫
        Q.map (Ψ P'.as H.as).hom =
      Q.map (Ψ P.as H.as).hom ≫ Q.map
        ((L.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.mapBifunctorMap
          f (𝟙 ((R.mapHomologicalComplex (.up ℤ)).obj H.as)) F (.up ℤ)))
    simpa only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp] using
      congrArg ((HomotopyCategory.quotient D (.up ℤ)).map)
        (hn P.as P'.as H.as H.as f (𝟙 H.as))
  · intro P H
    rfl

end GenericHomotopies

/-- The category of sheaves of `A`-modules on the small étale site.
Source: literature/stacks-project/sites-cohomology.tex, Section 06YL;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
abbrev EtaleModuleSheaf (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)

/-- Unbounded integer-indexed cochain complexes in `EtaleModuleSheaf`.
Source: literature/stacks-project/homology.tex, Section 010V;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
abbrev EtaleModuleComplex (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  CochainComplex (EtaleModuleSheaf T A) ℤ

/-- Families of totalization comparison isomorphisms with the two endpoint complexes
specified by the étale lower-shriek and upper-star functors.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def EtaleSumTensorComparison
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (u : U ⟶ X)
    (hu : Etale u) [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] :=
  TotalTensorComparison
    (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu)
    (Etale.upperStar (ModuleCat.{u + 1} A) u)

/-- The canonical component map has the orientation of the statement: it is the
inverse of `Etale.etaleLowerShriekTensorIso`, whose hom is oriented in the other
direction. This is the inverse of the sheafified presheaf Kan-extension
projection, transported through `upperStarIsoLocalizationRestriction`, the
sheafification tensor comparison, and the sheafification counits. Thus before
sum and tensor sheafification its generator is `(s,m) ⊗ h ↦ (s,m ⊗ s^*h)`.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF, pure-tensor construction;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable abbrev etaleSumTensorComponent
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (u : U ⟶ X)
    (hu : Etale u) [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (P : EtaleModuleComplex U A) (H : EtaleModuleComplex X A)
    (p q : ℤ) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu).obj (P.X p) ⊗ H.X q) ⟶
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu).obj
        (P.X p ⊗ ((Etale.upperStar (ModuleCat.{u + 1} A) u).obj (H.X q))) :=
  (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu (P.X p) (H.X q)).inv

/-- The clauses of the statement for the étale comparison `Ψ`: on every `(p,q)`
totalization summand its component is the canonical sheaf projection map
`etaleSumTensorComponent` (the inverse of `Etale.etaleLowerShriekTensorIso`, tensor
factors in the original order), followed by the inclusion of `L(P^p ⊗ R H^q)`; `Ψ` is
natural in both complex variables; it intertwines Mathlib's two canonical signed total
homotopies (`mapBifunctorMapHomotopy₁`, `mapBifunctorMapHomotopy₂`); and it descends to
a natural isomorphism of the induced homotopy-category bifunctors with components `Q(Ψ)`.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF, and homology.tex Section 010V
and Tag 012Z; (blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def EtaleSumTensorClauses
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (u : U ⟶ X)
    (hu : Etale u) [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (Ψ : EtaleSumTensorComparison A u hu) : Prop :=
  TotalTensorClauses
    (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu)
    (Etale.upperStar (ModuleCat.{u + 1} A) u) Ψ
    (fun M N ↦ (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M N).inv)

/-- Preservation of all small direct sums by the étale sum extension.
Source: literature/stacks-project/categories.tex, Tag 0038 (1), left adjoints and colimits;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def EtaleSumPreservesDirectSums
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (u : U ⟶ X)
    (hu : Etale u) [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] : Prop :=
  ∀ (β : Type (u + 1)),
    PreservesColimitsOfShape (Discrete β)
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu)


/-- For a separated étale finite-type morphism, sum extension commutes canonically with
unbounded total tensor complexes, naturally in both variables and compatibly with chain
homotopies.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF
(blueprint: lem-pur-etale-sum-tensor-totalization).
Proof plan (the seven steps of the DAG node):

1. Put `L = u_{Σ!}` and `R = u^*`. By
[lem-weil-pbc-etale-restriction-injectives], `L` is left adjoint to `R`.
[lem-weil-pbc-left-adjoint-preserves-colimits] (Stacks Tag 0038 (1)) applied to
any discrete shape gives direct-sum preservation, including the empty sum.
The coproduct comparison `c : ⨁ L(M_i) ≅ L(⨁ M_i)` is characterized by
`ι_i ≫ c.hom = L(ι_i)`. Its naturality follows by precomposing with each inclusion.
The needed coproducts exist by [def-pc-tensor-complex-sheaves].

2. The generator action of [def-weil-pbc-etale-sum-extension] is
`(s,m) ↦ (s,a(m))`; it preserves sums, zero and negatives, hence `L` is additive.
`R` is additive by [prop-weil-pbc-inverse-image-modules-exact]. Degreewise application
therefore preserves the square-zero and chain-map equations of
[def-pc-cochain-complex-modules].

3. Use [lem-pur-etale-sheaf-projection-map] (Stacks Tag 0GKF) on `P^p,H^q`.
Its component `a_pq : L(P^p) ⊗ H^q ≅ L(P^p ⊗ R(H^q))` is the inverse of the
upstream `etaleLowerShriekTensorIso`. Set `Ψ^n = (⨁ a_pq) ≫ c` for `p+q=n`.
Its inverse is `c.inv ≫ (⨁ a_pq.inv)`. This fixes every inclusion by
`ι_pq ≫ Ψ^n = a_pq.hom ≫ L(ι_pq)` and fixes the presheaf generator
`(s,m) ⊗ h ↦ (s,m ⊗ s^*h)`, without permuting tensor factors.

4. Naturality of the sheaf projection for `d_P` and `d_H` makes the two squares
`(L(d_P) ⊗ 1) ≫ a_(p+1,q) = a_pq ≫ L(d_P ⊗ 1)` and
`(1 ⊗ d_H) ≫ a_(p,q+1) = a_pq ≫ L(1 ⊗ R(d_H))` commute.
The second carries the same factor `(-1)^p` on both sides by
[def-pc-tensor-complex-sheaves], Stacks Tag 012Z. Additivity and coproduct extensionality
give the chain-map equation. The degreewise inverses then form a chain map too.

5. For arbitrary `f:P⟶P'` and `g:H⟶H'`, sheaf naturality gives
`(L(f^p) ⊗ g^q) ≫ a'_pq = a_pq ≫ L(f^p ⊗ R(g^q))`.
Sum over `p+q=n` and use naturality of `c` from step 1. This is naturality of
`Ψ` in both complexes, with the maps of [def-pc-tensor-complex-sheaves].

6. For a homotopy `h` in the first variable as in [def-pur-kinjective-complex],
use Mathlib's `mapBifunctorMapHomotopy₁`: its summand map is `L(h^p) ⊗ 1` on
the left and `L(h^p ⊗ 1)` on the right. In `dS+Sd`, mixed terms have coefficients
`(-1)^(p-1)` and `(-1)^p`, so cancel. The remaining terms are the image of
`f-f' = dh+hd`. Sheaf naturality for the degree-minus-one morphism `h^p`, then
the summand inclusions of step 3, makes `Ψ` intertwine these very homotopy maps.

7. In the second variable use `mapBifunctorMapHomotopy₂` on `k`.
The summand map is `(-1)^p (1 ⊗ k^q)` (and its corresponding images under `R,L`).
The mixed coefficients are `(-1)^p` and `(-1)^(p+1)` and cancel; the two remaining
coefficients are `(-1)^(2p)=1`. Sheaf naturality for `k^q` gives the second
intertwining equation. Each homotopy has one target summand per source summand and
the differential has two, so no boundedness is required. The canonical bifunctors
factor through homotopies by `bifunctorMapHomotopyCategory`. Quotient the naturality
equation of step 5 to get the natural isomorphism `η`, whose component is exactly
`Q.map (Ψ P H).hom`. The inverse also descends, as it is already an inverse chain map.
These calculations use [def-pur-kinjective-complex], [def-pc-tensor-complex-sheaves],
and [lem-pur-etale-sheaf-projection-map]; no flatness or constructibility is used.
-/
theorem etale_sum_tensor_totalization
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (u : U ⟶ X) (hu : Etale u)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] :
    ∃ Ψ : EtaleSumTensorComparison A u hu,
      EtaleSumPreservesDirectSums A u hu ∧ EtaleSumTensorClauses A u hu Ψ := by
  let L := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu
  let R := Etale.upperStar (ModuleCat.{u + 1} A) u
  let F := curriedTensor (EtaleModuleSheaf U A)
  let G := curriedTensor (EtaleModuleSheaf X A)
  have : PreservesColimitsOfSize.{0, 0} L :=
    (Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u hu).leftAdjoint_preservesColimits
  let a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)) :=
    fun M N ↦ (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M N).symm
  have ha : ∀ {M M' : EtaleModuleSheaf U A} {N N' : EtaleModuleSheaf X A}
      (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)) := by
    intro M M' N N' f g
    change (L.map f ⊗ₘ g) ≫
      (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M' N').inv =
      (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M N).inv ≫
        L.map (f ⊗ₘ R.map g)
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Etale.etaleLowerShriekTensorIso_hom_naturality
      (ModuleCat.{u + 1} A) hu f g).symm
  let Ψ := totalTensorIso F G L R a ha
  have hn := totalTensorIso_normalization F G L R a ha
  have hnat := totalTensor_naturality F G L R Ψ (fun M N ↦ (a M N).hom) ha hn
  have hh := totalTensor_homotopies F G L R Ψ (fun M N ↦ (a M N).hom) ha hn
  refine ⟨Ψ, ?_, hn, hnat, hh.1, hh.2, totalTensor_descent F G L R Ψ hnat⟩
  letI : PreservesColimitsOfSize.{u + 1, u + 1}
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu) :=
    (Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u hu).leftAdjoint_preservesColimits
  intro β
  infer_instance

end AlgebraicGeometry