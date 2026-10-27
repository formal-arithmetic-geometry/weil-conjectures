/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NH, J4, S2
-/
module

public import Sheaf.Paper.FiniteCounitRestrictionTowers
public import Sheaf.Paper.PodCompletionReindexModels
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.CategoryTheory.CommSq

/-! # Models for semilinear finite-fibre restriction diagrams

Source: blueprint, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
lem-zl-finite-pushforward.proof.md, finite stalk formula and Frobenius permutation
(blueprint: def-zl-finite-restriction-diagram-models).

The maps compared here are the published counit mates on the ringed sequence site.
Positive coefficient exponent n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence SheafOfModules.monoidalCategory

universe u d e d' e'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.FiniteRestrictionNaturality
open FiniteCounitTowers

/-- Canonical size witness at the actual coefficient universe.
Source: blueprint small pro-etale site convention
(blueprint: def-zl-finite-restriction-diagram-models). -/
instance (priority := 6000) canonicalSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} W.ProEt

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Composition comparison for two equal paths, with the published normalization.
Source: Stacks 03D8; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def paths {A B C D : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ D)
    (i : A ⟶ C) (j : C ⟶ D) (eq : g ≫ h = i ≫ j) :
    pull l E h ⋙ pull l E g ≅ pull l E j ⋙ pull l E i :=
  (integralComparisonSequenceComposition l E g h).symm ≪≫
    eqToIso (congrArg (pull l E) eq) ≪≫ integralComparisonSequenceComposition l E i j

/-- Direct-image transport is the counit mate of the equal-path comparison.
Source: Stacks 0959, 07A7; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def pushSquare {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (u : X ⟶ X') (w : Y ⟶ Y') (eq : u ≫ f' = f ≫ w) :
    push l E f' ⋙ pull l E w ⟶ pull l E u ⋙ push l E f :=
  (mateEquiv (adj l E f') (adj l E f)
    (TwoSquare.mk _ _ _ _ (paths l E f w u f' eq.symm).hom)).natTrans

/-- Geometric transport, allowing an arbitrary automorphism of k, with no k₀ condition.
Source: blueprint finite-stalk permutation sentence, explicit fibre-product calculation
(blueprint: def-zl-finite-restriction-diagram-models). -/
structure Diagram (k : Type u) [Field k] where
  X : Scheme.{u}
  Y : Scheme.{u}
  X' : Scheme.{u}
  Y' : Scheme.{u}
  aX : X ⟶ Spec (.of k)
  aY : Y ⟶ Spec (.of k)
  aX' : X' ⟶ Spec (.of k)
  aY' : Y' ⟶ Spec (.of k)
  f : X ⟶ Y
  f' : X' ⟶ Y'
  over_eq : f ≫ aY = aX
  over_eq' : f' ≫ aY' = aX'
  sigma : k ≃+* k
  u : X ≅ X'
  w : Y ≅ Y'
  semilinearX : u.hom ≫ aX' = aX ≫ (Scheme.Spec.mapIso sigma.toCommRingCatIso.op).hom
  semilinearY : w.hom ≫ aY' = aY ≫ (Scheme.Spec.mapIso sigma.toCommRingCatIso.op).hom
  commutes : u.hom ≫ f' = f ≫ w.hom
  y : Spec (.of k) ⟶ Y

variable {k : Type u} [Field k] (G : Diagram k)

/-- The automorphism of Spec k induced by the given field automorphism.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def c : Spec (.of k) ≅ Spec (.of k) := Scheme.Spec.mapIso G.sigma.toCommRingCatIso.op

/-- The transported point c⁻¹ y w, with the order written in categorical convention.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def y' : Spec (.of k) ⟶ G.Y' := (c G).inv ≫ G.y ≫ G.w.hom

/-- Equalities determining the geometric transport and its inverse.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models).
Proof: cancel c with its inverse and use the commuting diagram. The fibre product
lift has projections v u and h c; the reverse lift
has projections v' u⁻¹ and h' c⁻¹. Their composites have identity projections. -/
theorem geometry :
    (c G).hom ≫ y' G = G.y ≫ G.w.hom ∧
    ∃! t : Limits.pullback G.f G.y ≅ Limits.pullback G.f' (y' G),
      t.hom ≫ pullback.fst G.f' (y' G) = pullback.fst G.f G.y ≫ G.u.hom ∧
      t.hom ≫ pullback.snd G.f' (y' G) = pullback.snd G.f G.y ≫ (c G).hom := by
  have hc : (c G).hom ≫ y' G = G.y ≫ G.w.hom := by
    simp [y']
  refine ⟨hc, ?_⟩
  let m := pullback.map G.f G.y G.f' (y' G) G.u.hom (c G).hom G.w.hom
    G.commutes.symm hc.symm
  refine ⟨asIso m, ?_, ?_⟩
  · exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  · intro t ht
    apply Iso.ext
    apply pullback.hom_ext
    · exact ht.1.trans (pullback.lift_fst _ _ _).symm
    · exact ht.2.trans (pullback.lift_snd _ _ _).symm

/-- The canonical fibre-product transport, uniquely determined by both projections.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def fibreIso : Limits.pullback G.f G.y ≅ Limits.pullback G.f' (y' G) :=
  (geometry G).2.choose

/-- Transport of geometric lifts is c⁻¹ x u, with inverse c x' u⁻¹.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models).
Proof: the diagram equality gives f' u x c⁻¹ = w f x c⁻¹ = y'.
The inverse formula cancels u and c; subtype equality reduces to this cancellation. -/
theorem points_existsUnique :
    ∃! e : Points G.f G.y ≃ Points G.f' (y' G),
      ∀ x, (e x).val = (c G).inv ≫ x.val ≫ G.u.hom := by
  let e : Points G.f G.y ≃ Points G.f' (y' G) :=
    { toFun := fun x ↦ ⟨(c G).inv ≫ x.val ≫ G.u.hom, by
        rw [Category.assoc, Category.assoc, G.commutes, ← Category.assoc x.val,
          x.property]
        rfl⟩
      invFun := fun x ↦ ⟨(c G).hom ≫ x.val ≫ G.u.inv, by
        apply (cancel_mono G.w.hom).1
        simp only [Category.assoc, ← G.commutes, Iso.inv_hom_id_assoc, x.property]
        exact (geometry G).1⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        simp [Category.assoc]
      right_inv := fun x ↦ by
        apply Subtype.ext
        simp [Category.assoc] }
  refine ⟨e, (fun _ ↦ rfl), ?_⟩
  intro e' he'
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact he' x

/-- The uniquely normalized permutation of summands.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def points : Points G.f G.y ≃ Points G.f' (y' G) := (points_existsUnique G).choose

/-- The equal point paths and equality of the lifted sections, including nonreduced fibres.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models).
Proof: use the formula defining points and cancel c; compare both projections of
the lifted sections, using geometry and the pullback universal property. -/
theorem point_paths (x : Points G.f G.y) :
    (c G).hom ≫ (points G x).val = x.val ≫ G.u.hom ∧
      lift G.f G.y x ≫ (fibreIso G).hom =
        (c G).hom ≫ lift G.f' (y' G) (points G x) := by
  have hp : (points G x).val = (c G).inv ≫ x.val ≫ G.u.hom :=
    (points_existsUnique G).choose_spec.1 x
  have hc : (c G).hom ≫ (points G x).val = x.val ≫ G.u.hom := by
    simp [hp]
  refine ⟨hc, ?_⟩
  have hf := (geometry G).2.choose_spec.1.1
  have hs := (geometry G).2.choose_spec.1.2
  change (fibreIso G).hom ≫ pullback.fst G.f' (y' G) = _ at hf
  change (fibreIso G).hom ≫ pullback.snd G.f' (y' G) = _ at hs
  apply pullback.hom_ext
  · simp only [Category.assoc, hf, lift, pullback.lift_fst, pullback.lift_fst_assoc]
    exact hc.symm
  · simp only [Category.assoc, hs, lift, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id, Category.id_comp]

/-- Source comparison T_B, from pullback composition and the specified direct-image mate.
Source: Stacks 0959; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def source : push l E G.f' ⋙ pull l E (y' G) ⋙ pull l E (c G).hom ⟶
    pull l E G.u.hom ⋙ push l E G.f ⋙ pull l E G.y :=
  Functor.whiskerLeft (push l E G.f')
    (paths l E (c G).hom (y' G) G.y G.w.hom (geometry G).1).hom ≫
  (Functor.associator (push l E G.f') (pull l E G.w.hom) (pull l E G.y)).inv ≫
  Functor.whiskerRight (pushSquare l E G.f G.f' G.u.hom G.w.hom G.commutes)
    (pull l E G.y) ≫
  (Functor.associator (pull l E G.u.hom) (push l E G.f) (pull l E G.y)).hom

/-- Middle comparison T_C, from the fibre transport and the h-direct-image mate.
Source: Stacks 0959, 03QP; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def middle : pull l E (pullback.fst G.f' (y' G)) ⋙
      push l E (pullback.snd G.f' (y' G)) ⋙ pull l E (c G).hom ⟶
    pull l E G.u.hom ⋙ pull l E (pullback.fst G.f G.y) ⋙
      push l E (pullback.snd G.f G.y) :=
  Functor.whiskerLeft (pull l E (pullback.fst G.f' (y' G)))
    (pushSquare l E (pullback.snd G.f G.y) (pullback.snd G.f' (y' G))
      (fibreIso G).hom (c G).hom (geometry G).2.choose_spec.1.2) ≫
  (Functor.associator (pull l E (pullback.fst G.f' (y' G)))
    (pull l E (fibreIso G).hom) (push l E (pullback.snd G.f G.y))).inv ≫
  Functor.whiskerRight
    (paths l E (fibreIso G).hom (pullback.fst G.f' (y' G))
      (pullback.fst G.f G.y) G.u.hom (geometry G).2.choose_spec.1.1).hom
    (push l E (pullback.snd G.f G.y)) ≫
  (Functor.associator (pull l E G.u.hom) (pull l E (pullback.fst G.f G.y))
    (push l E (pullback.snd G.f G.y))).hom

/-- Stalk transport T_x is the specified pullback-composition comparison.
Source: Stacks 03QP; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def stalk (x : Points G.f G.y) :
    pull l E (points G x).val ⋙ pull l E (c G).hom ≅
      pull l E G.u.hom ⋙ pull l E x.val :=
  paths l E (c G).hom (points G x).val x.val G.u.hom (point_paths G x).1

private theorem productWhisker_existsUnique
    {A B C : Type*} [Category A] [Category B] [Category C]
    {ι : Type*} [HasLimitsOfShape (Discrete ι) C]
    (U : A ⥤ B) (H : ι → B ⥤ C) (V : A ⥤ C) (α : ∀ i, V ⟶ U ⋙ H i) :
    ∃! η : V ⟶ U ⋙ ∏ᶜ H,
      ∀ (M : A) (i : ι), η.app M ≫ (Pi.π H i).app (U.obj M) = (α i).app M := by
  let W := (Functor.whiskeringLeft A B C).obj U
  let L := isLimitOfPreserves W (limit.isLimit (Discrete.functor H))
  let cone : Cone (Discrete.functor H ⋙ W) :=
    { pt := V
      π := Discrete.natTrans (fun i ↦ α i.as) }
  refine ⟨L.lift cone, ?_, ?_⟩
  · intro M i
    exact congrArg (fun η ↦ η.app M) (L.fac cone ⟨i⟩)
  · intro η hη
    apply L.hom_ext
    intro i
    apply NatTrans.ext
    funext M
    exact (hη M i.as).trans (congrArg (fun η ↦ η.app M) (L.fac cone i)).symm

/-- The sum comparison is fixed by its permutation and these stalk components.
Source: Stacks 03QP; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models).
Proof: pullback along c is an equivalence and preserves products. Reindex the
product by points. The product projections uniquely determine the displayed map,
its inverse, and its naturality. For an empty fibre this is the unique zero map. -/
theorem sum_existsUnique :
    ∃! η : pointSum l E G.f' (y' G) ⋙ pull l E (c G).hom ⟶
        pull l E G.u.hom ⋙ pointSum l E G.f G.y,
      ∀ (M : coefficientSequenceModules l E G.X') (x : Points G.f G.y),
        η.app M ≫ (Pi.π (fun z : Points G.f G.y ↦ pull l E z.val) x).app
            ((pull l E G.u.hom).obj M) =
          (pull l E (c G).hom).map
            ((Pi.π (fun z : Points G.f' (y' G) ↦ pull l E z.val) (points G x)).app M) ≫
              (stalk l E G x).hom.app M := by
  exact productWhisker_existsUnique (pull l E G.u.hom)
    (fun x : Points G.f G.y ↦ pull l E x.val)
    (pointSum l E G.f' (y' G) ⋙ pull l E (c G).hom)
    (fun x ↦ Functor.whiskerRight
      (Pi.π (fun z : Points G.f' (y' G) ↦ pull l E z.val) (points G x))
        (pull l E (c G).hom) ≫ (stalk l E G x).hom)

/-- The canonical sum transport, with no additional scalar action on coefficients.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def sum : pointSum l E G.f' (y' G) ⋙ pull l E (c G).hom ⟶
    pull l E G.u.hom ⋙ pointSum l E G.f G.y := (sum_existsUnique l E G).choose

/-- The three comparisons on entire complexes of strict quotient systems.
Source: Stacks 0941; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
abbrev sourceComplex := NatTrans.mapHomologicalComplex (source l E G) (.up ℤ)

/-- The middle comparison on entire complexes of strict quotient systems.
Source: Stacks 0941; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
abbrev middleComplex := NatTrans.mapHomologicalComplex (middle l E G) (.up ℤ)

/-- The sum comparison on entire complexes of strict quotient systems.
Source: Stacks 0941; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
abbrev sumComplex := NatTrans.mapHomologicalComplex (sum l E G) (.up ℤ)



/-- A square retains its actual four arrows, before taking any realization.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
structure Square (A : Type d) [Category.{e} A] where
  topLeft : A
  topRight : A
  bottomLeft : A
  bottomRight : A
  top : topLeft ⟶ topRight
  bottom : bottomLeft ⟶ bottomRight
  left : topLeft ⟶ bottomLeft
  right : topRight ⟶ bottomRight

/-- Commutativity of the entire square, rather than only its separate evaluations.
Source: blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def Square.Commutes {A : Type d} [Category.{e} A] (S : Square A) : Prop :=
  CommSq S.top S.left S.right S.bottom

/-- Apply a specified functor to the four actual arrows.
Source: blueprint finite-stalk permutation sentence, completion and rationalization clauses
(blueprint: def-zl-finite-restriction-diagram-models). -/
def Square.image {A : Type d} [Category.{e} A] {A' : Type d'} [Category.{e'} A']
    (S : Square A) (F : A ⥤ A') : Square A' where
  topLeft := F.obj S.topLeft
  topRight := F.obj S.topRight
  bottomLeft := F.obj S.bottomLeft
  bottomRight := F.obj S.bottomRight
  top := F.map S.top
  bottom := F.map S.bottom
  left := F.map S.left
  right := F.map S.right

/-- All four vertices lie in the indicated full subcategory.
Source: blueprint finite-stalk permutation sentence, integral constructibility clause
(blueprint: def-zl-finite-restriction-diagram-models). -/
def Square.Vertices {A : Type d} [Category.{e} A] (S : Square A)
    (P : ObjectProperty A) : Prop :=
  P S.topLeft ∧ P S.topRight ∧ P S.bottomLeft ∧ P S.bottomRight

/-- Restrict the actual square to the full subcategory, without altering its arrows.
Source: blueprint finite-stalk permutation sentence, raw rationalization clause
(blueprint: def-zl-finite-restriction-diagram-models). -/
def Square.restrict {A : Type d} [Category.{e} A] (S : Square A)
    (P : ObjectProperty A) (h : S.Vertices P) : Square P.FullSubcategory where
  topLeft := ⟨S.topLeft, h.1⟩
  topRight := ⟨S.topRight, h.2.1⟩
  bottomLeft := ⟨S.bottomLeft, h.2.2.1⟩
  bottomRight := ⟨S.bottomRight, h.2.2.2⟩
  top := ObjectProperty.homMk S.top
  bottom := ObjectProperty.homMk S.bottom
  left := ObjectProperty.homMk S.left
  right := ObjectProperty.homMk S.right

/-- The actual exchange square on a strict quotient representative on X'.
Source: Stacks 0959; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def exchangeSquare (T : CochainComplex (coefficientSequenceModules l E G.X') ℤ) :
    Square (CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ) where
  topLeft := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).obj
    ((B l E G.f' (y' G)).obj T)
  topRight := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).obj
    ((C l E G.f' (y' G)).obj T)
  bottomLeft := (B l E G.f G.y).obj
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  bottomRight := (C l E G.f G.y).obj
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  top := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).map
    ((b l E G.f' (y' G)).app T)
  bottom := (b l E G.f G.y).app
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  left := (sourceComplex l E G).app T
  right := (middleComplex l E G).app T

/-- The actual restriction square, whose right side permutes exactly the geometric lifts.
Source: Stacks 03QP; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def restrictionSquare (T : CochainComplex (coefficientSequenceModules l E G.X') ℤ) :
    Square (CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ) where
  topLeft := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).obj
    ((C l E G.f' (y' G)).obj T)
  topRight := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).obj
    ((D l E G.f' (y' G)).obj T)
  bottomLeft := (C l E G.f G.y).obj
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  bottomRight := (D l E G.f G.y).obj
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  top := ((pull l E (c G).hom).mapHomologicalComplex (.up ℤ)).map
    ((r l E G.f' (y' G)).app T)
  bottom := (r l E G.f G.y).app
    (((pull l E G.u.hom).mapHomologicalComplex (.up ℤ)).obj T)
  left := (middleComplex l E G).app T
  right := (sumComplex l E G).app T

/-- The whole strict Roos square, retaining products, transitions and both cone coordinates.
Source: Stacks 0941; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def roos (S : Square
    (CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ)) :=
  ((S.image (restricted l E (Spec (.of k)))).image
    HomologicalComplex.complexOfFunctorsToFunctorToComplex).image integralOperationsRoosFunctor

/-- The total derived inverse limit of the entire localized system square.
Source: Stacks 0941; blueprint finite-stalk permutation sentence
(blueprint: def-zl-finite-restriction-diagram-models). -/
def completed (S : Square
    (CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ)) :=
  (S.image DerivedCategory.Q).image (coefficientSequenceLimit.{u, u} l E (Spec (.of k)))

end WeilConjectures.FiniteRestrictionNaturality
