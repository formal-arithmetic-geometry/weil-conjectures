/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
-- The elements equivalence must unfold in the proof of overFiberIso.
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Over
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantStalk

/-! # Finite local trivializations of finite étale representable sheaves

Source: Stacks Project, Tag 03RV, implication (2) to (1), and Tag 04HN.
(blueprint: lem-weil-pbc-finite-etale-yoneda-local-trivializations)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Replace each summand by the base and identify the resulting colimit over the base.
open CategoryTheory.Limits Opposite in
private theorem splitCoproductIso {T P U : Scheme.{u}}
    (π : P ⟶ T) (g : U ⟶ T) {J : Type u} (V : J → Scheme.{u})
    (ι : ∀ j, V j ⟶ pullback π g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback π g) ι)))
    (e : ∀ j, V j ≅ U) (he : ∀ j, (e j).hom = ι j ≫ pullback.snd π g) :
    ∃ q : (∐ fun _ : J ↦ U) ≅ pullback π g,
      q.hom ≫ pullback.snd π g = Sigma.desc (fun _ : J ↦ 𝟙 U) := by
  have : IsIso (Sigma.desc ι) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ ι)).mp hc
  let q := (Sigma.mapIso e).symm ≪≫ asIso (Sigma.desc ι)
  refine ⟨q, ?_⟩
  apply Sigma.hom_ext
  intro j
  dsimp [q]
  simp only [Category.assoc, Sigma.ι_mapIso_inv_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [← he j, Iso.inv_hom_id]

-- A section over T lifts uniquely to the pullback; compose with the splitting.
open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def splitPresheafIso {T P : Scheme.{u}}
    (π : P ⟶ T) [Etale π] (U : T.Etale) (J : Type u)
    (q : (∐ fun _ : J ↦ U.left) ≅ pullback π U.hom)
    (hq : q.hom ≫ pullback.snd π U.hom = Sigma.desc (fun _ : J ↦ 𝟙 U.left)) :
    ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
      (((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over U)).obj ≅
        constantSetCoproductPresheaf U.left J := by
  refine NatIso.ofComponents (fun W ↦ ?_) ?_
  · refine Equiv.toIso
      { toFun := fun a ↦ ⟨Over.homMk
          (pullback.lift a.down.left W.unop.hom (MorphismProperty.Over.w a.down) ≫ q.inv)
          (by
            change (pullback.lift a.down.left W.unop.hom _ ≫ q.inv) ≫
              Sigma.desc (fun _ : J ↦ 𝟙 U.left) = W.unop.hom
            rw [Category.assoc, ← hq, Iso.inv_hom_id_assoc, pullback.lift_snd])⟩
        invFun := fun b ↦ ⟨MorphismProperty.Over.homMk
          (b.down.left ≫ q.hom ≫ pullback.fst π U.hom) (by
            change b.down.left ≫ q.hom ≫ pullback.fst π U.hom ≫ π =
              W.unop.hom ≫ U.hom
            simpa [pullback.condition, reassoc_of% hq] using
              congrArg (fun f ↦ f ≫ U.hom) (Over.w b.down))⟩
        left_inv := by
          intro a
          apply ULift.ext
          apply MorphismProperty.Over.Hom.ext
          change (pullback.lift a.down.left W.unop.hom _ ≫ q.inv) ≫
            q.hom ≫ pullback.fst π U.hom = a.down.left
          rw [Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_fst]
        right_inv := by
          intro b
          apply ULift.ext
          apply Over.OverMorphism.ext
          apply (cancel_mono q.hom).1
          change (pullback.lift (b.down.left ≫ q.hom ≫ pullback.fst π U.hom)
            W.unop.hom _ ≫ q.inv) ≫ q.hom = b.down.left ≫ q.hom
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          apply pullback.hom_ext
          · simp only [pullback.lift_fst, Category.assoc]
          · rw [pullback.lift_snd, Category.assoc, hq]
            exact (Over.w b.down).symm }
  · intro W V f
    ext a
    apply ULift.ext
    apply Over.OverMorphism.ext
    change pullback.lift (f.unop.left ≫ a.down.left) V.unop.hom _ ≫ q.inv =
      f.unop.left ≫ pullback.lift a.down.left W.unop.hom _ ≫ q.inv
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
      pullback.lift_snd, MorphismProperty.Over.w]

-- Transport the coproduct/constant comparison back through the equivalence of sites.
open CategoryTheory.Limits Opposite in
private theorem localConstantOfSplit {T P : Scheme.{u}} (π : P ⟶ T) [Etale π]
    (U : T.Etale) (J : Type u)
    (q : (∐ fun _ : J ↦ U.left) ≅ pullback π U.hom)
    (hq : q.hom ≫ pullback.snd π U.hom = Sigma.desc (fun _ : J ↦ 𝟙 U.left)) :
    Nonempty ((((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over U) ≅
      (constantSheaf (T.smallEtaleTopology.over U) (Type (u + 1))).obj
        (ULift.{u + 1, u} J)) := by
  obtain ⟨hH, _, _, φ, _, hIso, _⟩ := constantSheaf_sets_representable U.left J
  let E := Etale.overSheafEquiv U (Type (u + 1))
  let F := ((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over U
  let H : Sheaf U.left.smallEtaleTopology (Type (u + 1)) :=
    ⟨constantSetCoproductPresheaf U.left J, hH⟩
  let e : E.functor.obj F ≅ H :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (splitPresheafIso π U J q hq)
  let : IsIso φ := hIso
  let e' := e ≪≫ (asIso φ).symm ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (Type (u + 1))
      Over.mkIdTerminal).symm.app (ULift.{u + 1, u} J)
  exact ⟨E.fullyFaithfulFunctor.preimageIso e'⟩

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

-- Pointed objects over U form an over category of the cofiltered neighbourhood category.
-- Its forgetful functor is initial, so restriction preserves the stalk colimit.
open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def overFiberIso {Y : Scheme.{u}}
    (Φ : Y.smallEtaleTopology.Point.{u}) (U : Y.Etale) (x : Φ.fiber.obj U)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    (Φ.over x).sheafFiber.obj (F.over U) ≅ Φ.sheafFiber.obj F := by
  let E := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x
  let G := E.functor ⋙ Over.forget (Φ.fiber.elementsMk U x)
  have : G.Initial := inferInstance
  exact Functor.Final.colimitIso G.op ((CategoryOfElements.π Φ.fiber).op ⋙ F.obj)

-- Work with separably closed fields, including those that are not algebraically closed.
open CategoryTheory.Limits Opposite in
private theorem finiteSheaf_of_local_models {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty (F.over (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) : IsFiniteSheaf F := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hF
  constructor
  intro Ω _ _ s
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
  let U := 𝒰.etalePrecoverageToEtale i
  let Φ := pointSmallEtale s
  let a : Φ.fiber.obj U := Over.homMk t ht
  obtain ⟨S, hS, ⟨e⟩⟩ := h𝒰 i
  let Ψ := (Φ.over a).ulift.{u + 1}
  let e' : Φ.sheafFiber.obj F ≅ S :=
    (overFiberIso Φ U a F).symm ≪≫
      ((Φ.over a).uliftSheafFiberIso (Type (u + 1))).symm.app (F.over U) ≪≫
      Ψ.sheafFiber.mapIso e ≪≫ Ψ.sheafFiberConstantSheafIso S
  apply (ConcreteCategory.isFinitelyGenerated_iff_finite _).2
  exact Finite.of_equiv S e'.toEquiv.symm

/-- The canonical sheaf of sections of a finite étale morphism has finite constant
local models, and its geometric stalks are finite.

Source: Stacks Project, Tag 03RV, implication (2) to (1); Tag 04HN gives the splitting.
(blueprint: lem-weil-pbc-finite-etale-yoneda-local-trivializations)

Proof: For each point of T, split P into finitely many copies of an étale neighbourhood
by Tag 04HN. These neighbourhoods form an étale cover. On the site localized at each
member, the sheaf of sections of this disjoint union is the constant sheaf with value
its finite set of sheets: a map into a disjoint union chooses a sheet on each open and
closed piece, so the sections are locally constant sheet-valued functions. This
identification commutes with restriction and gives the displayed sheaf isomorphisms.
At any separably closed geometric point, lift the point to a member of the cover.
Étale localization identifies the stalk with the stalk of the corresponding constant
sheaf; that stalk is its finite value. Thus all geometric stalks are finite, equivalently
finitely generated in the category of sets, which is IsFiniteSheaf. Empty fibres use
the empty set of sheets; the empty scheme uses the empty cover. -/
theorem finiteEtale_yoneda_local_trivializations
    (T P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [Etale π] :
    (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty (((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over
            (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) ∧
    IsFiniteSheaf ((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)) := by
  classical
  choose U g u hg hu J V ι hJ hc _ e he using finite_etale_etale_local_split π
  let 𝒰 : Cover.{u} etalePrecoverage T :=
    Cover.mkOfCovers T U g (fun x ↦ ⟨x, u x, hu x⟩) hg
  have hloc : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty (((T.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)).over
            (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S) := by
    refine ⟨𝒰, fun x ↦ ?_⟩
    have : Finite (J x) := hJ x
    obtain ⟨q, hq⟩ := splitCoproductIso π (g x) (V x) (ι x) (hc x) (e x) (he x)
    exact ⟨ULift.{u + 1, u} (J x), inferInstance,
      localConstantOfSplit π (𝒰.etalePrecoverageToEtale x) (J x) q hq⟩
  exact ⟨hloc, finiteSheaf_of_local_models _ hloc⟩

end AlgebraicGeometry.Scheme
