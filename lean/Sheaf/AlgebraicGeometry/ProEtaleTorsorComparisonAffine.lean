/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections

/-! # Affine comparison for torsors under classical group sheaves

Source: current blueprint, sec-proetale-coefficients/sk-lem-pe-torsor-comparison,
`sk-lem-pe-torsor-comparison-affine.md`; Stacks Project, Tag 099X
(blueprint: det-pe-torsor-comparison-affine).

Group sheaves are Mathlib internal group objects in sheaves of sets. Actions and their
laws are stated as sheaf morphisms, and the torsor condition uses the displayed
isomorphism and epimorphism of the source. No commutativity is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison inverse image on the original small sites, as publicly
retained by the recorded comparison module. Its data is left Kan extension followed by
sheafification, not an arbitrary left adjoint.
Source: Stacks Tags 099R and 099X (blueprint: det-pe-torsor-comparison-affine). -/
abbrev torsorComparisonPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical product-preserving structure, used to pull back group multiplication,
unit, inverse and actions. Its multiplication comparison is the inverse of the canonical
product comparison.
Source: Stacks Tags 099R and 099X (blueprint: det-pe-torsor-comparison-affine). -/
instance torsorComparisonPullback_monoidal (X : Scheme.{u}) :
    (torsorComparisonPullback X).Monoidal :=
  haveI := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  Functor.Monoidal.ofChosenFiniteProducts (torsorComparisonPullback X)

/-- Reflect an action along a fully faithful product-preserving functor.
The action is the preimage of the cotensorator followed by the given action.
Faithfulness, tensorator naturality and its coherence reflect the two action laws.
Source: Stacks Tag 099X, descent of the action; Mathlib monoidal-functor coherence.
(blueprint: det-pe-torsor-comparison-affine). -/
private theorem reflect_action
    {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
    (G : Grp C) (P : C)
    (b : F.obj G.X ⊗ F.obj P ⟶ F.obj P)
    (hb_one : (MonObj.one (X := F.obj G.X) ▷ F.obj P) ≫ b = (λ_ (F.obj P)).hom)
    (hb_mul : (MonObj.mul (X := F.obj G.X) ▷ F.obj P) ≫ b =
      (α_ _ _ _).hom ≫ (F.obj G.X ◁ b) ≫ b) :
    ∃ a₀ : G.X ⊗ P ⟶ P,
      (MonObj.one (X := G.X) ▷ P) ≫ a₀ = (λ_ P).hom ∧
      (MonObj.mul (X := G.X) ▷ P) ≫ a₀ =
        (α_ _ _ _).hom ≫ (G.X ◁ a₀) ≫ a₀ ∧
      Functor.LaxMonoidal.μ F G.X P ≫ F.map a₀ = b := by
  let a₀ := F.preimage (Functor.OplaxMonoidal.δ F G.X P ≫ b)
  have ha : F.map a₀ = Functor.OplaxMonoidal.δ F G.X P ≫ b := F.map_preimage _
  have hμ : Functor.LaxMonoidal.μ F G.X P ≫ F.map a₀ = b := by
    rw [ha, Functor.Monoidal.μ_δ_assoc]
  refine ⟨a₀, ?_, ?_, hμ⟩
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε F ▷ F.obj P ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) P)).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc, hμ]
    rw [← comp_whiskerRight_assoc]
    change (MonObj.one (X := F.obj G.X) ▷ F.obj P) ≫ b = _
    rw [hb_one, Functor.LaxMonoidal.left_unitality]
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F G.X G.X ▷ F.obj P ≫
      Functor.LaxMonoidal.μ F (G.X ⊗ G.X) P)).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc, hμ]
    rw [← comp_whiskerRight_assoc]
    change (MonObj.mul (X := F.obj G.X) ▷ F.obj P) ≫ b = _
    rw [hb_mul]
    rw [Functor.LaxMonoidal.associativity_assoc]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← whiskerLeft_comp_assoc, hμ]

/-- Reflect the torsor axioms together with the action. The pair map is carried
by the product comparisons to the given invertible pair map. Faithfulness reflects
its invertibility and the terminal-map epimorphism.
Source: Stacks Tag 099X, descent of torsor structure.
(blueprint: det-pe-torsor-comparison-affine). -/
private theorem reflect_torsor
    {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
    (G : Grp C) (P : C) (b : F.obj G.X ⊗ F.obj P ⟶ F.obj P)
    (hb_one : (MonObj.one (X := F.obj G.X) ▷ F.obj P) ≫ b = (λ_ (F.obj P)).hom)
    (hb_mul : (MonObj.mul (X := F.obj G.X) ▷ F.obj P) ≫ b =
      (α_ _ _ _).hom ≫ (F.obj G.X ◁ b) ≫ b)
    (hb_iso : IsIso (lift b (snd (F.obj G.X) (F.obj P))))
    (hb_epi : Epi (toUnit (F.obj P))) :
    ∃ a₀ : G.X ⊗ P ⟶ P,
      (MonObj.one (X := G.X) ▷ P) ≫ a₀ = (λ_ P).hom ∧
      (MonObj.mul (X := G.X) ▷ P) ≫ a₀ =
        (α_ _ _ _).hom ≫ (G.X ◁ a₀) ≫ a₀ ∧
      IsIso (lift a₀ (snd G.X P)) ∧ Epi (toUnit P) ∧
      Functor.LaxMonoidal.μ F G.X P ≫ F.map a₀ = b := by
  obtain ⟨a₀, h₁, h₂, ha⟩ := reflect_action F G P b hb_one hb_mul
  refine ⟨a₀, h₁, h₂, ?_, ?_, ha⟩
  · have heq : Functor.LaxMonoidal.μ F G.X P ≫ F.map (lift a₀ (snd G.X P)) ≫
        Functor.OplaxMonoidal.δ F P P = lift b (snd (F.obj G.X) (F.obj P)) := by
      ext <;> simp [ha]
    have : IsIso (Functor.LaxMonoidal.μ F G.X P ≫ F.map (lift a₀ (snd G.X P)) ≫
        Functor.OplaxMonoidal.δ F P P) := heq ▸ hb_iso
    have : IsIso (F.map (lift a₀ (snd G.X P)) ≫ Functor.OplaxMonoidal.δ F P P) :=
      IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F G.X P) _
    have : IsIso (F.map (lift a₀ (snd G.X P))) :=
      IsIso.of_isIso_comp_right _ (Functor.OplaxMonoidal.δ F P P)
    exact isIso_of_reflects_iso _ F
  · have heq : toUnit (F.obj P) ≫ Functor.LaxMonoidal.ε F = F.map (toUnit P) :=
      Functor.Monoidal.toUnit_ε F P
    have : Epi (F.map (toUnit P)) := heq ▸ inferInstance
    exact F.epi_of_epi_map inferInstance

/-- A section trivializes an object whose action pair map is invertible.
The inverse uses the inverse pair map on the pair consisting of the variable and
the chosen section; the second projection proves the two inverse identities.
Source: Stacks Tag 099X, trivializations of torsors.
(blueprint: det-pe-torsor-comparison-affine). -/
private def iso_of_section
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {G T : C} (a : G ⊗ T ⟶ T)
    [IsIso (lift a (snd G T))] (t : 𝟙_ C ⟶ T) : G ≅ T := by
  let q := lift a (snd G T)
  let f : G ⟶ G ⊗ T := lift (𝟙 G) (toUnit G ≫ t)
  let k : T ⟶ T ⊗ T := lift (𝟙 T) (toUnit T ≫ t)
  have hq : q ≫ snd T T = snd G T := by simp [q]
  have hqi : inv q ≫ snd G T = snd T T := by
    rw [← hq, IsIso.inv_hom_id_assoc]
  refine ⟨f ≫ a, k ≫ inv q ≫ fst G T, ?_, ?_⟩
  · have hf : f ≫ a ≫ k = f ≫ q := by
      ext <;> simp [f, k, q, comp_lift, ← Category.assoc]
    calc (f ≫ a) ≫ k ≫ inv q ≫ fst G T = f ≫ q ≫ inv q ≫ fst G T := by
            simpa only [Category.assoc] using congrArg (· ≫ inv q ≫ fst G T) hf
         _ = 𝟙 G := by simp [f]
  · have hk : k ≫ inv q ≫ fst G T ≫ f = k ≫ inv q := by
      ext <;> simp [f, k, comp_lift, Category.assoc, hqi]
    calc (k ≫ inv q ≫ fst G T) ≫ (f ≫ a) = k ≫ inv q ≫ a := by
            simpa only [Category.assoc] using congrArg (· ≫ a) hk
         _ = 𝟙 T := by
            have hqf : q ≫ fst T T = a := by simp [q]
            rw [← hqf, IsIso.inv_hom_id_assoc]
            simp [k]

/-- Restrict a section to obtain a global section over its source scheme.
Source: Stacks Tag 099X, restriction of a chosen torsor section.
(blueprint: det-pe-torsor-comparison-affine). -/
private def restriction_section (X : Scheme.{u}) (U : X.ProEt)
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (s : T.obj.obj (op U)) :
    𝟙_ _ ⟶ (Scheme.proEtaleSetRestriction X U).obj T := by
  let M := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop
  let q (W : U.left.ProEt) : M.obj W ⟶ U :=
    MorphismProperty.Over.homMk W.hom rfl
  exact ⟨{
    app := fun W ↦ TypeCat.ofHom (fun _ ↦ T.obj.map (q W.unop).op s)
    naturality := by
      intro V W f
      ext x
      change T.obj.map (q W.unop).op s =
        T.obj.map (M.map f.unop).op (T.obj.map (q V.unop).op s)
      rw [← Functor.map_comp_apply, ← op_comp]
      have hq : q W.unop = M.map f.unop ≫ q V.unop := by
        apply MorphismProperty.Over.Hom.ext
        exact (MorphismProperty.Over.w f.unop).symm
      rw [hq] }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- For a site object, restriction by composition is the scheme inverse image.
Both functors are left adjoint to restriction by the site pullback functor.
Source: Stacks Tags 00WX and 099R; the map/pullback adjunction.
(blueprint: det-pe-torsor-comparison-affine). -/
private def restriction_inverseImage_iso (X : Scheme.{u}) (U : X.ProEt) :
    proEtaleComparisonPullback (Type (u + 1)) U.hom ≅ Scheme.proEtaleSetRestriction X U := by
  letI hMap := Scheme.ProEt.isContinuous_overMap U.prop
  letI hPull := Scheme.ProEt.isContinuous_overPullback U.hom
  let adj : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop) ⊣
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom :=
    MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale) ⊤ U.hom U.prop trivial
  exact (proEtaleComparisonAdjunction (Type (u + 1)) U.hom).leftAdjointUniq
    (@Adjunction.sheafPushforwardContinuous _ _ _ _ _ _ _ _ adj
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) hMap hPull)

/-- Restricting a comparison inverse image gives the comparison inverse image
of the scheme inverse image. This is the existing canonical pullback comparison.
Source: Stacks Tags 099R and 00WX.
(blueprint: det-pe-torsor-comparison-affine). -/
private def classical_restriction_iso (X : Scheme.{u}) (U : X.ProEt) :
    torsorComparisonPullback X ⋙ Scheme.proEtaleSetRestriction X U ≅
      etaleComparisonPullback (Type (u + 1)) U.hom ⋙ torsorComparisonPullback U.left :=
  (Functor.isoWhiskerLeft _ (restriction_inverseImage_iso X U)).symm ≪≫
    (comparisonCoefficientPullbackIso (Type (u + 1)) U.hom).symm

/-- A torsor under a classical group is locally classical. The image sieve of
its epic terminal map supplies the covering by objects equipped with sections.
Those sections trivialize the torsor, and comparison/pullback compatibility
identifies the restricted group with an etale inverse image.
Source: Stacks Tag 099X; Bhatt--Scholze, Lemma 5.1.4.
(blueprint: det-pe-torsor-comparison-affine). -/
private theorem locally_classical_of_torsor (X : Scheme.{u})
    (G₀ : Grp (Sheaf X.smallEtaleTopology (Type (u + 1))))
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (a : (torsorComparisonPullback X).obj G₀.X ⊗ T ⟶ T)
    (h_iso : IsIso (lift a (snd ((torsorComparisonPullback X).obj G₀.X) T)))
    (h_epi : Epi (toUnit T)) : Scheme.IsProEtaleLocallyClassical X T := by
  let Q := 𝟙_ (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
  let q := toUnit T
  have hlocal : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) q.hom :=
    (Sheaf.isLocallySurjective_iff_epi q).mpr h_epi
  let I := Σ U : X.ProEt, T.obj.obj (op U)
  let U : I → X.ProEt := Sigma.fst
  have hcov : (Scheme.ProEt.topology X).CoversTop U := by
    intro W
    apply (Scheme.ProEt.topology X).superset_covering _
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) q.hom
        (show Q.obj.obj (op W) from PUnit.unit))
    rintro V f ⟨s, _⟩
    exact ⟨⟨V, s⟩, ⟨𝟙 V⟩⟩
  refine ⟨I, U, hcov, ?_⟩
  intro i
  let R := Scheme.proEtaleSetRestriction X (U i)
  let b : R.obj ((torsorComparisonPullback X).obj G₀.X) ⊗ R.obj T ⟶ R.obj T := R.map a
  have : IsIso (lift b (snd (R.obj ((torsorComparisonPullback X).obj G₀.X))
      (R.obj T))) := by
    change IsIso (R.map (lift a (snd ((torsorComparisonPullback X).obj G₀.X) T)))
    exact Functor.map_isIso _ _
  let e := iso_of_section b (restriction_section X (U i) T i.2)
  exact ⟨(etaleComparisonPullback (Type (u + 1)) (U i).hom).obj G₀.X,
    ⟨e.symm ≪≫ (classical_restriction_iso X (U i)).app G₀.X⟩⟩

/-- Conjugate an action and its torsor axioms by an isomorphism of carriers.
Source: Stacks Tag 099X, transport of torsor structure along comparison.
(blueprint: det-pe-torsor-comparison-affine). -/
private theorem transport_torsor
    {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (G T P : C) [MonObj G] (a : G ⊗ T ⟶ T) (e : P ≅ T)
    (h_one : (MonObj.one (X := G) ▷ T) ≫ a = (λ_ T).hom)
    (h_mul : (MonObj.mul (X := G) ▷ T) ≫ a =
      (α_ _ _ _).hom ≫ (G ◁ a) ≫ a)
    (h_iso : IsIso (lift a (snd G T))) (h_epi : Epi (toUnit T)) :
    let b := (G ◁ e.hom) ≫ a ≫ e.inv
    (MonObj.one (X := G) ▷ P) ≫ b = (λ_ P).hom ∧
    (MonObj.mul (X := G) ▷ P) ≫ b = (α_ _ _ _).hom ≫ (G ◁ b) ≫ b ∧
    IsIso (lift b (snd G P)) ∧ Epi (toUnit P) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← whisker_exchange_assoc, reassoc_of% h_one, leftUnitor_naturality_assoc]
    simp
  · rw [← whisker_exchange_assoc, reassoc_of% h_mul]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← associator_naturality_right_assoc]
    simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id,
      Category.id_comp]
  · have heq : lift ((G ◁ e.hom) ≫ a ≫ e.inv) (snd G P) =
        (G ◁ e.hom) ≫ lift a (snd G T) ≫ (e.inv ⊗ₘ e.inv) := by
      ext <;> simp
    rw [heq]
    infer_instance
  · have heq : toUnit P = e.hom ≫ toUnit T := toUnit_unique _ _
    rw [heq]
    infer_instance

/-- An inhabited etale sheaf on an affine base has a section on one affine
etale surjection. Refine the image sieve to finitely many affine sources and take
their disjoint union using the existing spectrum-of-product construction.
It is etale by source locality. Glue the sections after comparison using the
proved disjoint-union gluing lemma, then return through the invertible unit.
Source: Stacks Tag 099X, affine-cover reduction; Tags 0218 and 01I4.
(blueprint: det-pe-torsor-comparison-affine). -/
private theorem affine_section_of_epi (X : Scheme.{u}) [IsAffine X]
    (P : Sheaf X.smallEtaleTopology (Type (u + 1))) (hp : Epi (toUnit P)) :
    ∃ V : X.Etale, IsAffine V.left ∧ Surjective V.hom ∧
      Nonempty (P.obj.obj (op V)) := by
  let W : X.Etale := Scheme.Etale.mk (𝟙 X)
  have : CompactSpace W.left := inferInstanceAs (CompactSpace X)
  let q := toUnit P
  have hlocal : Presheaf.IsLocallySurjective X.smallEtaleTopology q.hom :=
    (Sheaf.isLocallySurjective_iff_epi q).mpr hp
  obtain ⟨n, U, f, hf, hU, hcov⟩ := Scheme.exists_finite_affine_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem X.smallEtaleTopology q.hom
      (show (𝟙_ (Sheaf X.smallEtaleTopology (Type (u + 1)))).obj.obj (op W) from PUnit.unit))
  have (i : Fin n) : IsAffine (U i).left := hU i
  let B : X.AffineProEt := Scheme.AffineProEt.ofEtale (𝟙 X)
  let V (i : ULift.{u} (Fin n)) : X.AffineProEt :=
    @Scheme.AffineProEt.ofEtale X (U i.down).left (hU i.down) (U i.down).hom inferInstance
  let g (i : ULift.{u} (Fin n)) : V i ⟶ B := MorphismProperty.Over.homMk (f i.down).left
    (MorphismProperty.Over.w (f i.down)) trivial
  let Z := Scheme.AffineProEt.sigmaCover V g
  let j := Scheme.AffineProEt.sigmaCoverι V g
  have hj (i : ULift.{u} (Fin n)) : IsOpenImmersion (j i).left :=
    Scheme.AffineProEt.isOpenImmersion_sigmaCoverι V g i
  have hjcov : ∀ z : Z.left, ∃ i, z ∈ Set.range (j i).left.base :=
    Scheme.AffineProEt.exists_mem_range_sigmaCoverι V g
  have hz : Etale Z.hom := by
    let C : Z.left.OpenCover := Scheme.Cover.mkOfCovers _ (fun i ↦ (V i).left)
      (fun i ↦ (j i).left) (fun z ↦ hjcov z)
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) C
    intro i
    rw [show C.f i ≫ Z.hom = (U i.down).hom from MorphismProperty.Over.w (j i)]
    infer_instance
  let E : X.Etale := Scheme.Etale.mk Z.hom
  have hsurj : Surjective E.hom := by
    have hs : ∀ x : B.left, ∃ i, x ∈ Set.range (g i).left.base := by
      intro x
      have hx : x ∈ ⋃ i, Set.range (f i).left := by rw [hcov]; trivial
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i⟩, y, hy⟩
    have H := Scheme.AffineProEt.surjective_sigmaCoverπ V g hs
    exact H
  refine ⟨E, inferInstanceAs (IsAffine Z.left), hsurj, ?_⟩
  choose s hs using hf
  let F := ((Scheme.AffineProEt.toProEt X).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.AffineProEt.topology X) (Scheme.ProEt.topology X)).obj
      ((torsorComparisonPullback X).obj P)
  let t (i : ULift.{u} (Fin n)) : F.obj.obj (op (V i)) :=
    ((Scheme.proEtaleSiteComparison X).unit.app P).hom.app (op (U i.down)) (s i.down)
  obtain ⟨z, _⟩ := Scheme.AffineProEt.exists_sigmaCover_glue V g F.property t
  have hu := Scheme.proEtaleComparisonUnitSets_isIso X
  let e := asIso (((Scheme.proEtaleSiteComparison X).unit.app P).hom.app (op E))
  exact ⟨e.inv z⟩

/-- Every torsor under a pulled-back group sheaf on an affine scheme descends to an
etale torsor with a section on one affine etale surjection; the given torsor is classical
and has a section on the same etale covering. The action isomorphism identifies these
sections with trivializations by left translation.
Source: blueprint `sk-lem-pe-torsor-comparison-affine.md`; Stacks Tag 099X
(blueprint: det-pe-torsor-comparison-affine).

Proof:
1. The epic terminal map gives a covering by objects with torsor sections. The
   inverse torsor pair map trivializes the restriction on each such object.
   Comparison/pullback compatibility makes each restricted group classical.
2. Apply the existing local-classicality theorem (Bhatt--Scholze, Lemma 5.1.4)
   to obtain an etale model P and an isomorphism e from its inverse image to T.
3. Conjugate the given action by e. The invertible comparison unit makes the
   inverse-image functor fully faithful. Take the preimage of the conjugated
   action, using its product comparison. Faithfulness and monoidal coherence
   reflect the unit and multiplication laws, the invertible pair map and the
   epic terminal map. This gives the etale torsor structure on P.
4. Refine the image sieve of P to the terminal etale sheaf to a finite affine
   family. Its disjoint union is affine, etale and surjective. Glue the sections
   on this union after comparison, then use the invertible unit to obtain a
   section of P on the union. Empty bases and empty finite families are allowed.
5. The essential-image criterion gives IsClassical T. The unit followed by e
   transports the section of P to T on the same affine etale surjection.

This uses the general local-classicality theorem to perform the continuity and
sheaf-descent argument, instead of descending the torsor cocycle explicitly.
Source for this route: Bhatt--Scholze, Lemmas 5.1.2 and 5.1.4; Stacks Tag 099X.
-/
theorem torsor_comparison_affine (X : Scheme.{u}) [IsAffine X]
    (G₀ : Grp (Sheaf X.smallEtaleTopology (Type (u + 1))))
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (a : (torsorComparisonPullback X).obj G₀.X ⊗ T ⟶ T)
    (h_one : (MonObj.one (X := (torsorComparisonPullback X).obj G₀.X) ▷ T) ≫ a =
      (λ_ T).hom)
    (h_mul : (MonObj.mul (X := (torsorComparisonPullback X).obj G₀.X) ▷ T) ≫ a =
      (α_ _ _ T).hom ≫ ((torsorComparisonPullback X).obj G₀.X ◁ a) ≫ a)
    (h_iso : IsIso (lift a (snd ((torsorComparisonPullback X).obj G₀.X) T)))
    (h_epi : Epi (toUnit T)) :
    ∃ (V : X.Etale), IsAffine V.left ∧ Surjective V.hom ∧
      ∃ (T₀ : Sheaf X.smallEtaleTopology (Type (u + 1))) (a₀ : G₀.X ⊗ T₀ ⟶ T₀),
        (MonObj.one (X := G₀.X) ▷ T₀) ≫ a₀ = (λ_ T₀).hom ∧
        (MonObj.mul (X := G₀.X) ▷ T₀) ≫ a₀ =
          (α_ G₀.X G₀.X T₀).hom ≫ (G₀.X ◁ a₀) ≫ a₀ ∧
        IsIso (lift a₀ (snd G₀.X T₀)) ∧ Epi (toUnit T₀) ∧
        Nonempty (T₀.obj.obj (op V)) ∧
        ∃ e : (torsorComparisonPullback X).obj T₀ ≅ T,
          Functor.LaxMonoidal.μ (torsorComparisonPullback X) G₀.X T₀ ≫
            (torsorComparisonPullback X).map a₀ ≫ e.hom =
              ((torsorComparisonPullback X).obj G₀.X ◁ e.hom) ≫ a ∧
          IsClassical T ∧ Nonempty (T.obj.obj (op ((Scheme.toProEt X).obj V))) := by
  have hl := locally_classical_of_torsor X G₀ T a h_iso h_epi
  obtain ⟨P, ⟨e'⟩⟩ := (Scheme.proEtale_locallyClassical_etaleCover X T).1 hl
  let e := e'.symm
  have hu := Scheme.proEtaleComparisonUnitSets_isIso X
  have : (torsorComparisonPullback X).Full :=
    (Scheme.proEtaleSiteComparison X).full_L_of_isSplitEpi_unit_app
  have : (torsorComparisonPullback X).Faithful :=
    (Scheme.proEtaleSiteComparison X).faithful_L_of_mono_unit_app
  let b := ((torsorComparisonPullback X).obj G₀.X ◁ e.hom) ≫ a ≫ e.inv
  obtain ⟨hb₁, hb₂, hbiso, hbepi⟩ := transport_torsor _ _ _ a e h_one h_mul h_iso h_epi
  obtain ⟨a₀, h₁, h₂, hi, he, ha⟩ :=
    reflect_torsor (torsorComparisonPullback X) G₀ P b hb₁ hb₂ hbiso hbepi
  have hc : IsClassical T :=
    (Scheme.proEtaleClassicalSheavesImage X T).1.mp ⟨P, ⟨e'⟩⟩
  have hsec : ∃ V : X.Etale, IsAffine V.left ∧ Surjective V.hom ∧
      Nonempty (P.obj.obj (op V)) := affine_section_of_epi X P he
  obtain ⟨V, hV, hsurj, hs⟩ := hsec
  refine ⟨V, hV, hsurj, P, a₀, h₁, h₂, hi, he, hs, e, ?_, hc, ?_⟩
  · rw [reassoc_of% ha]
    simp [b]
  · obtain ⟨s⟩ := hs
    exact ⟨e.hom.hom.app _ (((Scheme.proEtaleSiteComparison X).unit.app P).hom.app
      (op V) s)⟩

end AlgebraicGeometry.ProEtale
