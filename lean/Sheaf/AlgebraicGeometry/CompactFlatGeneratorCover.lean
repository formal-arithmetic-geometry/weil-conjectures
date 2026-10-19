/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Functorial covers by compact flat generators

Source: Stacks Project Tags 03EW and 077J, specialized to affine opens of a scheme.
(blueprint: lem-sc-compact-flat-generator-cover).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
namespace AlgebraicGeometry

private noncomputable def affineGenerator (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  (PresheafOfModules.sheafification (𝟙 (moduleRings Y.toRingedSpace).obj)).obj
    ((PresheafOfModules.free (moduleRings Y.toRingedSpace).obj).obj (yoneda.obj U))
private noncomputable def affineGeneratorHomEquiv (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    (affineGenerator Y U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRings Y.toRingedSpace).obj)).trans
    PresheafOfModules.freeYonedaEquiv
private theorem affineGeneratorHomEquiv_comp (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (f : affineGenerator Y U ⟶ M) (g : M ⟶ N) :
    affineGeneratorHomEquiv Y U N (f ≫ g) =
      g.val.app (op U) (affineGeneratorHomEquiv Y U M f) := by
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction _).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact PresheafOfModules.freeYonedaEquiv_comp _ _
private theorem affineGenerator_flat (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y) :
    SheafOfModules.IsFlat (affineGenerator Y U) := by
  let O := moduleRings Y.toRingedSpace
  let P := (PresheafOfModules.free O.obj).obj (yoneda.obj U)
  have hflatX (V : (TopologicalSpace.Opens Y)ᵒᵖ) :
      Module.Flat (Y.toRingedSpace.sheaf.obj.obj V) (P.obj V) := by
    change Module.Flat (Y.toRingedSpace.sheaf.obj.obj V)
      ((V.unop ⟶ U) →₀ Y.toRingedSpace.sheaf.obj.obj V)
    infer_instance
  have hpres : PreservesFiniteLimits (MonoidalCategory.tensorRight P) := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    have hpresX (V : (TopologicalSpace.Opens Y)ᵒᵖ) :
        PreservesFiniteLimits (MonoidalCategory.tensorRight
          (show ModuleCat (Y.toRingedSpace.sheaf.obj.obj V) from P.obj V)) := by
      have := hflatX V
      infer_instance
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun V ↦
      isLimitOfPreserves (MonoidalCategory.tensorRight
        (show ModuleCat (Y.toRingedSpace.sheaf.obj.obj V) from P.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation _ V) hc))⟩
  have : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology Y) (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology Y) (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj
    (R := Y.toRingedSpace.sheaf) (𝟙 O.obj) P hpres).2

private noncomputable def affineGeneratorCover (Y : Scheme.{u}) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) where
  obj M := ∐ (fun x : Σ U : Y.affineOpens, M.val.obj (op U.1) ↦ affineGenerator Y x.1.1)
  map {M N} f := Sigma.desc (fun x ↦ Sigma.ι
    (fun y : Σ U : Y.affineOpens, N.val.obj (op U.1) ↦ affineGenerator Y y.1.1)
    ⟨x.1, f.val.app (op x.1.1) x.2⟩)
  map_id M := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Category.comp_id]
    rfl
  map_comp f g := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc, Sigma.ι_desc_assoc]
    rfl
private noncomputable def affineCoverAugmentation (Y : Scheme.{u}) :
    affineGeneratorCover Y ⟶ 𝟭 _ where
  app M := Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 M).symm x.2)
  naturality {M N} f := by
    apply Sigma.hom_ext
    intro x
    symm
    change Sigma.ι _ x ≫
      Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 M).symm x.2) ≫ f =
      Sigma.ι _ x ≫ Sigma.desc (fun x ↦ Sigma.ι
        (fun y : Σ U : Y.affineOpens, N.val.obj (op U.1) ↦ affineGenerator Y y.1.1)
        ⟨x.1, f.val.app (op x.1.1) x.2⟩) ≫
      Sigma.desc (fun x ↦ (affineGeneratorHomEquiv Y x.1.1 N).symm x.2)
    simp only [Sigma.ι_desc, Sigma.ι_desc_assoc]
    apply (affineGeneratorHomEquiv Y x.1.1 N).injective
    rw [affineGeneratorHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
set_option backward.isDefEq.respectTransparency false in
private theorem affineCover_epi (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (q : (∐ (fun x : Σ U : Y.affineOpens, M.val.obj (op U.1) ↦
      affineGenerator Y x.1.1)) ⟶ M)
    (hq : ∀ x : Σ U : Y.affineOpens, M.val.obj (op U.1),
      Sigma.ι _ x ≫ q = (affineGeneratorHomEquiv Y x.1.1 M).symm x.2) :
    Epi q := by
  constructor
  intro N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := {V : Y.affineOpens // V.1 ≤ U}
  let cover : V → TopologicalSpace.Opens Y := fun V ↦ V.1.1
  have hc : U ≤ iSup cover := by
    intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  let Nsheaf : TopCat.Sheaf AddCommGrpCat.{u} Y :=
    ⟨N.val.presheaf, N.isSheaf⟩
  apply Nsheaf.eq_of_locally_eq' cover U
    (fun V ↦ homOfLE V.2) hc
  intro V
  change N.val.map (homOfLE V.2).op (f.val.app (op U) s) =
    N.val.map (homOfLE V.2).op (g.val.app (op U) s)
  have hh := Sigma.ι
    (fun x : Σ W : Y.affineOpens, M.val.obj (op W.1) ↦ affineGenerator Y x.1.1)
    ⟨V.1, M.val.map (homOfLE V.2).op s⟩ ≫= h
  simp only [← Category.assoc, hq] at hh
  have he := congrArg (affineGeneratorHomEquiv Y V.1.1 N) hh
  simp only [affineGeneratorHomEquiv_comp, Equiv.apply_symm_apply] at he
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply] at he
  exact he
set_option backward.isDefEq.respectTransparency false in
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K : Type u} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{u} R) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        (Limits.colimit.desc (D ⋙ SheafOfModules.forget R)
          ((SheafOfModules.forget R).mapCocone c))) := by
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := Limits.colimit.cocone (D ⋙ U)
  let hP := Limits.colimit.isColimit (D ⋙ U)
  let hQ := Limits.isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (Limits.IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : K) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : Limits.colimit.desc (D ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq, Functor.map_comp]
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt.presheaf)
    infer_instance
  infer_instance


set_option backward.isDefEq.respectTransparency false in
private theorem exists_local_subcoproduct_section (Y : Scheme.{u}) (U : TopologicalSpace.Opens Y)
    (K : Type u) (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (s : (∐ H).val.obj (op U)) (x : U) :
    ∃ (W : TopologicalSpace.Opens Y) (hWU : W ≤ U), x.val ∈ W ∧
      ∃ (S : Finset (Discrete K))
        (t : (∐ (fun k : S ↦ H k.val.as)).val.obj (op W)),
        (Sigma.desc (fun k : S ↦ Sigma.ι H k.val.as)).val.app (op W) t =
          (∐ H).val.map (homOfLE hWU).op s := by
  let R := moduleRings Y.toRingedSpace
  let D := liftToFinsetObj (Discrete.functor H)
  let c := finiteSubcoproductsCocone H
  let hc := isColimitFiniteSubproductsCocone H
  let F := D ⋙ SheafOfModules.forget R
  let P := colimit F
  let k : P ⟶ (∐ H).val := colimit.desc F ((SheafOfModules.forget R).mapCocone c)
  let q := (PresheafOfModules.toPresheaf R.obj).map k
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) q :=
    colimit_comparison_locally_surjective R D c hc
  have hcover := Presheaf.imageSieve_mem (Opens.grothendieckTopology Y) q s
  obtain ⟨W, f, hf, hxW⟩ := hcover x.val x.property
  obtain ⟨t, ht⟩ := hf
  let E := PresheafOfModules.evaluation R.obj (op W) ⋙ CategoryTheory.forget _
  have : PreservesColimit F E := by dsimp [E]; infer_instance
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective (F ⋙ E)
    (isColimitOfPreserves E (colimit.isColimit F)) t
  refine ⟨W, leOfHom f, hxW, i, a, ?_⟩
  have hk := colimit.ι_desc ((SheafOfModules.forget R).mapCocone c) i
  have hk' := congrArg (fun g ↦ g.app (op W) a) hk
  change k.app (op W) ((colimit.ι F i).app (op W) a) =
    (c.ι.app i).val.app (op W) a at hk'
  change (colimit.ι F i).app (op W) a = t at ha
  rw [ha] at hk'
  exact hk'.symm.trans ht

set_option backward.isDefEq.respectTransparency false in
private theorem affineGenerator_compact (Y : Scheme.{u}) (U : Y.affineOpens)
    (K : Type u) (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (f : affineGenerator Y U.1 ⟶ ∐ H) :
    ∃ (S : Finset K) (g : affineGenerator Y U.1 ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
      g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  classical
  let s := affineGeneratorHomEquiv Y U.1 (∐ H) f
  choose W hWU hx S t ht using fun x : U.1 ↦ exists_local_subcoproduct_section Y U.1 K H s x
  obtain ⟨B, hB⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 ↦ (W x : Set Y)) (fun x ↦ (W x).isOpen) (by
      intro x hxU
      exact Set.mem_iUnion.mpr ⟨(⟨x, hxU⟩ : U.1), hx (⟨x, hxU⟩ : U.1)⟩)
  let S' : Finset K := (B.biUnion S).image Discrete.as
  have hS (x : U.1) (hxB : x ∈ B) (k : S x) : k.val.as ∈ S' := by
    exact Finset.mem_image.mpr ⟨k.val,
      Finset.mem_biUnion.mpr ⟨x, hxB, k.property⟩, rfl⟩
  let inc : (∐ (fun k : {k // k ∈ S'} ↦ H k.1)) ⟶ ∐ H :=
    Sigma.desc (fun k ↦ Sigma.ι H k.1)
  let p : (∐ H) ⟶ ∐ (fun k : {k // k ∈ S'} ↦ H k.1) :=
    Sigma.desc (fun k ↦ if h : k ∈ S' then Sigma.ι (fun k : {k // k ∈ S'} ↦ H k.1) ⟨k, h⟩ else 0)
  refine ⟨S', f ≫ p, ?_⟩
  apply (affineGeneratorHomEquiv Y U.1 (∐ H)).injective
  rw [affineGeneratorHomEquiv_comp, affineGeneratorHomEquiv_comp]
  change inc.val.app (op U.1) (p.val.app (op U.1) s) = s
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨(∐ H).val.presheaf, (∐ H).isSheaf⟩
  let cover : B → TopologicalSpace.Opens Y := fun x ↦ W x.1
  have hc : U.1 ≤ iSup cover := by
    intro x hxU
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hB hxU)
    obtain ⟨hyB, hxy⟩ := Set.mem_iUnion.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hyB⟩, hxy⟩
  apply F.eq_of_locally_eq' cover U.1 (fun x ↦ homOfLE (hWU x.1)) hc
  intro x
  change (∐ H).val.map (homOfLE (hWU x.1)).op
      (inc.val.app (op U.1) (p.val.app (op U.1) s)) =
    (∐ H).val.map (homOfLE (hWU x.1)).op s
  rw [← PresheafOfModules.naturality_apply inc.val,
    ← PresheafOfModules.naturality_apply p.val, ← ht x.1]
  let incx : (∐ (fun k : S x.1 ↦ H k.val.as)) ⟶ ∐ H :=
    Sigma.desc (fun k ↦ Sigma.ι H k.val.as)
  have he : incx ≫ p ≫ inc = incx := by
    apply Sigma.hom_ext
    intro k
    simp [incx, p, inc, hS x.1 x.2 k]
  have ee := congrArg (fun e ↦ e.val.app (op (W x.1)) (t x.1)) he
  exact ee

/-- Every module sheaf has a functorial epic cover by a coproduct of flat sheaves
whose maps into arbitrary coproducts have finite support.

Source: Stacks Project Tag 03EW (3), the affine-open specialization of the
resolving class in Tag 077J and the parent relative-extension proof.
Proof: For each affine open U take the sheafification of the free module
presheaf on the representable presheaf U. This is a concrete model of j_! O_U.
Its section modules before sheafification are free; sheafification preserves
flatness. The sheafification and free-Yoneda adjunctions identify maps from this
generator with sections on U. Express a coproduct as the filtered colimit of
its finite subcoproducts. The comparison from the presheaf colimit to the sheaf
colimit is locally surjective because it is the sheafification unit followed
by an isomorphism. A lifted section of the presheaf colimit comes from one
finite stage. Quasi-compactness of U gives a finite subcover of these local
lifts. Take the union of their supports and project the original section onto
this finite subsum. On each member of the finite cover this projection followed
by inclusion fixes the section; sheaf separatedness gives the equality on U.
Define the cover of M to be the coproduct of these generators over all pairs
(U,s), where U is affine and s is a section of M on U. Its augmentation is
evaluation under the adjunction. A sheaf map sends (U,s) to (U,f(s)), using
the identity on the generator; coproduct universality gives functoriality
and naturality. To prove the augmentation epic, two maps out of M agreeing
after augmentation agree on every affine local section. Affine opens form
a basis, so sheaf separatedness makes the two maps equal on every open.
All indices lie in the scheme universe. The empty scheme and empty supports
need no exceptions. No sectionwise surjectivity or projectivity is asserted.
(blueprint: lem-sc-compact-flat-generator-cover). -/
theorem exists_functorial_compact_flat_generator_cover (Y : Scheme.{u}) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    ∃ (T : A ⥤ A) (π : T ⟶ 𝟭 A),
      ∀ M : A, Epi (π.app M) ∧
        ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((T.obj M) ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by
  refine ⟨affineGeneratorCover Y, affineCoverAugmentation Y, fun M ↦ ?_⟩
  refine ⟨affineCover_epi Y M ((affineCoverAugmentation Y).app M) ?_, ?_⟩
  · intro x
    change Sigma.ι _ x ≫ Sigma.desc _ = _
    exact Sigma.ι_desc _ _
  · refine ⟨(Σ U : Y.affineOpens, M.val.obj (op U.1)),
      (fun x ↦ affineGenerator Y x.1.1), ⟨Iso.refl _⟩, ?_, ?_⟩
    · intro x
      exact affineGenerator_flat Y x.1.1
    · intro x K H f
      exact affineGenerator_compact Y x.1 K H f

end AlgebraicGeometry
