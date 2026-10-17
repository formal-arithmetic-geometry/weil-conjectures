/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.TrivializationSections
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantOrigin
public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf

/-!
# Étale sheaves whose comparison pullback is locally constant

Let `Λ` be a finite ring and `G` a sheaf of `Λ`-modules on the small étale site of a scheme `Y`
such that the comparison pullback `ν^* G` is, on the members of a pro-étale covering family, the
constant sheaf of a finite `Λ`-module. Then `G` is finite locally constant
(`AlgebraicGeometry.ProEtale.isFiniteLocallyConstantSheaf_of_comparisonUpperStar`).

Let `y` be a point of `Y`. The proof runs as follows.

1. There is a weakly étale affine `V = lim Uⱼ ⟶ Y`, a cofiltered limit of affine étale
   `Y`-schemes, through whose image passes `y` and over which `ν^* G` is constant with value a
   finite module `M` (`AlgebraicGeometry.ProEtale.exists_affineProEt_comp_eq`, the density of
   the affine pro-étale site).
2. The sections of `ν^* G` over `V` are the colimit of the sections over the `Uⱼ`
   (`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone`); the trivialization
   over `V`, a linear map `M ⟶ Γ(V, ν^* G)`, factors through `Γ(U, ν^* G)` for some
   `U = Uⱼ` (`AlgebraicGeometry.ProEtale.exists_linearMap_lift_of_isColimit`).
3. Over every member `W ⟶ Y` of the trivializing covering family, the sections of `ν^* G`
   are locally constant functions to a finite module, so the image of `M` gives at every
   point of `W ×_Y U` a linear map, which is bijective on an open subset, independent of
   the member of the family by the transition maps
   (`AlgebraicGeometry.ProEtale.bijective_trivTransition`), and whose image in `U` is open,
   the members of a pro-étale covering family being jointly a quotient map. It contains the
   image of `V`.
4. On that open subscheme `O ⊆ U` the map `M_O ⟶ ν^* G|_O` is locally bijective, hence an
   isomorphism, so that `G|_O ≅ M_O` by full faithfulness of `ν^*`.
-/

@[expose] public section

universe v w u

open CategoryTheory Limits Opposite

/-- **Linear maps from a finite module to a filtered colimit factor through a stage**, for a
finite coefficient ring: the finitely many values lift to a common stage, and the finitely many
linear relations among them hold at a later stage. -/
lemma CategoryTheory.Limits.exists_linearMap_lift_of_isColimit {Λ : Type v} [CommRing Λ]
    [Finite Λ] {J : Type w} [Category J] [IsFiltered J] {K : J ⥤ ModuleCat.{v} Λ}
    {c : Cocone K} (hc : IsColimit c) [PreservesColimit K (forget (ModuleCat.{v} Λ))]
    (M : Type*) [AddCommGroup M] [Module Λ M] [Finite M] (b : M →ₗ[Λ] c.pt) :
    ∃ (j : J) (a : M →ₗ[Λ] K.obj j), ∀ m, c.ι.app j (a m) = b m := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite Λ
  -- lift the values to a common stage
  choose jm ym hym using fun m : M ↦ Concrete.isColimit_exists_rep K hc (b m)
  let O₁ : Finset J := Finset.univ.image jm
  have hO₁ (m : M) : jm m ∈ O₁ := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let k₀ := IsFiltered.sup O₁ ∅
  let a₀ (m : M) : K.obj k₀ := K.map (IsFiltered.toSup O₁ ∅ (hO₁ m)) (ym m)
  have ha₀ (m : M) : c.ι.app k₀ (a₀ m) = b m := by
    rw [← hym m, ← c.w (IsFiltered.toSup O₁ ∅ (hO₁ m))]
    rfl
  -- the linear relations hold at later stages
  let E := (M × M) ⊕ (Λ × M)
  let x : E → K.obj k₀
    | .inl (m, m') => a₀ (m + m') - a₀ m - a₀ m'
    | .inr (r, m) => a₀ (r • m) - r • a₀ m
  have hx (e : E) : c.ι.app k₀ (x e) = c.ι.app k₀ 0 := by
    rcases e with ⟨m, m'⟩ | ⟨r, m⟩
    · simp only [x]
      rw [map_sub, map_sub, ha₀, ha₀, ha₀, map_add, map_zero]
      abel_nf
      exact sub_eq_zero.2 rfl
    · simp only [x, map_sub, ha₀, map_smul, map_zero, sub_self]
  choose ke fe ge hfe using fun e ↦ Concrete.isColimit_exists_of_rep_eq K hc _ _ (hx e)
  let O₂ : Finset J := insert k₀ (Finset.univ.image ke)
  have hk₀ : k₀ ∈ O₂ := Finset.mem_insert_self _ _
  have hke (e : E) : ke e ∈ O₂ :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  let H : Finset (Σ' (X Y : J) (_ : X ∈ O₂) (_ : Y ∈ O₂), X ⟶ Y) :=
    Finset.univ.image fun e ↦ ⟨k₀, ke e, hk₀, hke e, fe e⟩
  obtain ⟨S, T, hT⟩ := IsFiltered.sup_exists O₂ H
  have hzero (e : E) : K.map (T hk₀) (x e) = 0 := by
    rw [← hT hk₀ (hke e) (Finset.mem_image_of_mem _ (Finset.mem_univ e)), K.map_comp,
      ConcreteCategory.comp_apply, hfe e, map_zero, map_zero]
  refine ⟨S, { toFun m := K.map (T hk₀) (a₀ m), map_add' m m' := ?_, map_smul' r m := ?_ },
    fun m ↦ ?_⟩
  · have := hzero (.inl (m, m'))
    simp only [x, map_sub] at this
    rw [sub_sub, sub_eq_zero] at this
    simp only [this]
  · have := hzero (.inr (r, m))
    simp only [x, map_sub, map_smul] at this
    rw [sub_eq_zero] at this
    simp only [this, RingHom.id_apply]
  · change c.ι.app S (K.map (T hk₀) (a₀ m)) = b m
    rw [← ConcreteCategory.comp_apply, c.w]
    exact ha₀ m

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **Density of the affine pro-étale site.** Every point of a weakly étale `Y`-scheme `W` lies
in the image of a `Y`-morphism from an object of the affine pro-étale site of `Y`. -/
lemma exists_affineProEt_comp_eq {Y W : Scheme.{u}} (g : W ⟶ Y) [WeaklyEtale g] (w : W) :
    ∃ (V : Y.AffineProEt) (v : V.left ⟶ W) (_ : v ≫ g = V.hom), w ∈ Set.range v := by
  obtain ⟨R, hR, hRS⟩ := (ProEt.mem_topology_iff (V := Scheme.ProEt.mk g)).1
    ((AffineProEt.toProEt Y).is_cover_of_isCoverDense (ProEt.topology Y) (Scheme.ProEt.mk g))
  have hR' := (ProEt.mem_precoverage_iff.1 hR).2.1
  obtain ⟨Z, f', hf, t, ht⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).1 hR' w
  obtain ⟨hf⟩ := hf
  obtain ⟨⟨V, l, m, hlm⟩⟩ := hRS _ _ hf
  subst ht
  refine ⟨V, m.left, by simpa using MorphismProperty.Over.w m, l.left t, ?_⟩
  subst hlm
  rfl

attribute [local instance] Scheme.continuousConstSMul_of_discreteTopology

section Model

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
  {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)}
  {ι : Type*} {W : ι → Scheme.{u}} {g : ∀ i, W i ⟶ Y} [∀ i, WeaklyEtale (g i)]
  {M : ι → Type (u + 1)} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  [∀ i, TopologicalSpace (M i)] [∀ i, DiscreteTopology (M i)]
  (ε : ∀ i, (ProEtale.upperStar (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
    (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (M i)))
  {U : Y.ProEt} {N : Type (u + 1)} [AddCommGroup N] [Module Λ N]
  (a : N →ₗ[Λ] F.obj.obj (op U))

/-- At a point `z` of a weakly étale `Y`-scheme `T` over `U` and over a member `W i` of the
trivializing family, the values at `z` of the images of the elements of `N`, for the
trivialization over `W i`. -/
noncomputable def modelMap (T : Y.ProEt) (k : T ⟶ U) (i : ι) (h : T.left ⟶ W i)
    (hh : h ≫ g i = T.hom) (z : T.left) : N →ₗ[Λ] M i where
  toFun n := trivSections (ε i) T h hh (F.obj.map k.op (a n)) z
  map_add' n n' := by simp only [map_add, ContinuousMap.add_apply]
  map_smul' r n := by simp only [map_smul, ContinuousMap.smul_apply, RingHom.id_apply]

lemma modelMap_apply (T : Y.ProEt) (k : T ⟶ U) (i : ι) (h : T.left ⟶ W i)
    (hh : h ≫ g i = T.hom) (z : T.left) (n : N) :
    modelMap ε a T k i h hh z n = trivSections (ε i) T h hh (F.obj.map k.op (a n)) z :=
  rfl

/-- `modelMap` is natural. -/
lemma modelMap_comp {T T' : Y.ProEt} (f : T' ⟶ T) (k : T ⟶ U) (k' : T' ⟶ U)
    (hk : f ≫ k = k') (i : ι) (h : T.left ⟶ W i) (hh : h ≫ g i = T.hom)
    (h' : T'.left ⟶ W i) (hh' : h' ≫ g i = T'.hom) (hf : f.left ≫ h = h') (z : T'.left) :
    modelMap ε a T' k' i h' hh' z = modelMap ε a T k i h hh (f.left z) := by
  ext n
  rw [modelMap_apply, modelMap_apply, ← hk, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply,
    trivSections_map (ε i) f h hh h' hh' hf]
  rfl

/-- The bijectivity of `modelMap` at a point does not depend on the member of the
trivializing family. -/
lemma bijective_modelMap_iff (T : Y.ProEt) (k : T ⟶ U) (i i' : ι) (h : T.left ⟶ W i)
    (hh : h ≫ g i = T.hom) (h' : T.left ⟶ W i') (hh' : h' ≫ g i' = T.hom) (z : T.left) :
    Function.Bijective (modelMap ε a T k i h hh z) ↔
      Function.Bijective (modelMap ε a T k i' h' hh' z) := by
  have e : (modelMap ε a T k i' h' hh' z : N → M i') =
      trivTransition (ε i) (ε i') T h hh h' hh' z ∘ modelMap ε a T k i h hh z := by
    ext n
    exact trivSections_apply_eq_trivTransition (ε i) (ε i') T h hh h' hh' _ z
  rw [e]
  exact ⟨fun hb ↦ (bijective_trivTransition (ε i) (ε i') T h hh h' hh' z).comp hb,
    fun hb ↦ (Function.Bijective.of_comp_iff' (bijective_trivTransition (ε i) (ε i') T h hh h'
      hh' z) _).1 hb⟩

/-- The locus where `modelMap` takes a given value is open. -/
lemma isOpen_setOf_modelMap_eq [Finite N] (T : Y.ProEt) (k : T ⟶ U) (i : ι)
    (h : T.left ⟶ W i) (hh : h ≫ g i = T.hom) (φ : N →ₗ[Λ] M i) :
    IsOpen {z | modelMap ε a T k i h hh z = φ} := by
  have : {z | modelMap ε a T k i h hh z = φ} =
      ⋂ n, (trivSections (ε i) T h hh (F.obj.map k.op (a n))) ⁻¹' {φ n} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hz n ↦ by rw [← hz]; rfl, fun hz ↦ LinearMap.ext fun n ↦ hz n⟩
  rw [this]
  exact isOpen_iInter_of_finite fun n ↦ (isOpen_discrete _).preimage (ContinuousMap.continuous _)

/-- The locus where `modelMap` is bijective is open. -/
lemma isOpen_setOf_bijective_modelMap [Finite N] (T : Y.ProEt) (k : T ⟶ U) (i : ι)
    (h : T.left ⟶ W i) (hh : h ≫ g i = T.hom) :
    IsOpen {z | Function.Bijective (modelMap ε a T k i h hh z)} := by
  have : {z | Function.Bijective (modelMap ε a T k i h hh z)} =
      ⋃ φ : {φ : N →ₗ[Λ] M i // Function.Bijective φ}, {z | modelMap ε a T k i h hh z = φ} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun hz ↦ ⟨⟨_, hz⟩, rfl⟩, fun ⟨φ, hφ⟩ ↦ hφ ▸ φ.2⟩
  rw [this]
  exact isOpen_iUnion fun φ ↦ isOpen_setOf_modelMap_eq ε a T k i h hh φ

/-- The base change of the member `W i` of the trivializing family to `U`, with its projection
to `U`, as morphism of the small pro-étale site of `Y`. -/
noncomputable abbrev modelBase (i : ι) : Y.ProEt := ProEt.baseChange (g i) U

lemma modelBase_condition (i : ι) :
    pullback.snd U.hom (g i) ≫ g i = (modelBase (g := g) (U := U) i).hom :=
  pullback.condition.symm

/-- The *good locus* in `U`: the points over which `modelMap` is bijective. -/
def goodLocus : Set U.left :=
  {x | ∃ (i : ι) (z : (modelBase (g := g) (U := U) i).left),
    (ProEt.baseChangeHom (g i) U).left z = x ∧
    Function.Bijective (modelMap ε a (modelBase i) (ProEt.baseChangeHom (g i) U) i
      (pullback.snd U.hom (g i)) (modelBase_condition i) z)}

/-- At every point of a weakly étale `Y`-scheme over `U` and `W i`, lying over the good locus,
`modelMap` is bijective. -/
lemma bijective_modelMap_of_mem_goodLocus (T : Y.ProEt) (k : T ⟶ U) (i : ι)
    (h : T.left ⟶ W i) (hh : h ≫ g i = T.hom) (z : T.left)
    (hz : k.left z ∈ goodLocus ε a) : Function.Bijective (modelMap ε a T k i h hh z) := by
  obtain ⟨i', z', hz', hb⟩ := hz
  -- the morphism from `T` to the base change of `W i`
  have hkh : k.left ≫ U.hom = h ≫ g i := by rw [hh]; exact MorphismProperty.Over.w k
  have hbase (j : ι) : (modelBase (g := g) (U := U) j).hom = pullback.fst U.hom (g j) ≫ U.hom :=
    rfl
  let φ : T ⟶ modelBase i := MorphismProperty.Over.homMk (pullback.lift k.left h hkh)
    (by rw [hbase, pullback.lift_fst_assoc]; exact MorphismProperty.Over.w k)
  have hφ : φ ≫ ProEt.baseChangeHom (g i) U = k :=
    MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  rw [modelMap_comp ε a φ (ProEt.baseChangeHom (g i) U) k hφ i (pullback.snd U.hom (g i))
    (modelBase_condition i) h hh (pullback.lift_snd _ _ _)]
  -- compare with the point `z'` over the same point of `U`
  have hpt : pullback.fst U.hom (g i) (φ.left z) = pullback.fst U.hom (g i') z' := by
    change (pullback.lift k.left h hkh ≫ pullback.fst U.hom (g i)) z = _
    rw [pullback.lift_fst]
    exact hz'.symm
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpt
  have : WeaklyEtale (pullback.fst (pullback.fst U.hom (g i)) (pullback.fst U.hom (g i')) ≫
      (modelBase (g := g) (U := U) i).hom) := by
    rw [hbase]
    infer_instance
  let TP : Y.ProEt := ProEt.mk (pullback.fst (pullback.fst U.hom (g i))
    (pullback.fst U.hom (g i')) ≫ (modelBase (g := g) (U := U) i).hom)
  let φ₁ : TP ⟶ modelBase i := MorphismProperty.Over.homMk (pullback.fst _ _) rfl
  let φ₂ : TP ⟶ modelBase i' := MorphismProperty.Over.homMk (pullback.snd _ _)
    (by
      change _ = pullback.fst _ _ ≫ (modelBase (g := g) (U := U) i).hom
      rw [hbase, hbase, pullback.condition_assoc])
  have hk : φ₂ ≫ ProEt.baseChangeHom (g i') U = φ₁ ≫ ProEt.baseChangeHom (g i) U :=
    MorphismProperty.Over.Hom.ext pullback.condition.symm
  have e₁ := modelMap_comp ε a φ₁ (ProEt.baseChangeHom (g i) U) _ rfl i
    (pullback.snd U.hom (g i)) (modelBase_condition i) _
    (by rw [Category.assoc, modelBase_condition]; rfl) rfl q
  have e₂ := modelMap_comp ε a φ₂ (ProEt.baseChangeHom (g i') U) _ rfl i'
    (pullback.snd U.hom (g i')) (modelBase_condition i') _
    (by rw [Category.assoc, modelBase_condition]; exact MorphismProperty.Over.w φ₂) rfl q
  rw [← hq₁]
  change Function.Bijective (modelMap ε a (modelBase i) _ i _ _ (φ₁.left q))
  rw [← e₁, bijective_modelMap_iff ε a TP _ i i' _ _ (φ₂.left ≫ pullback.snd U.hom (g i'))
    (by rw [Category.assoc, modelBase_condition]; exact MorphismProperty.Over.w φ₂), ← hk, e₂]
  change Function.Bijective (modelMap ε a (modelBase i') _ i' _ _
    (pullback.snd (pullback.fst U.hom (g i)) (pullback.fst U.hom (g i')) q))
  rw [hq₂]
  exact hb

/-- The good locus is open: its preimages in the base changes of the members of the
trivializing family are the loci where `modelMap` is bijective, and the base changes form a
pro-étale covering family of `U`. -/
lemma isOpen_goodLocus [Finite N] (hg : Presieve.ofArrows W g ∈ proetalePrecoverage Y) :
    IsOpen (goodLocus ε a) := by
  refine isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage
    (fun i ↦ pullback.fst U.hom (g i))
    (Precoverage.mem_coverings_of_isPullback g hg U.hom _ (fun i ↦ pullback.snd U.hom (g i))
      fun i ↦ IsPullback.of_hasPullback U.hom (g i)) _ fun i ↦ ?_
  have : {z | Function.Bijective (modelMap ε a (modelBase i) (ProEt.baseChangeHom (g i) U) i
      (pullback.snd U.hom (g i)) (modelBase_condition i) z)} =
      (pullback.fst U.hom (g i)).base ⁻¹' goodLocus ε a := by
    ext z
    exact ⟨fun hz ↦ ⟨i, z, rfl, hz⟩,
      fun hz ↦ bijective_modelMap_of_mem_goodLocus ε a _ _ i _ _ z hz⟩
  exact this ▸ isOpen_setOf_bijective_modelMap ε a (modelBase i) (ProEt.baseChangeHom (g i) U) i
    (pullback.snd U.hom (g i)) (modelBase_condition i)

section Restriction

variable (O : U.left.Opens)

/-- The morphism to `U` of a weakly étale scheme over the open `O` of `U`. -/
noncomputable def toModelBase (T : O.toScheme.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))).obj T ⟶ U :=
  MorphismProperty.Over.homMk (T.hom ≫ O.ι) (by simp)

lemma map_comp_toModelBase {T T' : O.toScheme.ProEt} (f : T' ⟶ T) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))).map f ≫
      toModelBase O T = toModelBase O T' :=
  MorphismProperty.Over.Hom.ext (by simp [toModelBase, MorphismProperty.Over.w_assoc f])

variable (F) in
/-- The restriction of `F` to the open `O` of `U`, as a sheaf on the small pro-étale site of
`O`. -/
noncomputable abbrev restrictionToOpen :
    Sheaf (Scheme.ProEt.topology O.toScheme) (ModuleCat.{u + 1} Λ) :=
  (ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) (O.ι ≫ U.hom) inferInstance).obj F

/-- The map from the constant presheaf with value `N` to the restriction of `F` to `O`
induced by `a`. -/
noncomputable def modelPresheafMap :
    (Functor.const O.toScheme.ProEtᵒᵖ).obj (ModuleCat.of Λ N) ⟶
      (restrictionToOpen F O).obj where
  app T := ModuleCat.ofHom ((F.obj.map (toModelBase O T.unop).op).hom ∘ₗ a)
  naturality T T' f := by
    ext n
    change F.obj.map (toModelBase O T'.unop).op (a n) =
      F.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))).map
        f.unop).op (F.obj.map (toModelBase O T.unop).op (a n))
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, map_comp_toModelBase]

lemma modelPresheafMap_app_apply (T : O.toScheme.ProEtᵒᵖ) (n : N) :
    (modelPresheafMap a O).app T n = F.obj.map (toModelBase O T.unop).op (a n) :=
  rfl

/-- The members of the trivializing family, base changed to `O`. -/
noncomputable abbrev coverMap (i : ι) : pullback (O.ι ≫ U.hom) (g i) ⟶ O.toScheme :=
  pullback.fst (O.ι ≫ U.hom) (g i)

variable {O} in
/-- The morphism to `W i` of the base change of an object of the pro-étale site of `O` to the
`i`-th member of the trivializing family. -/
noncomputable abbrev coverPieceHom (T : O.toScheme.ProEt) (i : ι) :
    (ProEt.baseChange (coverMap (g := g) O i) T).left ⟶ W i :=
  pullback.snd T.hom (coverMap O i) ≫ pullback.snd (O.ι ≫ U.hom) (g i)

variable {O} in
lemma coverPieceHom_comp (T : O.toScheme.ProEt) (i : ι) :
    coverPieceHom T i ≫ g i =
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))).obj
        (ProEt.baseChange (coverMap (g := g) O i) T)).hom := by
  simp only [coverPieceHom, Category.assoc, ← pullback.condition, ← pullback.condition_assoc]
  rfl

variable {O} in
/-- Every point of an object of the pro-étale site of `O` lifts to the base change to some
member of the trivializing family. -/
lemma exists_coverPiece_point (hg : Presieve.ofArrows W g ∈ proetalePrecoverage Y)
    (T : O.toScheme.ProEt) (z : T.left) :
    ∃ (i : ι) (z' : (ProEt.baseChange (coverMap (g := g) O i) T).left),
      (ProEt.baseChangeHom (coverMap (g := g) O i) T).left z' = z := by
  obtain ⟨i, w, hw⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 hg.2).1 ((O.ι ≫ U.hom) (T.hom z))
  obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (T.hom z) w hw.symm
  obtain ⟨z', hz', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom)
    (g := coverMap O i) z p hp₁.symm
  exact ⟨i, z', hz'⟩

variable {O}

/-- `modelMap` is bijective over the base changes to `O ⊆ goodLocus`. -/
lemma bijective_modelMap_coverPiece (hO : (O : Set U.left) ⊆ goodLocus ε a)
    (T : O.toScheme.ProEt) (i : ι) (z : (ProEt.baseChange (coverMap (g := g) O i) T).left) :
    Function.Bijective (modelMap ε a _ (toModelBase O (ProEt.baseChange (coverMap O i) T)) i
      (coverPieceHom T i) (coverPieceHom_comp T i) z) :=
  bijective_modelMap_of_mem_goodLocus ε a _ (toModelBase O (ProEt.baseChange (coverMap O i) T)) i
    (coverPieceHom T i) (coverPieceHom_comp T i) z
    (hO (by rw [← Scheme.Opens.range_ι O]; exact ⟨_, rfl⟩))

/-- **The map from the constant presheaf is locally injective.** -/
lemma isLocallyInjective_modelPresheafMap (hg : Presieve.ofArrows W g ∈ proetalePrecoverage Y)
    (hO : (O : Set U.left) ⊆ goodLocus ε a) :
    Presheaf.IsLocallyInjective (ProEt.topology O.toScheme) (modelPresheafMap a O) where
  equalizerSieve_mem {T} x y h := by
    by_cases hxy : x = y
    · subst hxy
      exact (ProEt.topology _).superset_covering (fun _ _ _ ↦ rfl) ((ProEt.topology _).top_mem _)
    · have : IsEmpty T.unop.left := ⟨fun z ↦ hxy ?_⟩
      · exact ProEt.mem_topology_of_openImmersion (ι := PEmpty.{u + 1}) _
          (Y := fun i ↦ i.elim) (fun i ↦ i.elim) (fun x ↦ isEmptyElim x) (fun i ↦ i.elim)
      obtain ⟨i, z', -⟩ := exists_coverPiece_point hg T.unop z
      let π := ProEt.baseChangeHom (coverMap (g := g) O i) T.unop
      refine (bijective_modelMap_coverPiece ε a hO T.unop i z').1 ?_
      have h' := congr_arg (fun s ↦ trivSections (ε i) _ (coverPieceHom T.unop i)
        (coverPieceHom_comp T.unop i) (F.obj.map
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))).map π).op s)
          z') h
      simp only [modelPresheafMap_app_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
        ← op_comp, map_comp_toModelBase] at h'
      exact h'

/-- **The map from the constant presheaf is locally surjective.** On the base change of an
object `T` to a member `W i` of the trivializing family, a section of `F` is a locally constant
function to `M i`; near a point `z` both it and `modelMap` are constant, and the section is the
image of the preimage of its value under the bijection `modelMap` at `z`. -/
lemma isLocallySurjective_modelPresheafMap [Finite N]
    (hg : Presieve.ofArrows W g ∈ proetalePrecoverage Y)
    (hO : (O : Set U.left) ⊆ goodLocus ε a) :
    Presheaf.IsLocallySurjective (ProEt.topology O.toScheme) (modelPresheafMap a O) where
  imageSieve_mem {T} s := by
    have hgO : Presieve.ofArrows _ (coverMap (g := g) O) ∈ proetalePrecoverage O.toScheme :=
      Precoverage.mem_coverings_of_isPullback g hg (O.ι ≫ U.hom) _
        (fun i ↦ pullback.snd _ (g i)) fun i ↦ IsPullback.of_hasPullback _ (g i)
    refine (ProEt.topology _).transitive
      (ProEt.ofArrows_baseChange_mem_topology T (coverMap O) hgO) _ ?_
    rintro Z f ⟨Z', h, _, ⟨i⟩, rfl⟩
    rw [Sieve.pullback_comp]
    refine (ProEt.topology _).pullback_stable h ?_
    let Ti := ProEt.baseChange (coverMap (g := g) O i) T
    let π := ProEt.baseChangeHom (coverMap (g := g) O i) T
    let mapO := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (O.ι ≫ U.hom))
    let σ := trivSections (ε i) (mapO.obj Ti) (coverPieceHom T i) (coverPieceHom_comp T i)
      (F.obj.map (mapO.map π).op s)
    let lam := modelMap ε a (mapO.obj Ti) (toModelBase O Ti) i (coverPieceHom T i)
      (coverPieceHom_comp T i)
    let Q (z : Ti.left) : Ti.left.Opens := Ti.left.fiberOpens σ (σ z) ⊓
      ⟨{z' | lam z' = lam z}, isOpen_setOf_modelMap_eq ε a (mapO.obj Ti) (toModelBase O Ti) i
        (coverPieceHom T i) (coverPieceHom_comp T i) (lam z)⟩
    have hQ (z : Ti.left) : z ∈ Q z := ⟨(Ti.left.mem_fiberOpens _ _ _).2 rfl, rfl⟩
    refine ProEt.mem_topology_of_openImmersion _ (fun z : Ti.left ↦ (Q z).ι)
      (fun z ↦ ⟨z, ⟨z, hQ z⟩, rfl⟩) fun z ↦ ?_
    obtain ⟨t, ht⟩ := (bijective_modelMap_coverPiece ε a hO T i z).2 (σ z)
    let r := ProEt.ofOpenImmersionHom Ti (Q z).ι
    have hhQ : ((Q z).ι ≫ coverPieceHom T i) ≫ g i =
        (mapO.obj (ProEt.ofOpenImmersion Ti (Q z).ι)).hom := by
      rw [Category.assoc, coverPieceHom_comp]
      rfl
    refine ⟨t, (trivSections (ε i) _ _ hhQ).injective (ContinuousMap.ext fun p ↦ ?_)⟩
    change trivSections (ε i) _ _ hhQ (F.obj.map (toModelBase O _).op (a t)) p =
      trivSections (ε i) _ _ hhQ (F.obj.map (mapO.map (r ≫ π)).op s) p
    rw [Functor.map_comp, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply,
      trivSections_map (ε i) (mapO.map r) (coverPieceHom T i) (coverPieceHom_comp T i) _ hhQ rfl]
    rw [← modelMap_apply, modelMap_comp ε a (mapO.map r) (toModelBase O Ti) _
      (map_comp_toModelBase O r) i (coverPieceHom T i) (coverPieceHom_comp T i) _ hhQ rfl]
    have hp := p.2
    simp only [Q, TopologicalSpace.Opens.mem_inf] at hp
    change lam ((Q z).ι p) t = σ ((Q z).ι p)
    rw [Scheme.Opens.ι_apply, hp.2, ht]
    exact ((Ti.left.mem_fiberOpens _ _ _).1 hp.1).symm

/-- **The restriction of `F` to `O ⊆ goodLocus` is constant**, with value `N`: the map from the
constant presheaf is locally bijective, so its sheafification is an isomorphism. -/
lemma nonempty_restrictionToOpen_iso [Finite N]
    (hg : Presieve.ofArrows W g ∈ proetalePrecoverage Y)
    (hO : (O : Set U.left) ⊆ goodLocus ε a) :
    Nonempty ((constantSheaf (ProEt.topology O.toScheme) (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ N) ≅ restrictionToOpen F O) := by
  have : (ProEt.topology O.toScheme).PreservesSheafification
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) := by
    have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) := inferInstance
    have (Y : O.toScheme.ProEt) : PreservesColimitsOfShape ((ProEt.topology O.toScheme).Cover Y)ᵒᵖ
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) := inferInstance
    exact GrothendieckTopology.instPreservesSheafification _ _
  let Ψ : (constantSheaf (ProEt.topology O.toScheme) (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ N) ⟶ restrictionToOpen F O :=
    ((sheafificationAdjunction (ProEt.topology O.toScheme) (ModuleCat.{u + 1} Λ)).homEquiv _
      _).symm (modelPresheafMap a O)
  have hΨ : toSheafify (ProEt.topology O.toScheme) _ ≫ Ψ.hom = modelPresheafMap a O := by
    have h := ((sheafificationAdjunction (ProEt.topology O.toScheme)
      (ModuleCat.{u + 1} Λ)).homEquiv _ (restrictionToOpen F O)).apply_symm_apply
        (modelPresheafMap a O)
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
    exact h
  have := isLocallyInjective_modelPresheafMap ε a hg hO
  have := isLocallySurjective_modelPresheafMap ε a hg hO
  have : IsIso Ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso Ψ).1 ⟨?_, ?_⟩
    · change Presheaf.IsLocallyInjective _ _
      rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology O.toScheme) _), hΨ]
      infer_instance
    · change Presheaf.IsLocallySurjective _ _
      rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology O.toScheme) _),
        hΨ]
      infer_instance
  exact ⟨asIso Ψ⟩

end Restriction

end Model

end AlgebraicGeometry.ProEtale
