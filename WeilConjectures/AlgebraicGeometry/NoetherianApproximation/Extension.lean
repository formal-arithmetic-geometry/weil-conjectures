/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Induction
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.Topology.Sets.Opens

/-!
# Absolute Noetherian approximation

**Absolute Noetherian approximation** (Stacks Project Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case follows by induction over a finite affine cover: the scheme attached to a
stage of `AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData` is the gluing of
the Noetherian stage `Dⱼ` and the affine scheme `Spec A` along `Wⱼ`, and `X = U ∪ V` is
the limit of these gluings.

## Main declarations

* `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`: absolute Noetherian
  approximation (blueprint: `lemma:nagata-absolute-noetherian-approximation-exists`).
* `AlgebraicGeometry.Scheme.NoetherianApproximation.sup`: the induction step, extending an
  approximation of a quasi-compact open across one affine open.
* `AlgebraicGeometry.Scheme.NoetherianApproximation.finsetSup`: the induction itself,
  extending an approximation of a quasi-compact open across finitely many affine opens
  (Stacks Project Tag 07RN).

## References

- [Stacks: Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
- [Stacks: Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.NoetherianApproximation

namespace InductionData

variable (E : InductionData.{u})

variable {E}

/-- The open immersion of `Wⱼ` into the stage `Dⱼ`. -/
noncomputable def Wι (E : InductionData.{u}) (j : Over E.i₀) :
    E.WD.obj j ⟶ E.N.D.obj j.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).app j

instance (E : InductionData.{u}) (j : Over E.i₀) : IsOpenImmersion (E.Wι j) :=
  inferInstanceAs (IsOpenImmersion ((opensDiagramι E.N.D E.i₀ E.W₀).app j))

@[reassoc]
lemma WD_map_Wι {j j' : Over E.i₀} (k : j ⟶ j') :
    E.WD.map k ≫ E.Wι j' = E.Wι j ≫ E.N.D.map k.left :=
  (opensDiagramι E.N.D E.i₀ E.W₀).naturality k

/-- The first projection from the coefficient algebra of a stage to the
sections of `V`. -/
noncomputable def Stage.toSectionsV (T : E.Stage) : CommRingCat.of ↥T.A ⟶ Γ(E.X, E.V) :=
  CommRingCat.ofHom ((RingHom.fst _ _).comp (Subalgebra.val T.A).toRingHom)

@[simp] lemma Stage.toSectionsV_apply (T : E.Stage) (a : ↥T.A) :
    T.toSectionsV a = (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 := rfl

/-- The map of coefficient algebras attached to a morphism of stages. -/
noncomputable def Stage.Hom.algHom {T T' : E.Stage} (f : T ⟶ T') :
    CommRingCat.of ↥T'.A ⟶ CommRingCat.of ↥T.A :=
  CommRingCat.ofHom
    ((AlgHom.codRestrict ((resAlgHom f.base).comp T'.A.val) T.A
      (fun a ↦ f.map_mem _ a.2)).toRingHom)

@[simp] lemma Stage.Hom.algHom_coe {T T' : E.Stage} (f : T ⟶ T') (a : ↥T'.A) :
    ((f.algHom a : ↥T.A) : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)) =
      ((a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).1,
        E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T'.j, ⊤)).2) := rfl

lemma Stage.Hom.algHom_toSectionsW {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.toSectionsW = T'.toSectionsW ≫ E.res f.base := rfl

lemma Stage.Hom.algHom_toSectionsV {T T' : E.Stage} (f : T ⟶ T') :
    f.algHom ≫ T.toSectionsV = T'.toSectionsV := rfl

@[simp] lemma Stage.Hom.algHom_id (T : E.Stage) : (𝟙 T : T ⟶ T).algHom = 𝟙 _ := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact E.res_id _ _

@[simp] lemma Stage.Hom.algHom_comp {T T' T'' : E.Stage} (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).algHom = g.algHom ≫ f.algHom := by
  ext a
  · rfl
  · rw [Stage.Hom.algHom_coe]
    exact (E.res_res g.base f.base _).symm

@[reassoc (attr := simp)]
lemma Stage.Hom.SpecMap_toSectionsV {T T' : E.Stage} (f : T ⟶ T') :
    Spec.map T.toSectionsV ≫ Spec.map f.algHom = Spec.map T'.toSectionsV := by
  rw [← Spec.map_comp, Stage.Hom.algHom_toSectionsV]

lemma Stage.toSpec_comp_SpecMap_algHom {T T' : E.Stage} (f : T ⟶ T') :
    T.toSpec ≫ Spec.map f.algHom = E.WD.map f.base ≫ T'.toSpec := by
  rw [Stage.toSpec, Stage.toSpec, Category.assoc, ← Spec.map_comp, Stage.Hom.algHom_toSectionsW,
    E.res_def f.base, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc]

/-- The system of stage schemes: the scheme attached to a stage is the gluing

```
  Wⱼ ───────▶ Spec A
  │             │
  Wι            inr
  ▼             ▼
  Dⱼ ──inl──▶ Dⱼ ⊔_{Wⱼ} Spec A
```

of the Noetherian stage `Dⱼ` and the affine scheme `Spec A` along `Wⱼ`. A morphism of
stages induces the morphism of pushouts given by `Dⱼ ⟶ Dⱼ'`, `Spec A ⟶ Spec A'` and
`Wⱼ ⟶ Wⱼ'`. -/
noncomputable def stageDiagram (E : InductionData.{u}) : E.Stage ⥤ Scheme.{u} where
  obj T := pushout (E.Wι T.j) T.toSpec
  map {T T'} f := pushout.map _ _ _ _ (E.N.D.map f.base.left) (Spec.map f.algHom)
    (E.WD.map f.base) (WD_map_Wι f.base).symm (Stage.toSpec_comp_SpecMap_algHom f)
  map_id T := by
    have hb : (𝟙 T : T ⟶ T).base.left = 𝟙 T.j.left := rfl
    have h2 := Stage.Hom.algHom_id T
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc, hb, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [pushout.inr_desc, h2, Spec.map_id, Category.id_comp, Category.comp_id]
  map_comp {T T' T''} f g := by
    have hb : (f ≫ g).base.left = f.base.left ≫ g.base.left := rfl
    have h2 := Stage.Hom.algHom_comp f g
    refine pushout.hom_ext ?_ ?_
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc, hb, CategoryTheory.Functor.map_comp,
        Category.assoc]
    · simp only [pushout.inr_desc, pushout.inr_desc_assoc, h2, Spec.map_comp, Category.assoc]

@[simp] lemma stageDiagram_obj (T : E.Stage) :
    E.stageDiagram.obj T = pushout (E.Wι T.j) T.toSpec := rfl

@[reassoc (attr := simp)]
lemma inl_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inl (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      E.N.D.map f.base.left ≫ pushout.inl (E.Wι T'.j) T'.toSpec :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    pushout.inr (E.Wι T.j) T.toSpec ≫ E.stageDiagram.map f =
      Spec.map f.algHom ≫ pushout.inr (E.Wι T'.j) T'.toSpec :=
  pushout.inr_desc _ _ _

@[simp] lemma opensRange_Wι (E : InductionData.{u}) (j : Over E.i₀) :
    (E.Wι j).opensRange = E.N.D.map j.hom ⁻¹ᵁ E.W₀ :=
  Scheme.Opens.opensRange_ι _

/-- The `Wⱼ`-squares of the system of stages are cartesian:

```
  Wⱼ ────▶ Dⱼ
  │        │
  ▼        ▼
  Wⱼ' ───▶ Dⱼ'
```
-/
lemma isPullback_Wι {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) (E.Wι T.j) (E.Wι T'.j) (E.N.D.map f.base.left) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (WD_map_Wι f.base).symm ?_
  rw [opensRange_Wι, opensRange_Wι, ← Scheme.Hom.comp_preimage, ← E.N.D.map_comp,
    Over.w f.base]

/-- The `Spec A`-squares of the system of stages are cartesian:

```
  Wⱼ ─────▶ Spec A
  │           │
  ▼           ▼
  Wⱼ' ────▶ Spec A'
```
-/
lemma isPullback_toSpec {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.WD.map f.base) T.toSpec T'.toSpec (Spec.map f.algHom) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Stage.toSpec_comp_SpecMap_algHom f) ?_
  rw [T.opensRange_toSpec, T'.opensRange_toSpec, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun l ↦ ?_
  rw [SpecMap_preimage_basicOpen]
  congr 1
  refine Subtype.ext ?_
  rw [Stage.Hom.algHom_coe, Stage.coe_gen, Stage.coe_gen, f.res_r]

/-- The `Dⱼ`-squares of the system of stage schemes are cartesian:

```
  Dⱼ ─────▶ Sⱼ
  │         │
  ▼         ▼
  Dⱼ' ────▶ Sⱼ'
```
-/
lemma isPullback_pushout_inl {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (E.N.D.map f.base.left) (pushout.inl (E.Wι T.j) T.toSpec)
      (pushout.inl (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inl_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

/-- The `Spec A`-squares of the system of stage schemes are cartesian:

```
  Spec A ────▶ Sⱼ
  │            │
  ▼            ▼
  Spec A' ───▶ Sⱼ'
```
-/
lemma isPullback_pushout_inr {T T' : E.Stage} (f : T ⟶ T') :
    IsPullback (Spec.map f.algHom) (pushout.inr (E.Wι T.j) T.toSpec)
      (pushout.inr (E.Wι T'.j) T'.toSpec) (E.stageDiagram.map f) :=
  isPullback_pushout_map_inr_of_isPullback (E.Wι T'.j) T'.toSpec (E.Wι T.j) T.toSpec
    (E.N.D.map f.base.left) (Spec.map f.algHom) (E.WD.map f.base) (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

instance (T : E.Stage) : CompactSpace (E.stageDiagram.obj T) :=
  inferInstanceAs (CompactSpace ↑(pushout (E.Wι T.j) T.toSpec))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A))) :=
  have : Algebra.FiniteType ℤ ↥T.A := (Subalgebra.fg_iff_finiteType _).mp T.fg_A
  inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (Spec (.of ↥T.A))))

instance (T : E.Stage) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.stageDiagram.obj T)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.stageDiagram.obj T))
    (pushout.desc (specULiftZIsTerminal.from (E.N.D.obj T.j.left))
      (specULiftZIsTerminal.from (Spec (CommRingCat.of ↥T.A)))
      (specULiftZIsTerminal.hom_ext _ _))]
  exact IsZariskiLocalAtSource.pushoutDesc (E.Wι T.j) T.toSpec _ inferInstance inferInstance

instance isAffineHom_stageDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    IsAffineHom (E.stageDiagram.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (Scheme.pushoutCover (E.Wι T'.j) T'.toSpec)
  rintro (_ | _)
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inl (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inl f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inl f).flip.isoPullback_hom_snd]
    infer_instance
  · change IsAffineHom (pullback.snd (E.stageDiagram.map f) (pushout.inr (E.Wι T'.j) T'.toSpec))
    refine (MorphismProperty.cancel_left_of_respectsIso (@IsAffineHom)
      (isPullback_pushout_inr f).flip.isoPullback.hom _).mp ?_
    rw [(isPullback_pushout_inr f).flip.isoPullback_hom_snd]
    infer_instance

/-! ### The cone -/

lemma top_le_preimage_V (E : InductionData.{u}) :
    (⊤ : E.Wc.pt.Opens) ≤ (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.V := by
  rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self]

lemma resV_eq (E : InductionData.{u}) :
    E.resV = (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ E.top_le_preimage_V := rfl

lemma range_WUι_comp_Uι_subset (E : InductionData.{u}) :
    Set.range (E.WU.ι ≫ E.U.ι) ⊆ Set.range E.V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨x, rfl⟩
  exact (E.opensRange_WUι_comp_Uι.le ⟨x, rfl⟩).2

/-- The canonical morphism from the intersection `W = U ⊓ V` to `V`. -/
noncomputable def interToV (E : InductionData.{u}) : E.Wc.pt ⟶ E.V.toScheme :=
  IsOpenImmersion.lift E.V.ι (E.WU.ι ≫ E.U.ι) E.range_WUι_comp_Uι_subset

@[reassoc (attr := simp)]
lemma interToV_ι (E : InductionData.{u}) : E.interToV ≫ E.V.ι = E.WU.ι ≫ E.U.ι :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma Wc_π_Wι (E : InductionData.{u}) (j : Over E.i₀) :
    E.Wc.π.app j ≫ E.Wι j = E.WU.ι ≫ E.N.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

lemma toSpecΓ_interToV (E : InductionData.{u}) :
    E.interToV ≫ E.V.toSpecΓ = E.Wc.pt.toSpecΓ ≫ Spec.map E.resV := by
  have : IsIso ((⊤ : E.Wc.pt.Opens).ι) := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hres : (E.WU.ι ≫ E.U.ι).resLE E.V ⊤ E.top_le_preimage_V =
      (⊤ : E.Wc.pt.Opens).ι ≫ E.interToV := by
    rw [← cancel_mono E.V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, E.interToV_ι]
  have h := Scheme.Opens.toSpecΓ_SpecMap_appLE (E.WU.ι ≫ E.U.ι) E.V (⊤ : E.Wc.pt.Opens)
    E.top_le_preimage_V
  rw [← E.resV_eq, hres, Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc] at h
  exact ((cancel_epi ((⊤ : E.Wc.pt.Opens).ι)).mp h).symm

/-- Comparing `W` with `Spec A` via `V` and via `Wⱼ` gives the same morphism:

```
  W ──────────▶ Wⱼ
  │              │
  interToV      toSpec
  ▼              ▼
  V ──▶ Spec Γ(X, V) ──▶ Spec A
```

This is where the fiber product condition on the coefficient algebra enters. -/
@[reassoc]
lemma Stage.interToV_toSpecΓ_SpecMap_toSectionsV (T : E.Stage) :
    E.interToV ≫ E.V.toSpecΓ ≫ Spec.map T.toSectionsV = E.Wc.π.app T.j ≫ T.toSpec := by
  rw [Stage.toSpec, ← Category.assoc E.interToV, E.toSpecΓ_interToV, Category.assoc,
    ← Spec.map_comp,
    ← Category.assoc (E.Wc.π.app T.j), Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact T.resV_eq_resLimit_of_mem a.2

/-- The open cover of `X` by `U` and `V`. -/
noncomputable def cover (E : InductionData.{u}) : E.X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b ↦ (bif b then E.U else E.V).toScheme)
    (fun b ↦ (bif b then E.U else E.V).ι)
    (fun x ↦ by
      have hx : x ∈ E.U ⊔ E.V := by
        rw [E.sup_eq_top]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
      · exact ⟨true, ⟨x, h⟩, rfl⟩
      · exact ⟨false, ⟨x, h⟩, rfl⟩)
    (fun b ↦ by cases b <;> exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))

@[simp] lemma cover_f_true (E : InductionData.{u}) : E.cover.f true = E.U.ι := rfl

@[simp] lemma cover_f_false (E : InductionData.{u}) : E.cover.f false = E.V.ι := rfl

/-- The morphism `U ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromU (T : E.Stage) : E.U.toScheme ⟶ E.stageDiagram.obj T :=
  E.N.π.app T.j.left ≫ pushout.inl (E.Wι T.j) T.toSpec

/-- The morphism `V ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromV (T : E.Stage) : E.V.toScheme ⟶ E.stageDiagram.obj T :=
  E.V.toSpecΓ ≫ Spec.map T.toSectionsV ≫ pushout.inr (E.Wι T.j) T.toSpec

lemma Stage.WUι_fromU (T : E.Stage) : E.WU.ι ≫ T.fromU = E.interToV ≫ T.fromV := by
  rw [Stage.fromU, Stage.fromV, ← E.Wc_π_Wι_assoc T.j, pushout.condition,
    T.interToV_toSpecΓ_SpecMap_toSectionsV_assoc]

/-- The isomorphism between `U ⊓ V` and the intersection `W`. -/
noncomputable def infIso (E : InductionData.{u}) : (E.U ⊓ E.V).toScheme ≅ E.Wc.pt :=
  IsOpenImmersion.isoOfRangeEq (E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U)) E.WU.ι (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
      Scheme.Opens.opensRange_ι, InductionData.WU, E.hW₀]
    congr 1
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq])

@[reassoc (attr := simp)]
lemma infIso_hom_WUι (E : InductionData.{u}) :
    E.infIso.hom ≫ E.WU.ι = E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma infIso_hom_interToV (E : InductionData.{u}) :
    E.infIso.hom ≫ E.interToV = E.X.homOfLE (inf_le_right : E.U ⊓ E.V ≤ E.V) := by
  rw [← cancel_mono E.V.ι, Category.assoc, E.interToV_ι, ← Category.assoc, E.infIso_hom_WUι,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι]

@[reassoc (attr := simp)]
lemma infIso_inv_homOfLE (E : InductionData.{u}) :
    E.infIso.inv ≫ E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) = E.WU.ι := by
  rw [← E.infIso_hom_WUι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma infIso_inv_infι (E : InductionData.{u}) :
    E.infIso.inv ≫ (E.U ⊓ E.V).ι = E.WU.ι ≫ E.U.ι := by
  rw [← Scheme.homOfLE_ι E.X (inf_le_left : E.U ⊓ E.V ≤ E.U), ← Category.assoc,
    infIso_inv_homOfLE]

lemma Stage.homOfLE_fromU (T : E.Stage) {W : E.X.Opens} (h₁ : W ≤ E.U) (h₂ : W ≤ E.V) :
    E.X.homOfLE h₁ ≫ T.fromU = E.X.homOfLE h₂ ≫ T.fromV := by
  rw [← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_left : E.U ⊓ E.V ≤ E.U),
    ← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_right : E.U ⊓ E.V ≤ E.V), Category.assoc,
    Category.assoc, ← E.infIso_hom_WUι, ← E.infIso_hom_interToV, Category.assoc, Category.assoc,
    T.WUι_fromU]

/-- The morphism from `X` to the stage scheme of a stage: it restricts to
the projection of the approximation of `U` on `U`, and to the map induced by the first
projection of the coefficient algebra on `V`. -/
noncomputable def Stage.fromX (T : E.Stage) : E.X ⟶ E.stageDiagram.obj T :=
  -- the `bif` idiom used for `cover` does not typecheck here: the type of the morphism
  -- depends on `b`
  E.cover.glueMorphisms (fun b ↦ match b with | true => T.fromU | false => T.fromV) (by
    rintro (_ | _) (_ | _)
    · change pullback.fst E.V.ι E.V.ι ≫ T.fromV = pullback.snd E.V.ι E.V.ι ≫ T.fromV
      rw [(cancel_mono E.V.ι).mp
        (pullback.condition : pullback.fst E.V.ι E.V.ι ≫ _ = pullback.snd _ _ ≫ _)]
    · change pullback.fst E.V.ι E.U.ι ≫ T.fromV = pullback.snd E.V.ι E.U.ι ≫ T.fromU
      rw [← cancel_epi (isPullback_opens_inf E.V E.U).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact (T.homOfLE_fromU inf_le_right inf_le_left).symm
    · change pullback.fst E.U.ι E.V.ι ≫ T.fromU = pullback.snd E.U.ι E.V.ι ≫ T.fromV
      rw [← cancel_epi (isPullback_opens_inf E.U E.V).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact T.homOfLE_fromU inf_le_left inf_le_right
    · change pullback.fst E.U.ι E.U.ι ≫ T.fromU = pullback.snd E.U.ι E.U.ι ≫ T.fromU
      rw [(cancel_mono E.U.ι).mp
        (pullback.condition : pullback.fst E.U.ι E.U.ι ≫ _ = pullback.snd _ _ ≫ _)])

@[reassoc (attr := simp)]
lemma Stage.Uι_fromX (T : E.Stage) : E.U.ι ≫ T.fromX = T.fromU :=
  E.cover.ι_glueMorphisms _ _ true

@[reassoc (attr := simp)]
lemma Stage.Vι_fromX (T : E.Stage) : E.V.ι ≫ T.fromX = T.fromV :=
  E.cover.ι_glueMorphisms _ _ false

@[reassoc]
lemma N_π_naturality (E : InductionData.{u}) {i i' : E.N.I} (g : i ⟶ i') :
    E.N.π.app i ≫ E.N.D.map g = E.N.π.app i' :=
  E.cone.w g

/-- The cone with point `X` over the system of stage schemes. -/
noncomputable def stageCone (E : InductionData.{u}) : Cone E.stageDiagram where
  pt := E.X
  π :=
    { app := fun T ↦ T.fromX
      naturality := fun T T' f ↦ by
        change 𝟙 E.X ≫ T'.fromX = T.fromX ≫ E.stageDiagram.map f
        rw [Category.id_comp]
        refine E.cover.hom_ext _ _ fun b ↦ ?_
        cases b
        · simp only [cover_f_false, Stage.Vι_fromX, Stage.Vι_fromX_assoc, Stage.fromV,
            Category.assoc, inr_stageDiagram_map, Stage.Hom.SpecMap_toSectionsV_assoc]
        · simp only [cover_f_true, Stage.Uι_fromX, Stage.Uι_fromX_assoc, Stage.fromU,
            Category.assoc, inl_stageDiagram_map, E.N_π_naturality_assoc] }

@[simp] lemma stageCone_pt (E : InductionData.{u}) : E.stageCone.pt = E.X := rfl

@[simp] lemma stageCone_π_app (E : InductionData.{u}) (T : E.Stage) :
    E.stageCone.π.app T = T.fromX := rfl

/-! ### The two charts of a stage scheme -/

/-- The chart of a stage scheme coming from the Noetherian stage `Dⱼ`. -/
noncomputable def Stage.chartU (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inl (E.Wι T.j) T.toSpec).opensRange

@[simp] lemma Stage.chartU_def (T : E.Stage) :
    T.chartU = (pushout.inl (E.Wι T.j) T.toSpec).opensRange := rfl

/-- The chart of a stage scheme coming from `Spec A`. -/
noncomputable def Stage.chartV (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inr (E.Wι T.j) T.toSpec).opensRange

@[simp] lemma Stage.chartV_def (T : E.Stage) :
    T.chartV = (pushout.inr (E.Wι T.j) T.toSpec).opensRange := rfl

lemma Stage.chartU_sup_chartV (T : E.Stage) : T.chartU ⊔ T.chartV = ⊤ :=
  opensRange_pushout_inl_sup_opensRange_inr _ _

lemma Stage.preimage_chartU {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartU = T.chartU :=
  pushout_map_preimage_opensRange_inl_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma Stage.preimage_chartV {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartV = T.chartV :=
  pushout_map_preimage_opensRange_inr_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

lemma Stage.chartU_inf_chartV (T : E.Stage) :
    T.chartU ⊓ T.chartV = (E.Wι T.j ≫ pushout.inl (E.Wι T.j) T.toSpec).opensRange := by
  rw [Stage.chartU_def, Stage.chartV_def,
    Scheme.Hom.opensRange_comp (E.Wι T.j) (pushout.inl (E.Wι T.j) T.toSpec),
    ← pushout_inl_preimage_opensRange_inr (E.Wι T.j) T.toSpec,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

lemma Stage.fromX_preimage_chartU (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartU = E.U := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by
      rw [E.sup_eq_top]
      trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · exact h
    · -- `x` lies in `V`; its image in `Spec A` lies in the image of `Wⱼ`, hence in one of
      -- the basic opens of the generators, which are contained in `U`.
      obtain ⟨y, hy⟩ : ∃ y, pushout.inl (E.Wι T.j) T.toSpec y = T.fromX x := hx
      let x' : E.V.toScheme := ⟨x, h⟩
      have hfV : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
          (Spec.map T.toSectionsV (E.V.toSpecΓ x')) :=
        calc T.fromX x = (E.V.ι ≫ T.fromX) x' := rfl
          _ = T.fromV x' := by rw [Stage.Vι_fromX]
          _ = _ := rfl
      rw [hfV] at hy
      obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy
      have hq : Spec.map T.toSectionsV (E.V.toSpecΓ x') ∈ T.toSpec.opensRange := ⟨w, hw⟩
      rw [T.opensRange_toSpec] at hq
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
      have hl' : E.V.toSpecΓ x' ∈
        Spec.map T.toSectionsV ⁻¹ᵁ PrimeSpectrum.basicOpen (T.gen l) := hl
      rw [SpecMap_preimage_basicOpen] at hl'
      have hb : (T.toSectionsV (T.gen l) : Γ(E.X, E.V)) = E.b l := rfl
      rw [hb] at hl'
      have : x' ∈ E.V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (E.b l) := hl'
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at this
      exact ((E.basicOpen_b_le_inf l) this).1
  · change T.fromX x ∈ T.chartU
    have h1 : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec
        (E.N.π.app T.j.left (⟨x, hx⟩ : E.U.toScheme)) :=
      calc T.fromX x = (E.U.ι ≫ T.fromX) (⟨x, hx⟩ : E.U.toScheme) := rfl
        _ = T.fromU (⟨x, hx⟩ : E.U.toScheme) := by rw [Stage.Uι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartV (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartV = E.V := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by
      rw [E.sup_eq_top]
      trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · obtain ⟨y, hy⟩ : ∃ y, pushout.inr (E.Wι T.j) T.toSpec y = T.fromX x := hx
      let x' : E.U.toScheme := ⟨x, h⟩
      have hfU : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec (E.N.π.app T.j.left x') :=
        calc T.fromX x = (E.U.ι ≫ T.fromX) x' := rfl
          _ = T.fromU x' := by rw [Stage.Uι_fromX]
          _ = _ := rfl
      rw [hfU] at hy
      obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy.symm
      have hp : E.N.π.app T.j.left x' ∈ (E.Wι T.j).opensRange := ⟨w, hw⟩
      rw [opensRange_Wι] at hp
      have hp' : E.N.π.app E.i₀ x' ∈ E.W₀ := by
        rw [← E.N_π_naturality T.j.hom, Scheme.Hom.comp_apply]
        exact hp
      have hmem : x' ∈ E.N.π.app E.i₀ ⁻¹ᵁ E.W₀ := hp'
      rwa [E.hW₀] at hmem
    · exact h
  · change T.fromX x ∈ T.chartV
    have h1 : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
        (Spec.map T.toSectionsV (E.V.toSpecΓ (⟨x, hx⟩ : E.V.toScheme))) :=
      calc T.fromX x = (E.V.ι ≫ T.fromX) (⟨x, hx⟩ : E.V.toScheme) := rfl
        _ = T.fromV (⟨x, hx⟩ : E.V.toScheme) := by rw [Stage.Vι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartU_inf_chartV (T : E.Stage) :
    T.fromX ⁻¹ᵁ (T.chartU ⊓ T.chartV) = E.U ⊓ E.V := by
  rw [Scheme.Hom.preimage_inf, T.fromX_preimage_chartU, T.fromX_preimage_chartV]

/-! ### The limit property, chart by chart -/

/-- The system of Noetherian stages `Dⱼ`, indexed by the stages below a
fixed stage. -/
noncomputable def baseDiagram (E : InductionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀ ⋙ E.N.D

/-- `U` is the limit of the Noetherian stages `Dⱼ` indexed by the stages
below a fixed stage: the index functor is initial. -/
noncomputable def isLimitBaseCone (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.cone).symm E.N.isLimit

set_option maxHeartbeats 400000 in
-- Naturality has to identify the `Dⱼ`-chart of the pushout defining the stage scheme with
-- the preimage of `chartU`, for every stage below `T₀`.
/-- The `U`-chart of a stage scheme is `Dⱼ`, compatibly with the transition morphisms:

```
  Dⱼ  ────≅────▶ Sⱼ ⊓ chartU
  │                  │
  ▼                  ▼
  Dⱼ' ────≅────▶ Sⱼ' ⊓ chartU
```
-/
noncomputable def chartUIso (E : InductionData.{u}) (T₀ : E.Stage) :
    E.baseDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ T₀.chartU :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Stage.preimage_chartU S.hom, Stage.chartU_def]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartU))]
      have h : (E.baseDiagram T₀).map k = E.N.D.map k.left.base.left := rfl
      simp only [h, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map])

/-- The restriction of the stage cone to the `U`-chart is a limit cone. -/
noncomputable def isLimitOpensConeChartU (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU) :=
  IsLimit.equivOfNatIsoOfIso (E.chartUIso T₀)
    (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU)
    (Cone.ext (E.X.isoOfEq T₀.fromX_preimage_chartU.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Category.assoc, chartUIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Scheme.isoOfEq_hom_ι_assoc]
      exact (Stage.Uι_fromX S.left).symm))
    (E.isLimitBaseCone T₀)

/-- The system of intersections `Wⱼ`, indexed by the stages below a fixed
stage. -/
noncomputable def interDiagram (E : InductionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ E.WD

/-- `W = U ⊓ V` is the limit of the `Wⱼ` indexed by the stages below a
fixed stage. -/
noncomputable def isLimitInterCone (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.Wc).symm E.isLimitWc

set_option maxHeartbeats 1600000 in
-- Naturality of the overlap isomorphism has to unfold the pushout defining the stage
-- scheme of every stage below `T₀`.
/-- The overlap of the two charts of a stage scheme is `Wⱼ`, compatibly with the
transition morphisms:

```
  Wⱼ  ────≅────▶ Sⱼ ⊓ (chartU ⊓ chartV)
  │                  │
  ▼                  ▼
  Wⱼ' ────≅────▶ Sⱼ' ⊓ (chartU ⊓ chartV)
```
-/
noncomputable def interIso (E : InductionData.{u}) (T₀ : E.Stage) :
    E.interDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ (T₀.chartU ⊓ T₀.chartV) :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq
      (E.Wι S.left.j ≫ pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ (T₀.chartU ⊓ T₀.chartV)))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, Stage.preimage_chartU S.hom,
        Stage.preimage_chartV S.hom, Stage.chartU_inf_chartV]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      have h : (E.interDiagram T₀).map k = E.WD.map k.left.base := rfl
      simp only [h, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map,
        WD_map_Wι_assoc])

/-- The restriction of the stage cone to the overlap of the two charts is a
limit cone. -/
noncomputable def isLimitOpensConeInter (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV)) :=
  IsLimit.equivOfNatIsoOfIso (E.interIso T₀)
    (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex))
    (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV))
    (Cone.ext (E.infIso.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartU_inf_chartV.symm)
      (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, interIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, infIso_inv_infι_assoc, stageCone_π_app]
      exact (E.Wc_π_Wι_assoc S.left.j _).trans (by rw [Stage.Uι_fromX, Stage.fromU])))
    (E.isLimitInterCone T₀)
/-! ### The `Spec A`-chart: the sections of `V` are the colimit of the coefficient algebras -/

/-- Every section of `V` occurs in the coefficient algebra of some stage. -/
lemma exists_stage_mem_A (E : InductionData.{u}) (β : Γ(E.X, E.V)) :
    ∃ (T : E.Stage) (a : ↥T.A), (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 = β := by
  obtain ⟨T₁⟩ := (inferInstance : Nonempty E.Stage)
  obtain ⟨j₁, x₁, hx₁⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.resV β)
  obtain ⟨j₂, k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j j₁
  have hxt : E.resLimit j₂ (E.res k₂ x₁) = E.resV β := by
    rw [E.resLimit_res]
    exact hx₁.symm
  have hle : Algebra.adjoin ℤ {(β, E.res k₂ x₁)} ≤ E.fiberProduct j₂ :=
    Algebra.adjoin_le (by
      rintro p rfl
      exact (E.mem_fiberProduct_iff _).mpr hxt.symm)
  have hfg : (Algebra.adjoin ℤ {(β, E.res k₂ x₁)}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.finite_singleton _, rfl⟩
  exact ⟨T₁.restrict k₁ _ hle hfg,
    ⟨(β, E.res k₂ x₁),
      T₁.le_restrict_A k₁ _ hle hfg (Algebra.subset_adjoin rfl)⟩, rfl⟩

/-- Two elements of a coefficient algebra whose components agree are
equal. -/
lemma Stage.Hom.algHom_eq_of_fst_eq_of_res_eq {T T' : E.Stage} (f : T' ⟶ T) (a b : ↥T.A)
    (h1 : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1)
    (h2 : E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.res f.base (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2) :
    f.algHom a = f.algHom b :=
  Subtype.ext (by rw [Stage.Hom.algHom_coe, Stage.Hom.algHom_coe, h1, h2])

/-- Two elements of a coefficient algebra with the same `V`-component become
equal at a later stage: their `Wⱼ`-components agree on the intersection `W`, hence already at
a finite stage. -/
lemma exists_hom_algHom_eq (E : InductionData.{u}) (T : E.Stage) (a b : ↥T.A)
    (h : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1) :
    ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b := by
  have ht : E.resLimit T.j (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.resLimit T.j (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := by
    rw [← T.resV_eq_resLimit_of_mem a.2, ← T.resV_eq_resLimit_of_mem b.2, h]
  have hcpt : IsCompact ((⊤ : (E.WD.obj T.j).Opens) : Set (E.WD.obj T.j)) := isCompact_univ
  obtain ⟨j', k, hk⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt _ _ ht
  exact ⟨T.restrict k ⊥ bot_le Subalgebra.fg_bot,
    T.restrictHom k ⊥ bot_le Subalgebra.fg_bot,
    Stage.Hom.algHom_eq_of_fst_eq_of_res_eq _ a b h hk⟩

/-- The system of coefficient algebras of the stages, as a diagram in the
opposite category of commutative rings. -/
noncomputable def algOp (E : InductionData.{u}) : E.Stage ⥤ CommRingCatᵒᵖ where
  obj T := Opposite.op (CommRingCat.of ↥T.A)
  map f := (f.algHom).op
  map_id T := Quiver.Hom.unop_inj (Stage.Hom.algHom_id T)
  map_comp f g := Quiver.Hom.unop_inj (Stage.Hom.algHom_comp f g)

/-- `Γ(X, V)` as a cocone on the system of coefficient algebras. -/
noncomputable def algCocone (E : InductionData.{u}) : Cocone E.algOp.leftOp where
  pt := Γ(E.X, E.V)
  ι :=
    { app := fun T ↦ T.unop.toSectionsV
      naturality := fun _ _ f ↦
        (Stage.Hom.algHom_toSectionsV f.unop).trans (Category.comp_id _).symm }

/-- `Γ(X, V)` is the filtered colimit of the coefficient algebras of the
stages: every section of `V` occurs at some stage, and two elements with the same
`V`-component become equal at a later stage. -/
noncomputable def isColimitAlgCocone (E : InductionData.{u}) : IsColimit E.algCocone := by
  have : ReflectsColimit E.algOp.leftOp (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun β ↦ ?_) (fun T a b hab ↦ ?_)
  · obtain ⟨T, a, ha⟩ := E.exists_stage_mem_A β
    exact ⟨Opposite.op T, a, ha.symm⟩
  · obtain ⟨T', f, hf⟩ := E.exists_hom_algHom_eq T.unop a b hab
    exact ⟨Opposite.op T', f.op, hf⟩

/-- The system of the spectra of the coefficient algebras. -/
noncomputable def specDiagram (E : InductionData.{u}) : E.Stage ⥤ Scheme.{u} :=
  E.algOp ⋙ Scheme.Spec

/-- `V ≅ Spec Γ(X, V)` as a cone on the spectra of the coefficient
algebras. -/
noncomputable def specCone (E : InductionData.{u}) : Cone E.specDiagram :=
  Scheme.Spec.mapCone (Limits.coneOfCoconeLeftOp E.algCocone)

@[simp] lemma specDiagram_map {T T' : E.Stage} (f : T ⟶ T') :
    E.specDiagram.map f = Spec.map f.algHom := rfl

lemma specCone_π_app (E : InductionData.{u}) (T : E.Stage) :
    E.specCone.π.app T = Spec.map T.toSectionsV := rfl

/-- `Spec Γ(X, V)` is the limit of the spectra of the coefficient
algebras. -/
noncomputable def isLimitSpecCone (E : InductionData.{u}) : IsLimit E.specCone :=
  isLimitOfPreserves Scheme.Spec
    (Limits.isLimitConeOfCoconeLeftOp E.algOp E.isColimitAlgCocone)

@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ (E : InductionData.{u}) :
    E.hV.isoSpec.inv ≫ E.V.toSpecΓ = 𝟙 _ := by
  rw [← IsAffineOpen.isoSpec_hom E.hV, Iso.inv_hom_id]

set_option maxHeartbeats 400000 in
-- Naturality has to identify the `Spec A`-chart of the pushout defining the stage scheme
-- with the preimage of `chartV`, for every stage below `T₀`.
/-- The `Spec A`-chart of a stage scheme is `Spec A`, compatibly with the transition
morphisms:

```
  Spec A  ────≅────▶ Sⱼ ⊓ chartV
  │                      │
  ▼                      ▼
  Spec A' ────≅────▶ Sⱼ' ⊓ chartV
```
-/
noncomputable def chartVIso (E : InductionData.{u}) (T₀ : E.Stage) :
    Over.forget T₀ ⋙ E.specDiagram ≅ opensDiagram E.stageDiagram T₀ T₀.chartV :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inr (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))
      (by rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Opens.opensRange_ι, Stage.preimage_chartV S.hom, Stage.chartV_def]))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Functor.comp_map, Over.forget_map, specDiagram_map, Category.assoc,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensDiagram_map_ι,
        IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inr_stageDiagram_map])

/-- The restriction of the stage cone to the `Spec A`-chart is a limit
cone. -/
noncomputable def isLimitOpensConeChartV (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV) :=
  IsLimit.equivOfNatIsoOfIso (E.chartVIso T₀)
    (E.specCone.whisker (Over.forget T₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV)
    (Cone.ext (E.hV.isoSpec.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, chartVIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, stageCone_π_app]
      rw [Stage.Vι_fromX, Stage.fromV, isoSpec_inv_toSpecΓ_assoc]
      exact congrArg (fun g ↦ g ≫ pushout.inr (E.Wι S.left.j) S.left.toSpec)
        (specCone_π_app E S.left)))
    ((Functor.Initial.isLimitWhiskerEquiv _ E.specCone).symm E.isLimitSpecCone)

/-- The two charts of a stage scheme, as a family indexed by `Bool`. -/
noncomputable def charts (E : InductionData.{u}) (T₀ : E.Stage) (b : Bool) :
    (E.stageDiagram.obj T₀).Opens :=
  bif b then T₀.chartU else T₀.chartV

@[simp] lemma charts_true (E : InductionData.{u}) (T₀ : E.Stage) :
    E.charts T₀ true = T₀.chartU := rfl

@[simp] lemma charts_false (E : InductionData.{u}) (T₀ : E.Stage) :
    E.charts T₀ false = T₀.chartV := rfl

/-- The stage cone is a limit cone: its restrictions to the two charts of a
stage scheme and to their overlap are limit cones. -/
noncomputable def isLimitStageConeOfStage (E : InductionData.{u}) (T₀ : E.Stage) :
    IsLimit E.stageCone := by
  refine isLimitOfIsLimitOpensCone E.stageDiagram E.stageCone T₀ (E.charts T₀) ?_
    (fun b ↦ ?_) ?_
  · rw [iSup_bool_eq]
    exact T₀.chartU_sup_chartV
  · cases b
    exacts [E.isLimitOpensConeChartV T₀, E.isLimitOpensConeChartU T₀]
  · rintro (_ | _) (_ | _) hne
    · exact absurd rfl hne
    · rw [charts_false, charts_true, inf_comm]
      exact E.isLimitOpensConeInter T₀
    · rw [charts_true, charts_false]
      exact E.isLimitOpensConeInter T₀
    · exact absurd rfl hne

/-- The stage cone is a limit cone. -/
noncomputable def isLimitStageCone (E : InductionData.{u}) : IsLimit E.stageCone :=
  E.isLimitStageConeOfStage (Classical.arbitrary E.Stage)

/-- The Noetherian approximation of `X = U ∪ V` extending a given approximation of `U`
across the affine open `V`. This is the one-affine-open step of the induction in the proof
of Stacks Project Tag 07RN; for its statement free of the auxiliary data of an
`InductionData`, see `AlgebraicGeometry.Scheme.NoetherianApproximation.sup`. -/
noncomputable def approximation (E : InductionData.{u}) : E.X.NoetherianApproximation where
  I := E.Stage
  D := E.stageDiagram
  locallyOfFiniteType_obj _ := inferInstance
  compactSpace_obj _ := inferInstance
  isAffineHom_map _ := inferInstance
  π := E.stageCone.π
  isLimit := E.isLimitStageCone

end InductionData

end Scheme.NoetherianApproximation

open Scheme.NoetherianApproximation

/-- **The induction step of absolute Noetherian approximation**: a Noetherian
approximation of a quasi-compact open `U` of a quasi-separated scheme extends to a
Noetherian approximation of `U ⊔ V` for every affine open `V`. The approximating schemes of
`U ⊔ V` are the gluings of the approximating schemes `Dⱼ` of `U` with the spectra of
suitable finitely generated subalgebras of `Γ(X, V) ×_{Γ(U ⊓ V)} Γ(Wⱼ)`, see
`AlgebraicGeometry.Scheme.NoetherianApproximation.InductionData.approximation`.

This is the one-affine-open step of the induction in the proof of Stacks Project Tag 07RN;
the induction itself is `AlgebraicGeometry.Scheme.NoetherianApproximation.finsetSup`. -/
noncomputable def Scheme.NoetherianApproximation.sup {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {U V : X.Opens} (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (N₀ : U.toScheme.NoetherianApproximation) :
    (U ⊔ V : X.Opens).toScheme.NoetherianApproximation := by
  classical
  set Y : X.Opens := U ⊔ V with hYdef
  have : QuasiSeparatedSpace Y.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ Y.2).mp (.of_quasiSeparatedSpace _)
  set U' : Y.toScheme.Opens := Y.ι ⁻¹ᵁ U with hU'def
  set V' : Y.toScheme.Opens := Y.ι ⁻¹ᵁ V with hV'def
  have hUV : U' ⊔ V' = ⊤ := by
    rw [hU'def, hV'def, ← Scheme.Hom.preimage_sup, ← hYdef, Scheme.Opens.ι_preimage_self]
  have hV'aff : IsAffineOpen V' := by
    refine hV.preimage_of_isOpenImmersion Y.ι ?_
    rw [Scheme.Opens.opensRange_ι]
    exact le_sup_right
  -- the approximation of `U`, transported to the open `U'` of `Y`
  have hrange : Set.range (X.homOfLE (le_sup_left : U ≤ Y)) = Set.range (Scheme.Opens.ι U') := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
      Scheme.opensRange_homOfLE, Scheme.Opens.opensRange_ι]
  have N : U'.toScheme.NoetherianApproximation :=
    N₀.ofIso (IsOpenImmersion.isoOfRangeEq _ _ hrange)
  -- the intersection `U' ⊓ V'` is quasi-compact
  have hinfc : IsCompact (((U ⊓ V : X.Opens)) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV.isCompact
  have hUVc : IsCompact ((U' ⊓ V' : Y.toScheme.Opens) : Set Y.toScheme) := by
    rw [show (U' ⊓ V' : Y.toScheme.Opens) = Y.ι ⁻¹ᵁ (U ⊓ V) by
      rw [hU'def, hV'def, Scheme.Hom.preimage_inf]]
    refine Y.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left.trans le_sup_left
  have hUVc' : IsCompact ((U'.ι ⁻¹ᵁ V' : U'.toScheme.Opens) : Set U'.toScheme) := by
    rw [show (U'.ι ⁻¹ᵁ V' : U'.toScheme.Opens) = U'.ι ⁻¹ᵁ (U' ⊓ V') by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]]
    refine U'.ι.isOpenEmbedding.isInducing.isCompact_preimage' hUVc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  choose i₀ W₀ hW₀c hW₀ using exists_preimage_eq N.D (Cone.mk _ N.π) N.isLimit _ hUVc'
  -- the generators of the intersection
  choose t ht using hV'aff.exists_finset_basicOpen_eq hUVc inf_le_right
  have hcov : (U' ⊓ V' : Y.toScheme.Opens) =
      ⨆ x : {x // x ∈ t}, Y.toScheme.basicOpen (x : Γ(Y.toScheme, V')) := by
    rw [ht]
    exact iSup_subtype' (p := fun x : Γ(Y.toScheme, V') ↦ x ∈ t)
      (f := fun x _ ↦ Y.toScheme.basicOpen x)
  exact InductionData.approximation
    { X := Y.toScheme, U := U', V := V', sup_eq_top := hUV, hV := hV'aff, N := N, i₀ := i₀,
      W₀ := W₀, hW₀c := hW₀c, hW₀ := hW₀, σ := {x // x ∈ t},
      b := fun x ↦ (x : Γ(Y.toScheme, V')), inf_eq_iSup_basicOpen := hcov }

/-- **Extending a Noetherian approximation across finitely many affine opens** (Stacks
Project Tag 07RN): a Noetherian approximation of a quasi-compact open `U` of a
quasi-separated scheme `X` extends to a Noetherian approximation of `U` together with any
finite family of affine opens of `X`, by induction on the family.

Stacks 07RN states in addition that the two systems can be taken compatibly — an
order-preserving map of index sets and open subschemes of the new stages isomorphic to the
old ones — which this statement does not record.

Absolute Noetherian approximation is the case `U = ⊥`, see
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`. -/
@[stacks 07RN]
noncomputable def Scheme.NoetherianApproximation.finsetSup {X : Scheme.{u}}
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X))
    (N : U.toScheme.NoetherianApproximation) :
    ∀ (s : Finset X.Opens), (∀ V ∈ s, IsAffineOpen V) →
      (U ⊔ s.sup id : X.Opens).toScheme.NoetherianApproximation := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    refine fun hs ↦ if h : s = ∅ then ?_ else ?_
    · subst h
      simpa using N
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have ha : hne.choose ∈ s := hne.choose_spec
      have M := ih _ (Finset.erase_ssubset ha) fun W hW ↦ hs W (Finset.mem_of_mem_erase hW)
      have hcpt : IsCompact ((U ⊔ (s.erase hne.choose).sup id : X.Opens) : Set X) := by
        rw [TopologicalSpace.Opens.coe_sup]
        exact hU.union (TopologicalSpace.Opens.isCompact_finset_sup _
          fun W hW ↦ (hs W (Finset.mem_of_mem_erase hW)).isCompact)
      have hsup : s.sup id = hne.choose ⊔ (s.erase hne.choose).sup id := by
        conv_lhs => rw [← Finset.insert_erase ha]
        rw [Finset.sup_insert, id]
      have heq : ((U ⊔ (s.erase hne.choose).sup id) ⊔ hne.choose : X.Opens) = U ⊔ s.sup id := by
        simp [hsup, sup_comm, sup_left_comm]
      exact heq ▸ Scheme.NoetherianApproximation.sup hcpt (hs _ ha) M

/-- **Absolute Noetherian approximation** (Stacks Project Tag 01ZA): every quasi-compact
quasi-separated scheme is the limit of a cofiltered system of schemes of finite type over
`ℤ` with affine transition morphisms.

The affine case is `AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`. The
general case is the empty-open case of
`AlgebraicGeometry.Scheme.NoetherianApproximation.finsetSup`, an induction over a finite
affine cover whose steps extend an approximation of a quasi-compact open across one more
affine open (`AlgebraicGeometry.Scheme.NoetherianApproximation.sup`).
(Blueprint: `lemma:nagata-absolute-noetherian-approximation-exists`.) -/
@[stacks 01ZA]
theorem Scheme.nonempty_noetherianApproximation (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty S.NoetherianApproximation := by
  classical
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    S.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) (by simpa using isCompact_univ)
  have : IsAffine ((⊥ : S.Opens).toScheme) := isAffineOpen_bot S
  have N := Scheme.NoetherianApproximation.finsetSup (U := (⊥ : S.Opens)) (by simp)
    (Scheme.NoetherianApproximation.ofIsAffine _) hUsfin.toFinset
    (fun V hV ↦ hUsB (hUsfin.mem_toFinset.mp hV))
  rw [bot_sup_eq, Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at N
  exact ⟨N.ofIso S.topIso⟩

end AlgebraicGeometry
