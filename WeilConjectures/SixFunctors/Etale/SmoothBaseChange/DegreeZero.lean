/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConnectedFibres
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomologyZero
public import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow

/-!
# Degree-zero flat base change

The base-change map is an isomorphism in degree zero for a morphism `p : X ⟶ S` which is
flat, locally of finite presentation and has geometrically reduced fibres, with *no* torsion
hypothesis on the coefficient sheaf. Smooth morphisms satisfy these hypotheses, so this is
the starting point of the induction proving smooth base change.

The proof is étale-local on `X`: by `AlgebraicGeometry.exists_etaleCover_factorization` one
may assume `p` factors as `U ⟶ V ⟶ S` with `V ⟶ S` étale and `U ⟶ V` quasi-compact flat
with geometrically connected fibres, and then both sides evaluate to `F(V ×_S T)` because for
such a morphism the global sections of an inverse image agree with the global sections
downstairs [Stacks 0A3H]; the latter is
`AlgebraicGeometry.Etale.isIso_upperStarSectionsMap` in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConnectedFibres`.

The argument is carried out for the underived base-change map
`AlgebraicGeometry.Etale.baseChangeMap`, whose adjoint under `p^* ⊣ p_*` is
`g_* F ⟶ g_* e_* e^* F ≅ p_* h_* e^* F`, so that its sections can be computed. It is
transferred to
the degree-zero homology of the derived base-change map of
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` by
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_zero`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_flat`: the underived base-change map
  is an isomorphism for `p` flat, locally of finite presentation with geometrically reduced
  fibres (blueprint `sbc-lem-degree-zero-flat-base-change`).
- `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_zero`: in degree zero the
  derived base-change map is the underived one.
- `AlgebraicGeometry.Etale.baseChangeProperty_zero`: degree-zero base change for a flat,
  locally finitely presented morphism with geometrically reduced fibres.
- `AlgebraicGeometry.Etale.baseChangeProperty_zero_of_smooth`: the smooth case, a corollary
  of the previous statement and the instance
  `AlgebraicGeometry.Smooth.geometricallyReduced`.
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero` and
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_smooth`: the same statements
  after every base change of `p`.

## References

- Stacks Project, Lemma 59.87.2, <https://stacks.math.columbia.edu/tag/0EYS>
- Stacks Project, Lemma 59.87.1, <https://stacks.math.columbia.edu/tag/0EZX>
- Stacks Project, More on Morphisms, Lemma 37.46.3, <https://stacks.math.columbia.edu/tag/0EY5>
- Stacks Project, Tag `0A3H`, <https://stacks.math.columbia.edu/tag/0A3H>
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

section BaseChangeMap

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The square isomorphism `e_* ⋙ g_* ≅ h_* ⋙ p_*` of pushforwards, written with the diagonal
`h ≫ p` instead of `e ≫ g`. -/
lemma Etale.squareLowerStarIso_eq (sq : CommSq e h g p) :
    Etale.squareLowerStarIso A sq =
      Etale.lowerStarComp A e g (h ≫ p) sq.w.symm ≪≫ (Etale.lowerStarComp A h p).symm := by
  have key (d₁ d₂ : Y ⟶ S) (hd : d₁ = d₂) (w₁ w₂ w₃ w₄) :
      Etale.lowerStarComp A e g d₁ w₁ ≪≫ (Etale.lowerStarComp A h p d₁ w₂).symm =
        Etale.lowerStarComp A e g d₂ w₃ ≪≫ (Etale.lowerStarComp A h p d₂ w₄).symm := by
    subst hd
    rfl
  exact key _ _ sq.w _ _ _ _

/-- The base-change map is compatible with the maps `Etale.upperStarSectionsMap` on both sides
of the square: for `φ : W ⟶ V ×_S X` and the induced morphism
`φ' : W ×_X Y ⟶ (V ×_S T) ×_T Y` of étale `Y`-schemes, the composite
`(g_* F)(V) ⟶ (p^* g_* F)(W) ⟶ (h_* e^* F)(W)` is the map
`F(V ×_S T) ⟶ (e^* F)(W ×_X Y)` attached to `φ'`. The morphism `φ'` is pinned down by its
first component `hφ'`. This is the computation underlying Step 2 of the blueprint proof of
`sk-prop-deg0`. -/
lemma Etale.upperStarSectionsMap_comp_baseChangeMap_app (sq : CommSq e h g p)
    (F : Sheaf T.smallEtaleTopology A) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (φ' : (MorphismProperty.Over.pullback @Etale ⊤ h).obj W ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ e).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))
    (hφ' : φ'.left ≫ pullback.fst _ e ≫ pullback.fst V.hom g =
      pullback.fst W.hom h ≫ φ.left ≫ pullback.fst V.hom p) :
    Etale.upperStarSectionsMap A p ((g)_*[A].obj F) φ ≫
        ((Etale.baseChangeMap A sq).app F).hom.app (op W) =
      Etale.upperStarSectionsMap A e F φ' := by
  have key : ((p)^*[A].obj ((g)_*[A].obj F)).obj.map φ.op ≫
      ((Etale.baseChangeMap A sq).app F).hom.app (op W) =
      ((Etale.baseChangeMap A sq).app F).hom.app _ ≫
        ((h)_*[A].obj ((e)^*[A].obj F)).obj.map φ.op :=
    ((Etale.baseChangeMap A sq).app F).hom.naturality φ.op
  simp only [Etale.upperStarSectionsMap, Category.assoc]
  rw [key, ← Category.assoc]
  have h2 : (Etale.upperStarLowerStarAdjunction A p).unit.app ((g)_*[A].obj F) ≫
      (p)_*[A].map ((Etale.baseChangeMap A sq).app F) =
      (g)_*[A].map ((Etale.upperStarLowerStarAdjunction A e).unit.app F) ≫
        (Etale.lowerStarComp A e g (h ≫ p) sq.w.symm).hom.app _ ≫
        (Etale.lowerStarComp A h p).inv.app _ := by
    rw [Etale.unit_map_baseChangeMap_app, Etale.squareLowerStarIso_eq]
    rfl
  have h3 := congr_arg (fun f ↦ f.hom.app (op V)) h2
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h3
  erw [h3]
  simp only [Category.assoc, Etale.lowerStarComp]
  rw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Etale.lowerStar_map_hom_app,
    Etale.lowerStar_obj_val_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  dsimp only [Quiver.Hom.unop_op]
  ext : 1
  have hw := MorphismProperty.Over.w φ'
  simp only [MorphismProperty.Over.pullback_obj_hom] at hw hφ' ⊢
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hφ']
      simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc]
    · simp only [Category.assoc]
      simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd]
      simp only [limit.lift_π_assoc, PullbackCone.mk_π_app, Category.comp_id]
      erw [pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.lift_snd_assoc, pullback.condition]
      rw [reassoc_of% hw]
  · simp only [Category.assoc]
    simp only [Functor.id_obj, Functor.const_obj_obj, Iso.symm_hom, Iso.symm_inv,
      MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id, Category.comp_id,
      MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd]
    simp only [pullback.map, limit.lift_π, PullbackCone.mk_π_app, Category.comp_id]
    erw [pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [hw]

/-- Let `φ : W ⟶ V ×_S X` be a morphism of étale `X`-schemes, so that `W ⟶ X ⟶ S` factors
through `q : W ⟶ V`, and let `c : W ×_X Y ⟶ V ×_S T` be the induced morphism. If the square
`(e, h, g, p)` is Cartesian, then `c` is the base change of `q` along `V ×_S T ⟶ V`. -/
lemma Etale.isPullback_pullbackFst_of_hom (sq : IsPullback e h g p) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (c : pullback W.hom h ⟶ pullback V.hom g)
    (hc₁ : c ≫ pullback.fst V.hom g = pullback.fst W.hom h ≫ φ.left ≫ pullback.fst V.hom p)
    (hc₂ : c ≫ pullback.snd V.hom g = pullback.snd W.hom h ≫ e) :
    IsPullback c (pullback.fst W.hom h) (pullback.fst V.hom g)
      (φ.left ≫ pullback.fst V.hom p) := by
  have hφ : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
  refine IsPullback.of_right ?_ (by rw [hc₁])
    (IsPullback.of_hasPullback V.hom g).flip
  rw [hc₂, Category.assoc, pullback.condition, reassoc_of% hφ]
  exact (IsPullback.of_hasPullback W.hom h).flip.paste_horiz sq

end BaseChangeMap

variable (Λ : Type (u + 1)) [CommRing Λ]

section DegreeZero

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Blueprint `sbc-lem-degree-zero-flat-base-change`: degree-zero flat base change.

For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` flat, locally of finite presentation and with geometrically reduced fibres, the
degree-zero base-change map `p⁻¹ g_* F ⟶ h_* e⁻¹ F` of
`AlgebraicGeometry.Etale.baseChangeMap` is an isomorphism at every sheaf `F` of
`Λ`-modules on `T_ét`; no hypothesis on `g` is needed.

Every étale `X`-scheme `W₀` is covered, by `AlgebraicGeometry.exists_etaleCover_factorization`
applied to `W₀ ⟶ S`, by charts `W` for which `W ⟶ S` factors as `W ⟶ V ⟶ S` with `V ⟶ S` étale
and `W ⟶ V` flat, of finite presentation, with geometrically connected fibres. On such
a chart both sides have sections `F(V ×_S T)`, by
`AlgebraicGeometry.Etale.isIso_upperStarSectionsMap` applied to `W ⟶ V` and to its base change
`W ×_X Y ⟶ V ×_S T`, compatibly with the base-change map by
`AlgebraicGeometry.Etale.upperStarSectionsMap_comp_baseChangeMap_app`. Since the
charts generate a covering sieve of every object, the base-change map is an isomorphism by
`CategoryTheory.Sheaf.isIso_of_isIso_app_of_generate_mem`. -/
@[stacks 0EYS]
theorem Etale.isIso_baseChangeMap_app_of_flat [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.baseChangeMap _ sq.toCommSq).app F) := by
  refine Sheaf.isIso_of_isIso_app_of_generate_mem _ (forget (ModuleCat.{u + 1} Λ)) _ fun W₀ ↦ ?_
  have : Etale W₀.hom := W₀.prop
  have : GeometricallyReduced (W₀.hom ≫ p) := GeometricallyReduced.comp_of_etale _ _
  obtain ⟨ι, U, a, V, q, r, ha, hcov, hr, hq₁, -, hq₃, -, hq₄, -, -, -, hfac⟩ :=
    exists_etaleCover_factorization (W₀.hom ≫ p)
  let W (i : ι) : X.Etale := Scheme.Etale.mk (a i ≫ W₀.hom)
  let ι' (i : ι) : W i ⟶ W₀ := MorphismProperty.Over.homMk (a i)
  refine ⟨Presieve.ofArrows W ι', (ofArrows_mem_smallEtaleTopology_iff ι').2 ?_, ?_⟩
  · refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := hcov x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  · rintro _ _ ⟨i⟩
    let Vi : S.Etale := Scheme.Etale.mk (r i)
    let φ : W i ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj Vi :=
      MorphismProperty.Over.homMk (pullback.lift (q i) (a i ≫ W₀.hom)
        (by rw [Category.assoc]; exact hfac i)) (by simp [W])
    have hq : φ.left ≫ pullback.fst Vi.hom p = q i := by simp [φ]
    have : Flat (φ.left ≫ pullback.fst Vi.hom p) := hq ▸ hq₁ i
    have : QuasiCompact (φ.left ≫ pullback.fst Vi.hom p) := hq ▸ inferInstance
    have : GeometricallyConnected (φ.left ≫ pullback.fst Vi.hom p) := hq ▸ hq₄ i
    let c : pullback (W i).hom h ⟶ pullback Vi.hom g :=
      pullback.lift (pullback.fst (W i).hom h ≫ φ.left ≫ pullback.fst Vi.hom p)
        (pullback.snd (W i).hom h ≫ e) (by
          have hφ : φ.left ≫ pullback.snd Vi.hom p = (W i).hom := MorphismProperty.Over.w φ
          simp only [Category.assoc]
          rw [pullback.condition, reassoc_of% hφ, pullback.condition_assoc, sq.w])
    have hc := Etale.isPullback_pullbackFst_of_hom sq φ c (by simp [c]) (by simp [c])
    let φ' : (MorphismProperty.Over.pullback @Etale ⊤ h).obj (W i) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ e).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ g).obj Vi) :=
      MorphismProperty.Over.homMk (pullback.lift c (pullback.snd (W i).hom h) (by simp [c]))
        (by simp)
    have hφ' : φ'.left ≫ pullback.fst _ e = c := by simp [φ']
    have : Flat (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have : QuasiCompact (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have : GeometricallyConnected (φ'.left ≫ pullback.fst _ e) :=
      hφ' ▸ MorphismProperty.of_isPullback hc.flip inferInstance
    have h₁ := Etale.isIso_upperStarSectionsMap Λ p ((g)_*[_].obj F) φ
    have h₂ := Etale.isIso_upperStarSectionsMap Λ e F φ'
    rw [← Etale.upperStarSectionsMap_comp_baseChangeMap_app _ sq.toCommSq F φ φ'
      (by rw [reassoc_of% hφ']; simp [c])] at h₂
    exact IsIso.of_isIso_comp_left (Etale.upperStarSectionsMap _ p ((g)_*[_].obj F) φ) _

/-- In degree zero the base-change map `AlgebraicGeometry.Etale.baseChangeHomologyMap` of the
derived base-change morphism is, up to isomorphism of arrows, the underived base-change map
`AlgebraicGeometry.Etale.baseChangeMap`: the degree-zero homology of
`p^*(R g_* F[0])` is `p^* g_* F` and that of `R h_*(e^*(F[0]))` is `h_* e^* F`, the pullbacks
being exact and `g_*`, `h_*` left exact, and under these identifications the units and counits
of the derived adjunctions restrict in degree zero to those of the underived adjunctions. -/
theorem Etale.nonempty_arrowIso_baseChangeHomologyMap_zero (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk (Etale.baseChangeHomologyMap Λ sq 0 F) ≅
      Arrow.mk ((Etale.baseChangeMap _ sq.toCommSq).app F)) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans_eq,
    Arrow.mk_whiskerLeft_whiskerRight_app, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  let A := ModuleCat.{u + 1} Λ
  let K₀ : CochainComplex.Plus (Sheaf T.smallEtaleTopology A) :=
    ⟨(CochainComplex.singleFunctor _ 0).obj F, 0, inferInstance⟩
  let Kh := (HomotopyCategory.Plus.quotient _).obj K₀
  let e₀ : (DerivedCategory.Plus.singleFunctor _ 0).obj F ≅ DerivedCategory.Plus.Qh.obj Kh :=
    DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫
      (DerivedCategory.quotientCompQhIso (Sheaf T.smallEtaleTopology A)).symm.app
        ((CochainComplex.singleFunctor _ 0).obj F))
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology A) 0
  have : K₀.obj.IsStrictlyGE 0 := (inferInstance :
    ((CochainComplex.singleFunctor (Sheaf T.smallEtaleTopology A) 0).obj F).IsStrictlyGE 0)
  have : ((e)^*[A].mapCochainComplexPlus.obj K₀).obj.IsStrictlyGE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (((e)^*[A].mapHomologicalComplex _).obj K₀.obj) 0)
  have h₁ : IsIso (H.map (((p)^*[A]).mapDerivedCategoryPlus.map
      (((g)_*[A]).rightDerivedFunctorPlusUnit.app Kh))) := by
    have := ((g)_*[A]).isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app K₀
    exact (NatIso.isIso_map_iff (((p)^*[A]).mapDerivedCategoryPlusHomologyFunctorIso 0) _).1
      (inferInstanceAs (IsIso ((p)^*[A].map _)))
  have h₂ : IsIso (H.map (((h)_*[A]).rightDerivedFunctorPlusUnit.app
      (((e)^*[A]).mapHomotopyCategoryPlus.obj Kh) ≫ ((h)_*[A]).rightDerivedFunctorPlus.map
        ((((e)^*[A]).mapDerivedCategoryPlusFactorsh).inv.app Kh))) := by
    rw [H.map_comp]
    have := ((h)_*[A]).isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app
      ((e)^*[A].mapCochainComplexPlus.obj K₀)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this (by infer_instance)
  exact ⟨Arrow.isoMapApp _ H e₀ ≪≫
    Arrow.isoOfFac H _ _ _ _ _ (Etale.derivedBaseChangeMapPlus_fac_app A sq.toCommSq Kh) ≪≫
    NatTrans.homologyFunctorMapQhMapArrowIso _ K₀ 0 ≪≫
    NatTrans.homologyMapMapHomologicalComplexSingleArrowIso _ F⟩

end DegreeZero

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Blueprint `sk-prop-deg0`: Degree-zero flat base change.

For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and `p` flat, locally of finite presentation and with
geometrically reduced fibres, the degree-zero base-change map `p⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for *every* sheaf `F` of `Λ`-modules on `T_ét`: no torsion hypothesis is needed in
degree zero. This is `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_flat`, transferred
to the derived base-change map by
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_zero`. -/
@[stacks 0EYS]
theorem Etale.baseChangeProperty_zero [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] :
    Etale.BaseChangeProperty Λ p 0 := by
  intro T Y g e h _ _ sq F
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_zero Λ sq F
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff φ).2
    (Etale.isIso_baseChangeMap_app_of_flat Λ sq F)

/-- The smooth case of `AlgebraicGeometry.Etale.baseChangeProperty_zero`: a smooth morphism
is flat and locally of finite presentation and its geometric fibres are smooth varieties,
hence reduced, so `BC(p, Λ, 0)` holds for `p` smooth. This is the degree-zero start of the
induction in the smooth base change theorem. -/
theorem Etale.baseChangeProperty_zero_of_smooth [Smooth p] :
    Etale.BaseChangeProperty Λ p 0 :=
  Etale.baseChangeProperty_zero Λ p

/-- `AlgebraicGeometry.Etale.baseChangeProperty_zero` holds universally: flatness, local finite
presentation and geometric reducedness of the fibres are stable under base change. -/
theorem Etale.universalBaseChangeProperty_zero [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] :
    Etale.UniversalBaseChangeProperty Λ p 0 := by
  intro _ _ _ _ p' hp
  have : Flat p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  have : LocallyOfFinitePresentation p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  have : GeometricallyReduced p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  intro _ _ g e h _ _ sq F
  exact Etale.baseChangeProperty_zero Λ p' g e h sq F

/-- The smooth case of `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`: the base case
of the induction on `q` in the smooth base change theorem. -/
theorem Etale.universalBaseChangeProperty_zero_of_smooth [Smooth p] :
    Etale.UniversalBaseChangeProperty Λ p 0 :=
  Etale.universalBaseChangeProperty_zero Λ p

end AlgebraicGeometry
