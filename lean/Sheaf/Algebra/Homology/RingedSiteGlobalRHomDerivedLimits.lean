module

public import Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel
import Sheaf.Algebra.Homology.RingedSiteGlobalRHomCoefficientModel
import Sheaf.Algebra.Homology.RingedSiteGlobalRHomResolvedTowerModels
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! Models used in the global derived Hom and inverse-limit comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z u k

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

section Comparison
variable {S B B' D D' : Type*} [Category* S] [Category* B] [Category* B']
  [Category* D] [Category* D'] [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ B']
  (U : S ⥤ (ℕᵒᵖ ⥤ B)) (Q : B ⥤ D) (Q' : B' ⥤ D') (H : B ⥤ B') (F : D ⥤ D')
  (P : ObjectProperty B)
  (β : ∀ (I : B) (_ : P I), Q'.obj (H.obj I) ≅ F.obj (Q.obj I))
  (hβ : ∀ (I I' : B) (hI : P I) (hI' : P I') (f : I ⟶ I'),
    Q'.map (H.map f) ≫ (β I' hI').hom = (β I hI).hom ≫ F.map (Q.map f))
  (hlim : ∀ I : S, P (limit (U.obj I)))
  (hpost : ∀ I : S, IsIso (limit.post (U.obj I) H))

private def comparisonIso : U ⋙ lim ⋙ Q ⋙ F ≅
    U ⋙ (Functor.whiskeringRight _ _ _).obj H ⋙ lim ⋙ Q' :=
  NatIso.ofComponents (fun I ↦ by
    have := hpost I
    exact (β _ (hlim I)).symm ≪≫ asIso (Q'.map (limit.post (U.obj I) H))) (by
      intro I I' f
      let u := U.map f
      have hn := hβ _ _ (hlim I) (hlim I') (lim.map u)
      change F.map (Q.map (lim.map u)) ≫
          ((β _ (hlim I')).inv ≫ Q'.map (limit.post (U.obj I') H)) =
        ((β _ (hlim I)).inv ≫ Q'.map (limit.post (U.obj I) H)) ≫
          Q'.map (lim.map (Functor.whiskerRight u H))
      have hn' : F.map (Q.map (lim.map u)) ≫ (β _ (hlim I')).inv =
          (β _ (hlim I)).inv ≫ Q'.map (H.map (lim.map u)) := by
        apply (Iso.comp_inv_eq _).mpr
        rw [Category.assoc, hn]
        exact (Iso.inv_hom_id_assoc _ _).symm
      have hp : H.map (lim.map u) ≫ limit.post (U.obj I') H =
          limit.post (U.obj I) H ≫ lim.map (Functor.whiskerRight u H) :=
        limit.map_post (α := u) H
      rw [← Category.assoc, hn', Category.assoc, ← Q'.map_comp, hp, Q'.map_comp]
      exact (Category.assoc _ _ _).symm)

private theorem comparisonIso_π
    (hobj : ∀ (I : S) (n : ℕ), P ((U.obj I).obj (op n))) (I : S) (n : ℕ) :
    (comparisonIso U Q Q' H F P β hβ hlim hpost).hom.app I ≫
        Q'.map (limit.π (U.obj I ⋙ H) (op n)) ≫
        (β _ (hobj I n)).hom = F.map (Q.map (limit.π (U.obj I) (op n))) := by
  change ((β _ (hlim I)).inv ≫ Q'.map (limit.post (U.obj I) H)) ≫
    Q'.map (limit.π (U.obj I ⋙ H) (op n)) ≫ (β _ (hobj I n)).hom = _
  rw [Category.assoc, ← Q'.map_comp_assoc, limit.post_π]
  rw [hβ _ _ (hlim I) (hobj I n) (limit.π (U.obj I) (op n))]
  exact Iso.inv_hom_id_assoc _ _

end Comparison

private theorem towerGrothendieck
    (D : Type u) [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{k} D] :
    IsGrothendieckAbelian.{k} (ℕᵒᵖ ⥤ D) := by
  let G := separator D
  have hG := isSeparator_separator D
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint D j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight D j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ D) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{k, k} (ℕᵒᵖ ⥤ D) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{k, k} (ℕᵒᵖ ⥤ D) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

section LimitModel
variable {D : Type u} [Category.{v} D] [Abelian D] [HasLimitsOfShape ℕᵒᵖ D]

private theorem baseLimit_additive : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

attribute [local instance] baseLimit_additive

private def limitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private def limitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    IsLimit (limitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private theorem limit_isKInjective (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    [I.IsKInjective] : CochainComplex.IsKInjective (limit I.asFunctor) := by
  have : (Functor.const ℕᵒᵖ : D ⥤ (ℕᵒᵖ ⥤ D)).Additive := by
    refine ⟨?_⟩
    intro X Y f g
    rfl
  have := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim).preservesKInjectiveComplexes
  let e : ((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
    (limitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)
  exact CochainComplex.isKInjective_of_iso e

end LimitModel

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

attribute [local irreducible] globalHom representative

set_option linter.unusedVariables false in
set_option maxHeartbeats 1200000 in
-- Assemble comparison types over the module-sheaf category without unfolding its data.
/-- Global RHom preserves resolution-derived inverse limits, with the actual limiting
cone, naturally for maps of strict towers; its cohomology computes all derived Homs.

Source: Stacks 0B6E and 0D3F; resolution and Roos normalization in Tag 0941
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits).

Proof:
1. Choose a K-flat representative of E (lem-pc-kflat-resolution). The tensor-Hom
adjunction and native symmetry (lem-sf-ringed-derived-tensor-hom-adjunction and
lem-sf-ringed-derived-native-tensor) identify internal RHom with Hom into a
K-injective representative. The sections model
(lem-sfb-derived-internal-hom-sections-model), using def-pur-hom-complex and
lem-pur-hom-kflat-into-kinjective, identifies global RHom with representative L.
All constructions are A-linear by postmultiplication through φ; the same comparison
works for any representative L by quasi-isomorphism invariance.
2. Resolve a strict tower by a K-injective complex of injective towers
(lem-pur-injective-tower-roos-shifts and
lem-weil-pbc-ringed-strict-tower-homotopy-limit). Evaluations are K-injective,
transitions split in every degree, and the ordinary limit represents Rlim.
The constant-tower functor is exact (lem-weil-tower-category-levelwise-abelian),
so its right adjoint lim preserves K-injectives
(lem-weil-pbc-right-adjoint-preserves-kinjective).
3. In degree q the representative has product terms Hom(L^p,I^(p+q)).
The universal property of inverse limits and interchange of products identify
representative(lim I) with lim representative(I), with the same differential and
projections. This yields the natural isomorphism α and its projection formula.
4. The resolved transitions split, so transitions of these Hom groups are surjective.
The endomorphism 1-s on their product is surjective: recursively lift x_n-b_n to
choose x_(n+1). Its kernel is the ordinary limit. Apply
lem-weil-degreewise-epi-kernel-cocone-qis and lem-weil-strict-roos-comparison.
Products in A-modules are exact, and the normalized kernel-to-cone inclusion has
zero shifted component. It identifies this limit with the resolution-derived Rlim
and supplies exactly the Roos triangle and projection equations stated here.
5. Postcomposition commutes with every projection. Thus the construction is natural
on resolved towers. Maps and homotopies between resolutions induce the same derived
map by lem-weil-pbc-kinjective-hom-derived, so the projection-normalized comparison
is independent of the resolution and natural on original strict towers.
6. The sections-model cohomology formula gives the additive equivalences in every
integer degree. Its naturality and the postmultiplication action give the displayed
naturality and scalar equations. No boundedness or quasi-coherence is used. -/
theorem preserves_derived_limits
    (E : DerivedCategory (Modules.{c, v, max c v r} R))
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    (eL : DerivedCategory.Q.obj L ≅ E) :
    (∀ X : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) ℤ,
      ∃ (I : (resolvedProperty.{c, v, r} R).FullSubcategory) (q : X ⟶ I.obj), QuasiIso q) ∧
    ∃ (β : ∀ (I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (_hI : I.IsKInjective),
        DerivedCategory.Q.obj ((representative.{c, v, r, a} R A φ L).obj I) ≅
          (globalHom.{c, v, r, a, w, z} R A φ E).obj (DerivedCategory.Q.obj I))
      (α : limitGlobalHom.{c, v, r, a, w, z} R A φ E ≅ globalHomLimit.{c, v, r, a} R A φ L),
      (∀ (I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (hI : I.IsKInjective)
        (hI' : I'.IsKInjective) (f : I ⟶ I'),
        DerivedCategory.Q.map ((representative.{c, v, r, a} R A φ L).map f) ≫ (β I' hI').hom =
          (β I hI).hom ≫ (globalHom.{c, v, r, a, w, z} R A φ E).map (DerivedCategory.Q.map f)) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hLim : CochainComplex.IsKInjective (limit I.obj.asFunctor),
          α.hom.app I = (β (limit I.obj.asFunctor) hLim).inv ≫
            DerivedCategory.Q.map (limit.post I.obj.asFunctor
              (representative.{c, v, r, a} R A φ L))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦
            DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))),
        ∃ (p : DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor) ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
              (I.obj.asFunctor.obj (op n)))) ⟶
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor))⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
              (I.obj.asFunctor.map (homOfLE (Nat.le_succ n)).op))
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor)) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map
            (limit.π I.obj.asFunctor (op n))) ∧
      (∀ (I : (resolvedProperty.{c, v, r} R).FullSubcategory) (n : ℕ),
        ∃ hIn : CochainComplex.IsKInjective (I.obj.asFunctor.obj (op n)),
          α.hom.app I ≫ DerivedCategory.Q.map
              (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n)) ≫
              (β (I.obj.asFunctor.obj (op n)) hIn).hom =
            (globalHom.{c, v, r, a, w, z} R A φ E).map
              (DerivedCategory.Q.map (limit.π I.obj.asFunctor (op n)))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj
            (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))),
        ∃ (p : (globalHomLimit.{c, v, r, a} R A φ L).obj I ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n)))) ⟶
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I)⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.map
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).map
                (homOfLE (Nat.le_succ n)).op))
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.map
            (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n))) ∧
      ∃ e : ∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ),
          ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)) ≃+ (E ⟶ N⟦q⟧),
        (∀ (N N' : DerivedCategory (Modules.{c, v, max c v r} R)) (f : N ⟶ N') (q : ℤ)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N' q ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).map
            ((globalHom.{c, v, r, a, w, z} R A φ E).map f) x) = e N q x ≫ f⟦q⟧') ∧
        (∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ) (b : A)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N q (b • x) = (φ b) • e N q x) := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let : IsGrothendieckAbelian.{max c v r} (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) :=
    towerGrothendieck _
  have hres (X : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) ℤ) :
      ∃ (I : (resolvedProperty.{c, v, r} R).FullSubcategory) (q : X ⟶ I.obj),
        QuasiIso q := by
    let T := (CochainComplex.kInjectiveResolutionFunctor.{max c v r}
      (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R)).obj X
    have hT : resolvedProperty.{c, v, r} R T :=
      ⟨inferInstance, fun p ↦ inferInstance⟩
    exact ⟨⟨T, hT⟩, _,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) X).2⟩
  have hkinj (I : (resolvedProperty.{c, v, r} R).FullSubcategory) :
      CochainComplex.IsKInjective (limit I.obj.asFunctor) ∧
        ∀ n : ℕ, CochainComplex.IsKInjective (I.obj.asFunctor.obj (op n)) := by
    have : I.obj.IsKInjective := I.property.1
    exact ⟨limit_isKInjective I.obj,
      fun n ↦ tower_evaluation_isKInjective _ I.obj (op n)⟩
  obtain ⟨hpost, hsource, htarget⟩ :=
    resolved_tower_models.{c, v, r, a, w, z} R A φ L
  obtain ⟨β, hβ, e, henat, hescalar⟩ :=
    coefficient_model.{c, v, r, a, w, z} R A φ E L eL
  let U : (resolvedProperty.{c, v, r} R).FullSubcategory ⥤
      (ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, max c v r} R) ℤ) :=
    (resolvedProperty.{c, v, r} R).ι ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let H := representative.{c, v, r, a} R A φ L
  let F := globalHom.{c, v, r, a, w, z} R A φ E
  let P : ObjectProperty (CochainComplex (Modules.{c, v, max c v r} R) ℤ) :=
    fun I ↦ I.IsKInjective
  let α : limitGlobalHom.{c, v, r, a, w, z} R A φ E ≅
      globalHomLimit.{c, v, r, a} R A φ L :=
    comparisonIso U DerivedCategory.Q DerivedCategory.Q H F P β hβ
      (fun I ↦ (hkinj I).1) hpost
  refine ⟨hres, β, α, hβ, ?_, hsource, ?_, htarget, e, henat, hescalar⟩
  · intro I
    exact ⟨(hkinj I).1, rfl⟩
  · intro I n
    refine ⟨(hkinj I).2 n, ?_⟩
    exact comparisonIso_π U DerivedCategory.Q DerivedCategory.Q H F P β hβ
      (fun I ↦ (hkinj I).1) hpost (fun I n ↦ (hkinj I).2 n) I n

end CategoryTheory.RingedSiteGlobalRHom
