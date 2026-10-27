/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData
import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentHom
import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerFiniteFrame
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen

/-! # Normalized finite descent on connected abelian cover towers

Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2--5.1.4 and Corollary 5.1.5
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

private theorem connected_copies_map_constant (V W : Scheme.{u}) [ConnectedSpace W]
    (E : Type u) (s : W ⟶ V) (f : W ⟶ ∐ fun _ : E ↦ V)
    (hf : f ≫ Sigma.desc (fun _ : E ↦ 𝟙 V) = s) :
    ∃ e : E, f = s ≫ Sigma.ι (fun _ : E ↦ V) e := by
  classical
  obtain ⟨b, hb⟩ := (coproductCopiesMorphismsClopen V W E s).2.2.2.1
  let a := b ⟨f, hf⟩
  let w : W := Classical.arbitrary W
  have htop : f ⁻¹ᵁ (Sigma.ι (fun _ : E ↦ V) (a w)).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    change (↑(f ⁻¹ᵁ (Sigma.ι (fun _ : E ↦ V) (a w)).opensRange) : Set W) = Set.univ
    rw [hb ⟨f, hf⟩ (a w)]
    exact Set.eq_univ_of_forall (fun x ↦ a.apply_eq_of_preconnectedSpace x w)
  refine ⟨a w, ?_⟩
  have h := (coproductCopiesMorphismsClopen V W E s).1 f hf |>.2 (a w)
  rw [htop] at h
  have h' := congrArg (fun t ↦ W.topIso.inv ≫ t) h
  simpa only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] using h'

/-- The sheafification unit applied to a constant label.
Source: constant-sheaf definition
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
private abbrev constantLabel (V : Scheme.{u}) (E : Type u) (W : V.ProEt)
    (e : ULift.{u + 1, u} E) :=
  (toSheafify (Scheme.ProEt.topology V)
    ((Functor.const V.ProEtᵒᵖ).obj (ULift.{u + 1, u} E))).app (op W) e

private theorem comparison_constantLabel (V : Scheme.{u}) (E : Type u)
    (W : V.ProEt) (e : ULift.{u + 1, u} E) :
    (Scheme.proEtaleFiniteConstantComparison V E).hom.app (op W)
      (constantLabel V E W e) =
        ULift.up (show W ⟶ Scheme.proEtaleFiniteConstantObject V E from
          MorphismProperty.Over.homMk
            (W.hom ≫ Sigma.ι (fun _ : E ↦ V) e.down) (by simp)) := by
  exact congrArg (fun a ↦ a.app (op W) e)
    (toSheafify_sheafifyLift (Scheme.ProEt.topology V)
      (Scheme.proEtaleFiniteConstantSections V E) _)

private theorem constantLabel_injective (V : Scheme.{u}) (E : Type u) [Finite E]
    (W : V.ProEt) [Nonempty W.left] :
    Function.Injective (constantLabel V E W) := by
  intro a b h
  have h' := congrArg ((Scheme.proEtaleFiniteConstantComparison V E).hom.app (op W)) h
  rw [comparison_constantLabel, comparison_constantLabel] at h'
  have hh := congrArg (fun t ↦ t.down.left) h'
  let w : W.left := Classical.arbitrary _
  have hp := congrArg (fun t : W.left ⟶ ∐ fun _ : E ↦ V ↦ t w) hh
  change Sigma.ι (fun _ : E ↦ V) a.down (W.hom w) =
    Sigma.ι (fun _ : E ↦ V) b.down (W.hom w) at hp
  exact ULift.ext _ _ (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hp))

private theorem constantLabel_surjective (V : Scheme.{u}) [ConnectedSpace V]
    (E : Type u) [Finite E] :
    Function.Surjective (constantLabel V E (Scheme.ProEt.mk (𝟙 V))) := by
  intro s
  let W := Scheme.ProEt.mk (𝟙 V)
  let c := Scheme.proEtaleFiniteConstantComparison V E
  have : IsIso c := Scheme.proEtaleFiniteConstantComparison_isIso V E
  let f := (c.hom.app (op W) s).down
  obtain ⟨e, he⟩ := connected_copies_map_constant V V E (𝟙 V) f.left f.w
  refine ⟨ULift.up e, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (c.hom.app (op W))).1
  rw [comparison_constantLabel]
  apply ULift.ext
  apply MorphismProperty.Over.Hom.ext
  exact he.symm

private theorem constantLabel_germ_injective (V : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (E : Type u) [Finite E] (N : Scheme.ProEtaleGeometricNeighbourhood v) :
    Function.Injective (fun e : ULift.{u + 1, u} E ↦
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram v
        ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
          (ULift.{u + 1, u} E))) (op N) (constantLabel V E N.right e)) := by
  intro a b h
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (colimit.isColimit _) _ _).mp h
  have hn (e : ULift.{u + 1, u} E) :
      ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
        (ULift.{u + 1, u} E)).obj.map f.unop.right.op (constantLabel V E N.right e) =
      constantLabel V E j.unop.right e := by
    exact (congrArg (fun t ↦ t e)
      ((toSheafify (Scheme.ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (ULift.{u + 1, u} E))).naturality
          f.unop.right.op)).symm
  change ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
    (ULift.{u + 1, u} E)).obj.map f.unop.right.op (constantLabel V E N.right a) =
      ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
        (ULift.{u + 1, u} E)).obj.map f.unop.right.op (constantLabel V E N.right b) at hf
  rw [hn, hn] at hf
  have : Nonempty j.unop.right.left :=
    ⟨j.unop.hom.left (IsLocalRing.closedPoint Ω)⟩
  exact constantLabel_injective V E j.unop.right hf

private theorem constant_maps_fibre_ext (V : Scheme.{u}) [ConnectedSpace V]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (A B : FintypeCat.{u})
    (f g : (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj (ULift.{u + 1, u} A) ⟶
      (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj (ULift.{u + 1, u} B))
    (h : colim.map (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget v).op
        f.hom) =
      colim.map (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget v).op
        g.hom)) : f = g := by
  let W := Scheme.ProEt.mk (𝟙 V)
  let N : Scheme.ProEtaleGeometricNeighbourhood v :=
    StructuredArrow.mk (Y := W) (Over.homMk v (by change v ≫ 𝟙 V = v; exact Category.comp_id _))
  apply ((sheafificationAdjunction (Scheme.ProEt.topology V)
    (Type (u + 1))).homEquiv _ _).injective
  apply NatTrans.ext
  funext Z
  ext a
  have he (k : _ ⟶ (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
      (ULift.{u + 1, u} B)) := constantLabel_surjective V B (k.hom.app (op W)
        (constantLabel V A W a))
  obtain ⟨b, hb⟩ := he f
  obtain ⟨c, hc⟩ := he g
  have hbc : b = c := by
    apply constantLabel_germ_injective V v B N
    change colimit.ι (Scheme.proEtaleGeometricStalkDiagram v
      ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
        (ULift.{u + 1, u} B))) (op N) (constantLabel V B W b) =
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram v
        ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
          (ULift.{u + 1, u} B))) (op N) (constantLabel V B W c)
    rw [hb, hc]
    have hf := congrArg (fun t ↦ t (constantLabel V A W a))
      (colimit.ι_map (Functor.whiskerLeft
        (Scheme.proEtaleGeometricNeighbourhoodForget v).op f.hom) (op N))
    have hg := congrArg (fun t ↦ t (constantLabel V A W a))
      (colimit.ι_map (Functor.whiskerLeft
        (Scheme.proEtaleGeometricNeighbourhoodForget v).op g.hom) (op N))
    exact hf.symm.trans ((congrArg (fun t ↦ t
      (colimit.ι (Scheme.proEtaleGeometricStalkDiagram v
        ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
          (ULift.{u + 1, u} A))) (op N) (constantLabel V A W a))) h).trans hg)
  let r : Z.unop ⟶ W := MorphismProperty.Over.homMk Z.unop.hom (Category.comp_id _)
  have hn (k : _ ⟶ (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
      (ULift.{u + 1, u} B)) :
      k.hom.app Z (constantLabel V A Z.unop a) =
        ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
          (ULift.{u + 1, u} B)).obj.map r.op
            (k.hom.app (op W) (constantLabel V A W a)) := by
    have hh := congrArg (fun t ↦ t a)
      ((toSheafify (Scheme.ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (ULift.{u + 1, u} A))).naturality r.op)
    have hk := congrArg (fun t ↦ t (constantLabel V A W a)) (k.hom.naturality r.op)
    change constantLabel V A Z.unop a =
      ((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
        (ULift.{u + 1, u} A)).obj.map r.op (constantLabel V A W a) at hh
    change k.hom.app Z
      (((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
        (ULift.{u + 1, u} A)).obj.map r.op (constantLabel V A W a)) = _ at hk
    exact (congrArg (k.hom.app Z) hh).trans hk
  change f.hom.app Z (constantLabel V A Z.unop a) =
    g.hom.app Z (constantLabel V A Z.unop a)
  exact (hn f).trans ((congrArg
    (((constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj
      (ULift.{u + 1, u} B)).obj.map r.op)
        (hb.symm.trans ((congrArg (constantLabel V B W) hbc).trans hc))).trans (hn g).symm)

variable {U : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]

/-- The unique normalized splitting, its continuous left action, and all comparison
assertions. Finite labels are identified with the actual stalk by fibreIso; this
only changes the universe of a finite set, not its elements or action. No chosen
section or action is assumed: the theorem asserts existence of this whole package.
The universal-section equality is on X[G times Q], including nonconstant labels.
Source: Bhatt--Scholze, Lemmas 4.2.12, 5.1.2--5.1.4 and Corollary 5.1.5
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
structure ConnectedAbelianTowerNormalizedDescent (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ T.cone.pt.left) where
  fibre : T.finiteLevel.FullSubcategory ⥤ ContAction FintypeCat.{u} T.groupCone.pt
  fullyFaithful : fibre.FullyFaithful
  fibreIso : fibre ⋙ forget₂ _ FintypeCat ⋙ forget FintypeCat ⋙ uliftFunctor.{u + 1, u} ≅
    T.finiteLevelStalk z
  splitting : ∀ F : T.finiteLevel.FullSubcategory,
    F.obj.obj.obj (op ((abelianTowerLabels T.cone.pt).obj
      (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)))
  normalized : ∀ F : T.finiteLevel.FullSubcategory,
    IsAbelianTowerNormalizedSection T.cone.pt (Over.homMk z) F.obj (fibre.obj F).obj.V
      (Equiv.ofBijective (ConcreteCategory.hom (fibreIso.hom.app F))
        (ConcreteCategory.bijective_of_isIso (fibreIso.hom.app F))) (splitting F)
  unique : ∀ (F : T.finiteLevel.FullSubcategory) s,
    IsAbelianTowerNormalizedSection T.cone.pt (Over.homMk z) F.obj (fibre.obj F).obj.V
      (Equiv.ofBijective (ConcreteCategory.hom (fibreIso.hom.app F))
        (ConcreteCategory.bijective_of_isIso (fibreIso.hom.app F))) s → s = splitting F
  finiteLevel : ∀ (F : T.finiteLevel.FullSubcategory) (i : Iᵒᵖ),
    abelianTowerConstantAt F.obj (T.levels.obj i) →
    ∃ (s : F.obj.obj.obj (op ((abelianTowerLabels (T.levels.obj i)).obj
        (FintypeCat.toProfinite.obj (fibre.obj F).obj.V))))
      (ρ : T.groups.obj i →* End (fibre.obj F).obj.V),
      IsAbelianTowerNormalizedSection (T.levels.obj i)
        (Over.homMk z ≫ (Scheme.ProEt.forget U).map (T.cone.π.app i))
        F.obj (fibre.obj F).obj.V
        (Equiv.ofBijective (ConcreteCategory.hom (fibreIso.hom.app F))
          (ConcreteCategory.bijective_of_isIso (fibreIso.hom.app F))) s ∧
      F.obj.obj.map (abelianTowerLabelTransport (T.cone.π.app i)
        (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)).op s = splitting F ∧
      (∀ g : T.groupCone.pt, (fibre.obj F).obj.ρ g = ρ (T.groupCone.π.app i g)) ∧
      ∀ (g : T.groups.obj i) (q : (fibre.obj F).obj.V),
        abelianTowerLabelGerm (T.levels.obj i)
          (Over.homMk z ≫ (Scheme.ProEt.forget U).map (T.cone.π.app i) ≫
            (Scheme.ProEt.forget U).map (T.action i g))
          F.obj (fibre.obj F).obj.V s q =
            fibreIso.hom.app F (ULift.up (ConcreteCategory.hom (ρ g) q))
  natural : ∀ (F F' : T.finiteLevel.FullSubcategory) (f : F ⟶ F'),
    F'.obj.obj.map
      ((abelianTowerLabels T.cone.pt).map
        (FintypeCat.toProfinite.map ((forget₂ _ FintypeCat).map (fibre.map f)))).op
          (splitting F') = f.hom.hom.app _ (splitting F)
  actionLabels : ∀ F : T.finiteLevel.FullSubcategory,
    Profinite.of (T.groupCone.pt × (fibre.obj F).obj.V) ⟶
      FintypeCat.toProfinite.obj (fibre.obj F).obj.V
  actionLabels_apply : ∀ F (g : T.groupCone.pt) (q : (fibre.obj F).obj.V),
    actionLabels F (g, q) = ConcreteCategory.hom ((fibre.obj F).obj.ρ g) q
  descentLabel : ∀ F : T.finiteLevel.FullSubcategory,
    (abelianTowerLabels T.cone.pt).obj
      (Profinite.of (T.groupCone.pt × (fibre.obj F).obj.V)) ⟶
        (abelianTowerLabels T.cone.pt).obj (FintypeCat.toProfinite.obj (fibre.obj F).obj.V)
  descentLabel_base : ∀ F,
    (descentLabel F).left ≫ Scheme.UniversalCover.profiniteProductBase _ _ =
      ((abelianTowerLabels T.cone.pt).map
        (ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩)).left ≫
          T.comparison.hom ≫ pullback.snd _ _
  descentLabel_label : ∀ F,
    (descentLabel F).left ≫ pullback.fst _ _ =
      ((abelianTowerLabels T.cone.pt).map
        (ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩)).left ≫ pullback.fst _ _
  descent : ∀ F : T.finiteLevel.FullSubcategory,
    F.obj.obj.map ((abelianTowerLabels T.cone.pt).map (actionLabels F)).op (splitting F) =
      F.obj.obj.map (descentLabel F).op (splitting F)
  complete : ∀ F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1)),
    T.finiteLevel F ↔ abelianTowerConstantAt F T.cone.pt
  constant_maps : ∀ (V : Scheme.{u}) [ConnectedSpace V] (K : Type u) [Field K]
    [IsAlgClosed K] (v : Spec (.of K) ⟶ V) (A B : FintypeCat.{u})
    (f g : (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj (ULift.{u + 1, u} A) ⟶
      (constantSheaf (Scheme.ProEt.topology V) (Type (u + 1))).obj (ULift.{u + 1, u} B)),
    colim.map (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget v).op f.hom) =
      colim.map (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget v).op g.hom) →
        f = g


/-- Normalized finite descent, finite-stage completeness, and the Hom bijection on
actual geometric fibres, including empty fibres.
Source: Bhatt--Scholze, Lemmas 4.2.12, 5.1.2--5.1.4 and Corollary 5.1.5
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent).

Proof:
1. Object inverse image is sectionwise restriction on the slice, by
   lem-sfb-proetale-object-inverse-image-restriction and weakly etale localization.
   Iterated restrictions have the canonical double-overlap cocycle.
2. Represent finite constants by labelled copies (finite-constant representability).
   Yoneda and coproduct-copies-morphisms-clopen identify their arrows with families
   of locally constant functions on the base, including empty label sets.
3. On a nonempty connected base those functions are constant. The geometric stalk
   of the constant sheaf is its label set: locally constant germs become constant
   on a pointed open neighborhood. Inverse-image stalk comparison identifies fibres.
4. Normalize an arbitrary finite-level trivialization by its inverse fibre map.
   Step 3 proves uniqueness; pulling to X gives independence of the chosen level.
5. On the component (x,gx) the descent comparison is a permutation rho_i(g).
   The cocycle gives rho_i(hg)=rho_i(g)rho_i(h). The finite groups are abelian,
   so these permutations form a left action with exactly the given convention.
6. Pull back that finite-level action. It is continuous and factors through Gamma_i.
   On each clopen cylinder g_i=a the whole arrow is the constant permutation
   rho_i(a). Gluing sheaf morphisms gives the equation on all X[G times Q].
7. Compare two levels at a common later level. Their normalized splittings coincide,
   hence so do their whole descent arrows and therefore their actions on fibres.
8. A sheaf morphism is constant in normalized labels; naturality of the descent
   comparison makes its fibre map equivariant. Conversely an equivariant fibre map
   intertwines the whole overlap arrows, since G to Gamma_i is surjective by the
   finite inverse-limit lemma. Apply lem-pe-set-sheaf-cover-descent.
9. Gluing along the singleton covering X to U gives a unique global morphism.
   Equality is detected on its fibre. An empty source fibre gives the unique map;
   a nonempty source and empty target give none; both empty give the unique map.
10. If F is finite constant on X, its finite-frame Isom sheaf H is a sheaf by
    morphism gluing. On X it is the constant symmetric-group sheaf, even for the
    empty fibre, whose symmetric group is a singleton.
11. Constants are classical, since the etale/proetale inverse image preserves the
    final object and coproducts. Locally-classical continuity gives H(X)=colim H(X_i).
    A frame on X therefore comes from an actual frame on some X_i. The reverse
    implication is pullback of a finite-level splitting. This proves completeness. -/
theorem nonempty_connectedAbelianTowerNormalizedDescent (U : Scheme.{u}) [IsAffine U]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (T : ConnectedAbelianCoverTower U I) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ T.cone.pt.left) :
    Nonempty (ConnectedAbelianTowerNormalizedDescent T z) := by
  classical
  let D (F : T.finiteLevel.FullSubcategory) : AbelianTowerDescentObject T z F.obj :=
    (nonempty_abelianTowerDescentObject T z F.obj F.property).some
  let S := T.finiteLevelStalk z
  have label_fibre (F F' : T.finiteLevel.FullSubcategory) (f : F ⟶ F')
      (q : (D F).action.obj.V) :
      (D F').fibre (ULift.up (ConcreteCategory.hom
        ((D F).labelMap T (D F') f.hom) q)) = S.map f ((D F).fibre (ULift.up q)) :=
    (D F).fibre_labelMap T (D F') f.hom q
  have label_id (F : T.finiteLevel.FullSubcategory) :
      (D F).labelMap T (D F) (𝟙 F.obj) = 𝟙 (D F).action.obj.V := by
    ext q
    have h := label_fibre F F (𝟙 F) q
    rw [S.map_id] at h
    exact congrArg ULift.down ((D F).fibre.injective h)
  have label_comp (F F' F'' : T.finiteLevel.FullSubcategory)
      (f : F ⟶ F') (g : F' ⟶ F'') :
      (D F).labelMap T (D F'') (f.hom ≫ g.hom) =
        (D F).labelMap T (D F') f.hom ≫ (D F').labelMap T (D F'') g.hom := by
    ext q
    have hfg := label_fibre F F'' (f ≫ g) q
    have hg := label_fibre F' F'' g
      (ConcreteCategory.hom ((D F).labelMap T (D F') f.hom) q)
    have hf := label_fibre F F' f q
    have hc := congrArg (fun h ↦ h ((D F).fibre (ULift.up q))) (S.map_comp f g)
    exact congrArg ULift.down ((D F'').fibre.injective
      (hfg.trans (hc.trans (hg.trans (congrArg (S.map g) hf)).symm)))
  let fibre : T.finiteLevel.FullSubcategory ⥤ ContAction FintypeCat.{u} T.groupCone.pt :=
    { obj := fun F ↦ (D F).action
      map := fun {F F'} f ↦ ObjectProperty.homMk
        { hom := (D F).labelMap T (D F') f.hom
          comm := (abelianTowerDescentHom T (D F) (D F')).1 f.hom |>.1 }
      map_id := fun F ↦ ObjectProperty.hom_ext _ (Action.Hom.ext (label_id F))
      map_comp := fun {F F' F''} f g ↦
        ObjectProperty.hom_ext _ (Action.Hom.ext (label_comp F F' F'' f g)) }
  have ff : fibre.FullyFaithful := by
    refine ⟨fun {F F'} a ↦ ObjectProperty.homMk
      ((abelianTowerDescentHom T (D F) (D F')).2 a.hom.hom a.hom.comm).choose, ?_, ?_⟩
    · intro F F' a
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      exact ((abelianTowerDescentHom T (D F) (D F')).2 a.hom.hom
        a.hom.comm).choose_spec.1
    · intro F F' f
      apply ObjectProperty.hom_ext
      exact ((abelianTowerDescentHom T (D F) (D F')).2
        ((D F).labelMap T (D F') f.hom)
          ((abelianTowerDescentHom T (D F) (D F')).1 f.hom).1).choose_spec.2 f.hom rfl |>.symm
  let e : fibre ⋙ forget₂ _ FintypeCat ⋙ forget FintypeCat ⋙ uliftFunctor.{u + 1, u} ≅ S :=
    NatIso.ofComponents (fun F ↦ (D F).fibre.toIso) (by
      intro F F' f
      ext q
      exact label_fibre F F' f q.down)
  have he (F : T.finiteLevel.FullSubcategory) :
      Equiv.ofBijective (ConcreteCategory.hom (e.hom.app F))
        (ConcreteCategory.bijective_of_isIso (e.hom.app F)) = (D F).fibre := by
    apply Equiv.ext
    intro q
    rfl
  refine ⟨{ fibre := fibre
            fullyFaithful := ff
            fibreIso := e
            splitting := fun F ↦ (D F).section_
            normalized := ?_
            unique := ?_
            finiteLevel := ?_
            natural := ?_
            actionLabels := fun F ↦ abelianTowerActionLabels T (D F).action
            actionLabels_apply := fun _ _ _ ↦ rfl
            descentLabel := fun F ↦ abelianTowerDescentLabel T (D F).action.obj.V
            descentLabel_base := fun F ↦ abelianTowerDescentLabel_base T _
            descentLabel_label := fun F ↦ abelianTowerDescentLabel_label T _
            descent := fun F ↦ (D F).descent
            complete := abelianTowerFiniteFrame T
            constant_maps := fun V _ K _ _ v A B f g h ↦
              constant_maps_fibre_ext V v A B f g h }⟩
  · intro F
    rw [he]
    exact (D F).normalized
  · intro F s hs
    rw [he] at hs
    exact (D F).unique s hs
  · intro F i hi
    rw [he]
    exact (D F).finiteLevel i hi
  · intro F F' f
    exact ((abelianTowerDescentHom T (D F) (D F')).1 f.hom).2

end AlgebraicGeometry.ProEtale
