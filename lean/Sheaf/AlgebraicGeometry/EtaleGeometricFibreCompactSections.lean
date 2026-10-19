module

public import Sheaf.AlgebraicGeometry.CompactlySupportedSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Sheaf.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
import WeilConjectures.AlgebraicGeometry.FiniteOverField

/-!
# Compact sections of a quasi-compact étale geometric fibre

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 09Z9, assertion (1),
and Tag 0F4Y (blueprint: lem-sfb-etale-geometric-fibre-compact-sections).
This statement is revalidated for the NE stage-2 delivery.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem unit_germ
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : X.Etale)
    (ū : (pointSmallEtale (y ≫ f)).fiber.obj U) :
    ((Etale.upperStarLowerStarAdjunction (ModuleCat A) f).unit.app G).hom.app (op U) ≫
        (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
          ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
          ((Etale.upperStar (ModuleCat A) f).obj G).obj ≫
        (Etale.upperStarCompSheafFiberIso (ModuleCat A) f y).hom.app G =
      (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv ((Etale.upperStarCompSheafFiberIso (ModuleCat A) f y).app G)).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale y).sheafFiber.map _ =
    (pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} A)
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction (ModuleCat A) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl
private theorem canonical_coordinates
    (A : Type (u + 1)) [CommRing A] {I : Type u} [Finite I]
    (X : ModuleCat.{u + 1} A) (Y : I → ModuleCat.{u + 1} A)
    (f : ∀ i, X ⟶ Y i) (i : I) :
    let _ : DecidableEq I := Classical.decEq I
    canonicalFiniteCoproductMap A X Y f ≫
        (ModuleCat.coprodIsoDirectSum.{u + 1, u, u + 1} Y).hom ≫
        ModuleCat.ofHom (DirectSum.coeFnLinearMap A (M := fun i ↦ Y i)) ≫
        ModuleCat.ofHom (LinearMap.proj i) = f i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  unfold canonicalFiniteCoproductMap
  simp only [dif_pos (inferInstance : Finite I)]
  change ModuleCat.ofHom _ ≫ _ ≫ _ ≫ _ = _
  rw [ModuleCat.ofHom_comp]
  simp only [ModuleCat.ofHom_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext z
  simp only [ModuleCat.comp_apply]
  simp only [← ConcreteCategory.comp_apply]
  simp [DirectSum.lof_eq_of, DirectSum.of_apply]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem pullback_germ
    (A : Type (u + 1)) [CommRing A] {V P C : Scheme.{u}}
    (r : C ⟶ V) (p : P ⟶ V) [Etale p] (a : C ⟶ P) (ha : a ≫ p = r)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ C)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    etaleSectionPullbackToGlobal A r p a ha F ≫ geometricFibreComponentMap A r x F =
      (pointSmallEtale (x ≫ r)).toPresheafFiber (Scheme.Etale.mk p)
        (Over.homMk (x ≫ a) (by simp [Category.assoc, ha])) F.obj := by
  let j : Scheme.Etale.mk (𝟙 C) ⟶ r.Etale.obj (Scheme.Etale.mk p) :=
    MorphismProperty.Over.homMk (pullback.lift a (𝟙 C) (by simpa using ha))
      (by exact pullback.lift_snd _ _ _)
  have hj : (pointSmallEtale x).fiber.map j (Over.homMk x) =
      (pointSmallEtaleFiberEtaleIso r x).inv.app (Scheme.Etale.mk p)
        (Over.homMk (x ≫ a) (by simp [Category.assoc, ha])) := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (x ≫ pullback.lift a (𝟙 C) _) ≫ pullback.fst p r = _
      rw [Category.assoc, pullback.lift_fst,
        pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      rfl
    · change (x ≫ pullback.lift a (𝟙 C) _) ≫ pullback.snd p r = _
      rw [Category.assoc, pullback.lift_snd, Category.comp_id,
        pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
  simp only [etaleSectionPullbackToGlobal, geometricFibreComponentMap, Category.assoc]
  change ((Etale.upperStarLowerStarAdjunction (ModuleCat A) r).unit.app F).hom.app _ ≫
      ((Etale.upperStar (ModuleCat A) r).obj F).obj.map j.op ≫
      (pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
        (Over.homMk x) _ ≫ _ = _
  rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hj]
  exact unit_germ A r x F (Scheme.Etale.mk p) _

private theorem canonical_single
    (A : Type (u + 1)) [CommRing A] {I : Type u} [Finite I]
    (X : ModuleCat.{u + 1} A) (Y : I → ModuleCat.{u + 1} A)
    (f : ∀ i, X ⟶ Y i) (j : I) (z : X)
    (hz : ∀ i, i ≠ j → f i z = 0) :
    canonicalFiniteCoproductMap A X Y f z = Sigma.ι Y j (f j z) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  apply (ConcreteCategory.bijective_of_isIso
    (ModuleCat.coprodIsoDirectSum.{u + 1, u, u + 1} Y).hom).1
  change (canonicalFiniteCoproductMap A X Y f ≫
      (ModuleCat.coprodIsoDirectSum.{u + 1, u, u + 1} Y).hom) z =
    (Sigma.ι Y j ≫ (ModuleCat.coprodIsoDirectSum.{u + 1, u, u + 1} Y).hom) (f j z)
  rw [ModuleCat.ι_coprodIsoDirectSum_hom]
  unfold canonicalFiniteCoproductMap
  simp only [dif_pos (inferInstance : Finite I)]
  change (ModuleCat.ofHom _ ≫ _) z = _
  rw [ModuleCat.ofHom_comp]
  simp only [ModuleCat.ofHom_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (∑ i, (DirectSum.lof A I (fun i ↦ Y i) i).comp (f i).hom) z = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · rfl
  · intro i _ hij
    simp [hz i hij]
  · simp

private theorem germ_transport
    (A : Type (u + 1)) [CommRing A] {V : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : V.Etale)
    (x x' : Spec (.of Ω) ⟶ V) (e : x = x')
    (y : Spec (.of Ω) ⟶ U.left) (hy : y ≫ U.hom = x) :
    (pointSmallEtale x).toPresheafFiber U (Over.homMk y hy) F.obj ≫
        eqToHom (congrArg (fun q ↦ (pointSmallEtale q).sheafFiber.obj F) e) =
      (pointSmallEtale x').toPresheafFiber U (Over.homMk y (hy.trans e)) F.obj := by
  subst x'
  simp


private theorem clopen_extension
    (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {W P : X.Etale} (i : W ⟶ P) [IsOpenImmersion i.left]
    (hi : IsClosed (Set.range i.left.base)) (z : F.obj.obj (op W)) :
    ∃ zext : F.obj.obj (op P), F.obj.map i.op zext = z ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ P.left),
        x default ∉ Set.range i.left.base →
          (Scheme.pointSmallEtale (x ≫ P.hom)).toPresheafFiber P
            (Over.homMk x) F.obj zext = 0 := by
  classical
  have : Etale P.hom := P.prop
  let U : P.left.Opens := ⟨(Set.range i.left.base)ᶜ, hi.isOpen_compl⟩
  let Q : X.Etale := Scheme.Etale.mk (U.ι ≫ P.hom)
  let j : Q ⟶ P := MorphismProperty.Over.homMk U.ι rfl
  let D (b : ULift.{u} Bool) : X.Etale := if b.down then W else Q
  let k (b : ULift.{u} Bool) : D b ⟶ P := by
    rcases b with ⟨b⟩
    cases b
    · exact j
    · exact i
  have (b : ULift.{u} Bool) : IsOpenImmersion (k b).left := by
    rcases b with ⟨b⟩
    cases b
    · change IsOpenImmersion U.ι
      infer_instance
    · exact inferInstanceAs (IsOpenImmersion i.left)
  have hd : Pairwise (fun b b' ↦ Disjoint (Set.range (k b).left.base)
      (Set.range (k b').left.base)) := by
    rintro ⟨b⟩ ⟨b'⟩ hne
    cases b <;> cases b' <;> try exact (hne rfl).elim
    · change Disjoint (Set.range U.ι) (Set.range i.left.base)
      rw [Scheme.Opens.range_ι]
      exact disjoint_compl_left
    · change Disjoint (Set.range i.left.base) (Set.range U.ι)
      rw [Scheme.Opens.range_ι]
      exact disjoint_compl_right
  have hc : ⋃ b, Set.range (k b).left.base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Set.range i.left.base
    · exact Set.mem_iUnion.mpr ⟨⟨true⟩, hx⟩
    · exact Set.mem_iUnion.mpr ⟨⟨false⟩, by
        change x ∈ Set.range U.ι
        rw [Scheme.Opens.range_ι]
        exact hx⟩
  let a (b : ULift.{u} Bool) : ModuleCat.of A A ⟶ F.obj.obj (op (D b)) := by
    rcases b with ⟨b⟩
    cases b
    · exact 0
    · exact ModuleCat.ofHom (LinearMap.toSpanSingleton A _ z)
  obtain ⟨σ, hσ, _⟩ := Scheme.Etale.existsUnique_of_pairwise_disjoint F D k hd hc a
  refine ⟨σ 1, ?_, ?_⟩
  · have hh := ConcreteCategory.congr_hom (hσ ⟨true⟩) 1
    simpa [a, k, D] using hh
  · intro Ω _ _ x hx
    have hr : Set.range x.base ⊆ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨b, rfl⟩
      change x b ∉ Set.range i.left.base
      simpa only [Subsingleton.elim b default] using hx
    let y := IsOpenImmersion.lift U.ι x hr
    have hy : y ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
    let ypt : (Scheme.pointSmallEtale (x ≫ P.hom)).fiber.obj Q :=
      Over.homMk y (by change y ≫ U.ι ≫ P.hom = x ≫ P.hom; rw [← Category.assoc, hy])
    have hpt : (Scheme.pointSmallEtale (x ≫ P.hom)).fiber.map j ypt = Over.homMk x := by
      apply Over.OverMorphism.ext
      exact hy
    rw [← hpt, ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
    have hz : F.obj.map j.op (σ 1) = 0 := by
      simpa [k, a, D] using ConcreteCategory.congr_hom (hσ ⟨false⟩) 1
    rw [hz, map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `h : V ⟶ T` be separated, quasi-compact, and étale, and let `t` be a geometric
point of `T` over an algebraically closed field `Ω`. The geometric fibre is finite and its
canonical coproduct decomposition is an isomorphism. Every fibre section has proper reduced
support, and the canonical restriction-and-germ map identifies compactly supported sections
with the coproduct of the geometric stalks. The final clause gives the germ formula for the
extension by zero from a pointed étale neighbourhood.

Source: Stacks Project, Étale Cohomology, Tag 09Z9, assertion (1), and more-etale.tex,
Tag 0F4Y (blueprint: lem-sfb-etale-geometric-fibre-compact-sections).
Proof: base change preserves étaleness, separatedness and quasi-compactness; Tag 09Z9
splits the fibre over `Spec Ω` into finitely many copies of `Spec Ω`, yielding the stated
coproduct isomorphism. The clopen decomposition identifies sections with their component
germs, and the upper-star stalk comparison identifies each fibre germ with the stalk at the
corresponding point of `V`. The support is a finite union of point components and is proper
over `Spec Ω`, so every section is compactly supported and the finite coproduct map is an
isomorphism. Finally, the graph of an étale lift is clopen in the fibre product; gluing the
given section with zero off the graph gives the extension and the stated germ formula.
-/
theorem etaleGeometricFibreCompactSections
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (h : V ⟶ T) [IsSeparated h] [QuasiCompact h] [Etale h]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let C := Limits.pullback h t
    let r := Limits.pullback.fst h t
    let I := Scheme.Hom.GeometricFiber h t
    Finite I ∧
      IsIso (Sigma.desc (fun v : I ↦
        Limits.pullback.lift v.1 (𝟙 (Spec (.of Ω))) (by simpa using v.2)) :
        (∐ fun _ : I ↦ Spec (.of Ω)) ⟶ Limits.pullback h t) ∧
      IsIso (compactlySupportedSections.ι A (Limits.pullback.snd h t)
        ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F) ≫
        etaleGeometricFibreRestrictionMap A h Ω t F) ∧
      (∀ (s : (Etale.sectionsFunctor (ModuleCat.{u + 1} A) C).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F)),
        Etale.SectionHasProperSupport A
          ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F)
          (Scheme.Etale.mk (𝟙 C)) (Limits.pullback.snd h t) s) ∧
      (∀ (W : T.Etale) (w : Spec (.of Ω) ⟶ W.left)
          (lift : W.left ⟶ V) [Etale lift]
          (hw : w ≫ W.hom = t) (hlift : lift ≫ h = W.hom)
          (z : F.obj.obj (op (Scheme.Etale.mk lift))),
        let P := Limits.pullback h W.hom
        let p := Limits.pullback.fst h W.hom
        let γ := Limits.pullback.lift lift (𝟙 W.left) (by simp [hlift])
        ∃ zext : F.obj.obj (op (Scheme.Etale.mk p)),
          (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
              (x : Spec (.of Ω') ⟶ P),
            x default ∉ Set.range γ.base →
              ((Scheme.pointSmallEtale (x ≫ p)).toPresheafFiber
                (Scheme.Etale.mk p) (CategoryTheory.Over.homMk x) F.obj).hom zext = 0) ∧
          F.obj.map (MorphismProperty.Over.homMk
            (A := Scheme.Etale.mk lift) (B := Scheme.Etale.mk p) γ
              (by simp [p, γ])).op zext = z ∧
          (etaleGeometricFibreRestrictionMap A h Ω t F).hom
              ((etaleSectionPullbackToGlobal A r p
                (Limits.pullback.lift r (Limits.pullback.snd h t ≫ w)
                  (by simpa only [r, Category.assoc, hw] using
                    (Limits.pullback.condition (f := h) (g := t))))
                (by simp [p]) F).hom zext) =
              (Sigma.ι (fun v : Scheme.Hom.GeometricFiber h t ↦
                (Scheme.pointSmallEtale v.1).sheafFiber.obj F)
                ⟨w ≫ lift, by simp [hw, hlift]⟩)
                (((Scheme.pointSmallEtale (w ≫ lift)).toPresheafFiber
                  (Scheme.Etale.mk lift) (CategoryTheory.Over.homMk w) F.obj).hom z)) := by
  classical
  dsimp only
  let C := Limits.pullback h t
  let q := Limits.pullback.snd h t
  let c (v : Scheme.Hom.GeometricFiber h t) : Spec (.of Ω) ⟶ C :=
    Limits.pullback.lift v.1 (𝟙 _) (by simpa using v.2)
  have hcq (v : Scheme.Hom.GeometricFiber h t) : c v ≫ q = 𝟙 _ := by
    exact Limits.pullback.lift_snd _ _ _
  have hqfinite : IsFinite q := IsFinite.of_locallyQuasiFinite q
  have hIfinite : Finite (Scheme.Hom.GeometricFiber h t) := by
    let e := Scheme.Hom.GeometricFiber.pullbackEquiv h t (𝟙 (Spec (.of Ω)))
    have : Finite (Scheme.Hom.GeometricFiber h ((𝟙 (Spec (.of Ω))) ≫ t)) :=
      Finite.of_equiv _ e
    simpa using this
  have hopen (v : Scheme.Hom.GeometricFiber h t) : IsOpenImmersion (c v) := by
    have : IsOpenImmersion (c v ≫ q) := by rw [hcq]; infer_instance
    exact FormallyUnramified.isOpenImmersion_of_comp q (c v)
  have hdisj : Pairwise (fun v v' : Scheme.Hom.GeometricFiber h t ↦
      Disjoint (c v).opensRange (c v').opensRange) := by
    intro v v' hv
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨a, ha⟩ := hx.1
    obtain ⟨b, hb⟩ := hx.2
    have hab : Set.range (c v').base ⊆ Set.range (c v).base := by
      rintro _ ⟨d, rfl⟩
      exact ⟨a, ha.trans (hb.symm.trans (congrArg (c v') (Subsingleton.elim b d)))⟩
    let l := IsOpenImmersion.lift (c v) (c v') hab
    have hl : l ≫ c v = c v' := IsOpenImmersion.lift_fac _ _ _
    have hlid : l = 𝟙 _ := by
      have hh := congrArg (fun k ↦ k ≫ q) hl
      simpa only [Category.assoc, hcq, Category.comp_id] using hh
    apply hv
    apply Subtype.ext
    have hh := congrArg (fun k ↦ k ≫ Limits.pullback.fst h t) hl
    simpa [hlid, c] using hh
  have hcov : (⨆ v, (c v).opensRange) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨v, hv⟩ := Scheme.Hom.GeometricFiber.exists_apply_default_eq q
      (𝟙 (Spec (.of Ω))) x (Subsingleton.elim _ _)
    let v' : Scheme.Hom.GeometricFiber h t :=
      ⟨v.1 ≫ Limits.pullback.fst h t, by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, v.2]
        simp⟩
    have hc : c v' = v.1 := by
      apply Limits.pullback.hom_ext
      · simp [c, v']
      · exact (Limits.pullback.lift_snd _ _ _).trans v.2.symm
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨v', default, hc ▸ hv⟩
  have hcoprod : IsIso (Sigma.desc c) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp
      (nonempty_isColimit_cofanMk_of c hcov hdisj)
  have hsupp (s : (Etale.sectionsFunctor (ModuleCat.{u + 1} A) C).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) (Limits.pullback.fst h t)).obj F)) :
      Etale.SectionHasProperSupport A
        ((Etale.upperStar (ModuleCat.{u + 1} A) (Limits.pullback.fst h t)).obj F)
        (Scheme.Etale.mk (𝟙 C)) q s := by
    obtain ⟨Z, _, hZ⟩ := Etale.etaleModuleSection_closedSupport A
      ((Etale.upperStar (ModuleCat.{u + 1} A) (Limits.pullback.fst h t)).obj F)
      (Scheme.Etale.mk (𝟙 C)) s
    refine ⟨Z, hZ, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ q)
    infer_instance
  refine ⟨hIfinite, hcoprod, ?_, hsupp, ?_⟩
  · let : IsFinite q := hqfinite
    obtain ⟨hfinC, hdiscC⟩ := finite_and_discreteTopology_of_isFinite q
    let : Finite C := hfinC
    let : DiscreteTopology C := hdiscC
    have hsepC (x : C) : IsSepClosed (C.residueField x) := by
      have := Scheme.isAlgClosed_residueField_of_isClosed q x (isClosed_discrete _)
      infer_instance
    have hcbi : Function.Bijective (fun v : Scheme.Hom.GeometricFiber h t ↦ c v default) := by
      constructor
      · intro v v' hh
        apply Subtype.ext
        have he : c v = c v' := Scheme.eq_of_comp_eq_of_isSepClosed q
          ((hcq v).trans (hcq v').symm) hh (by
            have := Scheme.isAlgClosed_residueField_of_isClosed (𝟙 (Spec (.of Ω)))
              (q (c v default)) (isClosed_discrete _)
            infer_instance)
        simpa [c] using congrArg (fun k ↦ k ≫ Limits.pullback.fst h t) he
      · intro x
        have hx : x ∈ (⨆ v, (c v).opensRange) := hcov.symm ▸ trivial
        obtain ⟨v, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨v, (congrArg (c v) (Subsingleton.elim default y)).trans hy⟩
    let e : C ≃ Scheme.Hom.GeometricFiber h t := (Equiv.ofBijective _ hcbi).symm
    let spt (x : C) : Spec (.of Ω) ⟶ C := c (e x)
    have hspt (x : C) : (spt x).base.hom default = x := e.symm_apply_apply x
    have hpt (x : C) : spt x ≫ Limits.pullback.fst h t = (e x).1 := by
      exact Limits.pullback.lift_fst _ _ _
    let G := (Etale.upperStar (ModuleCat.{u + 1} A) (Limits.pullback.fst h t)).obj F
    let hp := Etale.isIso_piLift_toPresheafFiber hsepC (fun _ : C ↦ Ω) spt hspt G
    have hι : IsIso (compactlySupportedSections.ι A q G) := by
      apply (ConcreteCategory.isIso_iff_bijective _).2
      constructor
      · intro x y hxy
        exact Subtype.ext hxy
      · intro s
        have hs' := hsupp s
        have hsSpan : s ∈ Submodule.span A {s |
            Etale.SectionHasProperSupport A G (Scheme.Etale.mk (𝟙 C)) q s} :=
          Submodule.subset_span hs'
        exact ⟨⟨s, hsSpan⟩, rfl⟩
    let : Finite (Scheme.Hom.GeometricFiber h t) := hIfinite
    let : Fintype (Scheme.Hom.GeometricFiber h t) := Fintype.ofFinite _
    let Z : (Scheme.Hom.GeometricFiber h t) → ModuleCat.{u + 1} A := fun v ↦
      (Scheme.pointSmallEtale v.1).sheafFiber.obj F
    let E : (∐ Z) ⟶ ∏ᶜ Z :=
      (ModuleCat.coprodIsoDirectSum.{u + 1, u, u + 1} Z).hom ≫
        ModuleCat.ofHom (DirectSum.coeFnLinearMap A (M := fun v ↦ Z v)) ≫
        (ModuleCat.piIsoPi.{u + 1, u, u + 1} Z).inv
    have hE : IsIso E := by
      have : IsIso (ModuleCat.ofHom
          (DirectSum.coeFnLinearMap A (M := fun v ↦ Z v))) := by
        apply (ConcreteCategory.isIso_iff_bijective _).2
        exact (DirectSum.addEquivProd (fun v ↦ Z v)).bijective
      infer_instance
    have hcoords : IsIso (Pi.lift (fun x : C ↦
        geometricFibreComponentMap A (Limits.pullback.fst h t) (spt x) F ≫
          eqToHom (show (Scheme.pointSmallEtale
            (spt x ≫ Limits.pullback.fst h t)).sheafFiber.obj F = Z (e x) from
              congrArg (fun y ↦ (Scheme.pointSmallEtale y).sheafFiber.obj F) (hpt x)))) := by
      have : IsIso (Pi.lift (fun x : C ↦
          (Scheme.pointSmallEtale (spt x)).toPresheafFiber
            (Scheme.Etale.mk (𝟙 C)) (CategoryTheory.Over.homMk (spt x)) G.obj) ≫
          Limits.Pi.map (fun x ↦ (Etale.upperStarCompSheafFiberIso
            (ModuleCat.{u + 1} A) (Limits.pullback.fst h t) (spt x)).hom.app F ≫
              eqToHom (show (Scheme.pointSmallEtale
                (spt x ≫ Limits.pullback.fst h t)).sheafFiber.obj F = Z (e x) from
              congrArg (fun y ↦ (Scheme.pointSmallEtale y).sheafFiber.obj F) (hpt x)))) := by
        infer_instance
      convert this using 1
      · rfl
      · apply Limits.Pi.hom_ext
        intro x
        simp only [geometricFibreComponentMap, Category.assoc,
          Limits.Pi.map_π, Limits.Pi.lift_π_assoc, Limits.Pi.lift_π]
        rfl
    have hfac :
        (compactlySupportedSections.ι A q G ≫ etaleGeometricFibreRestrictionMap A h Ω t F) ≫ E ≫
          (Limits.Pi.reindex e Z).inv =
        compactlySupportedSections.ι A q G ≫ Pi.lift (fun x : C ↦
          geometricFibreComponentMap A (Limits.pullback.fst h t) (spt x) F ≫
            eqToHom (show (Scheme.pointSmallEtale
              (spt x ≫ Limits.pullback.fst h t)).sheafFiber.obj F = Z (e x) from
              congrArg (fun y ↦ (Scheme.pointSmallEtale y).sheafFiber.obj F) (hpt x))) := by
      apply Limits.Pi.hom_ext
      intro x
      simp only [Category.assoc, Limits.Pi.reindex_inv_π]
      change compactlySupportedSections.ι A q G ≫
        etaleGeometricFibreRestrictionMap A h Ω t F ≫ E ≫ Limits.Pi.π Z (e x) = _
      dsimp only [E]
      simp only [etaleGeometricFibreRestrictionMap, Category.assoc,
        ModuleCat.piIsoPi_inv_kernel_ι]
      dsimp only [Z, spt, c]
      erw [Limits.Pi.lift_π]
      congr 1
      convert canonical_coordinates A _
        (fun v : Scheme.Hom.GeometricFiber h t ↦
          (Scheme.pointSmallEtale v.1).sheafFiber.obj F)
        (fun v ↦ geometricFibreComponentMap A (Limits.pullback.fst h t) (c v) F ≫
          eqToHom (congrArg (fun y ↦ (Scheme.pointSmallEtale y).sheafFiber.obj F)
            (show c v ≫ Limits.pullback.fst h t = v.1 from
              Limits.pullback.lift_fst _ _ _))) (e x) using 1
      congr 4; first | rfl | exact Subsingleton.elim _ _
    have : IsIso ((compactlySupportedSections.ι A q G ≫
        etaleGeometricFibreRestrictionMap A h Ω t F) ≫ E ≫
          (Limits.Pi.reindex e Z).inv) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (E ≫ (Limits.Pi.reindex e Z).inv)
  · intro W w lift _ hw hlift
    let P := Limits.pullback h W.hom
    let p := Limits.pullback.fst h W.hom
    let π := Limits.pullback.snd h W.hom
    let γ : W.left ⟶ P := Limits.pullback.lift lift (𝟙 W.left) (by simp [hlift])
    have hγ : γ ≫ π = 𝟙 _ := Limits.pullback.lift_snd _ _ _
    have : IsOpenImmersion (γ ≫ π) := by rw [hγ]; infer_instance
    have : IsOpenImmersion γ := FormallyUnramified.isOpenImmersion_of_comp π γ
    have : IsClosedImmersion (γ ≫ π) := by rw [hγ]; infer_instance
    have : IsClosedImmersion γ := IsClosedImmersion.of_comp γ π
    let i : Scheme.Etale.mk lift ⟶ Scheme.Etale.mk p :=
      MorphismProperty.Over.homMk γ (by simp [γ, p])
    have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion γ)
    intro z
    obtain ⟨zext, hz, hzero⟩ := clopen_extension A F i
      (show IsClosed (Set.range i.left.base) from γ.isClosedEmbedding.isClosed_range) z
    refine ⟨zext, hzero, hz, ?_⟩
    let : Finite (Scheme.Hom.GeometricFiber h t) := hIfinite
    let v₀ : Scheme.Hom.GeometricFiber h t := ⟨w ≫ lift, by simp [hw, hlift]⟩
    let a : C ⟶ P := Limits.pullback.lift (Limits.pullback.fst h t)
      (q ≫ w) (by simpa only [Category.assoc, hw] using
        (Limits.pullback.condition (f := h) (g := t)))
    have ha : a ≫ p = Limits.pullback.fst h t := Limits.pullback.lift_fst _ _ _
    let b (v : Scheme.Hom.GeometricFiber h t) : Spec (.of Ω) ⟶ P :=
      Limits.pullback.lift v.1 w (by simpa [hw] using v.2)
    have hb (v : Scheme.Hom.GeometricFiber h t) : c v ≫ a = b v := by
      apply Limits.pullback.hom_ext
      · simp [a, b, c]
      · simp [a, b, c, q]
    have he (v : Scheme.Hom.GeometricFiber h t) :
        c v ≫ Limits.pullback.fst h t = v.1 := Limits.pullback.lift_fst _ _ _
    let Z (v : Scheme.Hom.GeometricFiber h t) :=
      (Scheme.pointSmallEtale v.1).sheafFiber.obj F
    let f (v : Scheme.Hom.GeometricFiber h t) :
        ModuleCat.of A ((Etale.sectionsFunctor (ModuleCat A) C).obj
          ((Etale.upperStar (ModuleCat A) (Limits.pullback.fst h t)).obj F)) ⟶ Z v :=
      geometricFibreComponentMap A (Limits.pullback.fst h t) (c v) F ≫
        eqToHom (congrArg (fun y ↦ (Scheme.pointSmallEtale y).sheafFiber.obj F) (he v))
    have hf (v : Scheme.Hom.GeometricFiber h t) :
        etaleSectionPullbackToGlobal A (Limits.pullback.fst h t) p a ha F ≫ f v =
      (Scheme.pointSmallEtale v.1).toPresheafFiber (Scheme.Etale.mk p)
        (Over.homMk (b v) (by exact Limits.pullback.lift_fst _ _ _)) F.obj := by
      dsimp only [f]
      rw [← Category.assoc, pullback_germ]
      rw [germ_transport A F (Scheme.Etale.mk p) _ _ (he v)]
      congr 1
      apply Over.OverMorphism.ext
      exact hb v
    have hgraph (v : Scheme.Hom.GeometricFiber h t) (hv : v ≠ v₀) :
        b v default ∉ Set.range γ.base := by
      intro hx
      have hr : Set.range (b v).base ⊆ Set.range γ.base := by
        rintro _ ⟨y, rfl⟩
        simpa only [Subsingleton.elim y default] using hx
      let l := IsOpenImmersion.lift γ (b v) hr
      have hl : l ≫ γ = b v := IsOpenImmersion.lift_fac _ _ _
      have hlw : l = w := by
        have hh := congrArg (fun k ↦ k ≫ π) hl
        simpa only [Category.assoc, hγ, Category.comp_id, b, π,
          Limits.pullback.lift_snd] using hh
      apply hv
      apply Subtype.ext
      have hh := congrArg (fun k ↦ k ≫ p) hl
      simpa [hlw, b, γ, p, v₀] using hh.symm
    let u := (etaleSectionPullbackToGlobal A (Limits.pullback.fst h t) p a ha F) zext
    have hzero' (v : Scheme.Hom.GeometricFiber h t) (hv : v ≠ v₀) : f v u = 0 := by
      have hh := ConcreteCategory.congr_hom (hf v) zext
      change f v u = _ at hh
      rw [hh]
      have hz' := hzero Ω (b v) (hgraph v hv)
      have hg := germ_transport A F (Scheme.Etale.mk p) (b v ≫ p) v.1
        (by exact Limits.pullback.lift_fst _ _ _) (b v) rfl
      have hval := ConcreteCategory.congr_hom hg zext
      change (Scheme.pointSmallEtale (b v ≫ p)).toPresheafFiber
        (Scheme.Etale.mk p) (Over.homMk (b v)) F.obj zext = 0 at hz'
      simpa only [ModuleCat.comp_apply, hz', map_zero] using hval.symm
    have hvalue : f v₀ u =
        (Scheme.pointSmallEtale (w ≫ lift)).toPresheafFiber
          (Scheme.Etale.mk lift) (Over.homMk w) F.obj z := by
      have hh := ConcreteCategory.congr_hom (hf v₀) zext
      change f v₀ u = _ at hh
      rw [hh]
      have hpoint : (Scheme.pointSmallEtale v₀.1).fiber.map i (Over.homMk w) =
          Over.homMk (b v₀) (by exact Limits.pullback.lift_fst _ _ _) := by
        apply Over.OverMorphism.ext
        change w ≫ γ = b v₀
        apply Limits.pullback.hom_ext
        · simp [γ, b, v₀]
        · simp [γ, b]
      rw [← hpoint]
      have hn := GrothendieckTopology.Point.toPresheafFiber_w_apply
        (Scheme.pointSmallEtale v₀.1) i (Over.homMk w) F.obj zext
      exact hn.symm.trans (congrArg
        ((Scheme.pointSmallEtale v₀.1).toPresheafFiber
          (Scheme.Etale.mk lift) (Over.homMk w) F.obj) hz)
    change canonicalFiniteCoproductMap A _ Z f u = _
    rw [canonical_single A _ Z f v₀ u hzero', hvalue]

end AlgebraicGeometry
