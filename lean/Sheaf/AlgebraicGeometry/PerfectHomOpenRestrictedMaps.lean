module
public import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
import Sheaf.AlgebraicGeometry.PerfectHomOpenTestBijective
import Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare
import Sheaf.AlgebraicGeometry.DerivedOpenTestObject
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Sheaf.AlgebraicGeometry.DerivedAdjoint
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
private theorem conjugated_map_natural
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (k : F ⋙ G ≅ H)
    {M N Q : C} (g : M ⟶ N) (f : F.obj N ⟶ F.obj Q) :
    k.inv.app M ≫ G.map (F.map g ≫ f) ≫ k.hom.app Q =
      H.map g ≫ k.inv.app N ≫ G.map f ≫ k.hom.app Q := by
  rw [G.map_comp]
  have hn := k.inv.naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc (k.inv.app M), ← hn]
  simp only [Category.assoc]

/-- Assemble the transition and cocone compatibility fields from restricted Hom
naturality. Source: Stacks Project, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: new-perfect-hom-open-restricted-maps).

Proof: For each testing object M on B, choose its supported extension X(M),
with M isomorphic to L(X(M)) and restriction bijective on Hom out of X(M).
Lift a morphism M -> L(F_j) uniquely to X(M) -> F_j. Apply h.stageEquiv,
then the canonical cartesian open restriction map, which is bijective on
supported tests, then conjugate by M -> L(X(M)). Do the same at the apex.
Lift a testing arrow M -> N uniquely to X(M) -> X(N); injectivity of
restriction gives compatibility with these lifts. Original Hom naturality and
the naturality of the cartesian pullback comparison give testing naturality.
Lift postcomposition by a transition or cocone leg using functoriality of L.
Apply h.stageMap or h.limitMap, then the cartesian open transport square.
Naturality of Hom transport accounts for conjugation by the chosen testing
isomorphisms. The supplied QCoh hypotheses fill the two remaining fields.
The argument does not assume coherence of the arbitrary supplied e, and
constructs its own compatible equivalences. No target signature changes. -/
theorem perfect_hom_open_restricted_maps_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (hStage : ∀ j : Set.Ici i, schemeDerivedQCohProperty B.toScheme
      ((F ⋙ schemeMVDerivedRestriction Y B).obj j))
    (hLimit : schemeDerivedQCohProperty B.toScheme
      ((schemeMVDerivedRestriction Y B).obj d.pt))
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d) :
    Nonempty (PerfectHomPushPullData R c (B.ι ≫ s)
      ((schemeMVDerivedRestriction Y B).obj Q)
      (F ⋙ schemeMVDerivedRestriction Y B)
      ((schemeMVDerivedRestriction Y B).mapCocone d)) := by
  classical
  have _ := e
  clear e
  let L := schemeMVDerivedRestriction Y B
  let a := Classical.choice (nonempty_derivedPullbackAdjunction B.ι)
  let b (r : Over (Spec (R.obj i))) :=
    pullback.map (B.ι ≫ s) r.hom s r.hom B.ι (𝟙 r.left) (𝟙 _) (by simp) (by simp)
  let σ : L ≅ derivedPullback B.ι :=
    (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  have he (r : Over (Spec (R.obj i))) :
      b r ≫ pullback.fst s r.hom = pullback.fst (B.ι ≫ s) r.hom ≫ B.ι := by
    simp [b, pullback.map]
  let κ (r : Over (Spec (R.obj i))) :=
    perfectHomComposition (b r) (pullback.fst s r.hom) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) (he r)) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r.hom) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r.hom))
  let A (r : Over (Spec (R.obj i))) := derivedPullback (pullback.fst s r.hom)
  let A' (r : Over (Spec (R.obj i))) := derivedPullback (pullback.fst (B.ι ≫ s) r.hom)
  let τ (r : Over (Spec (R.obj i))) {M K : schemeDerivedCategory Y}
      (f : (A r).obj M ⟶ (A r).obj K) : (A' r).obj (L.obj M) ⟶ (A' r).obj (L.obj K) :=
    (κ r).inv.app M ≫ (derivedPullback (b r)).map f ≫ (κ r).hom.app K
  have τn (r : Over (Spec (R.obj i))) {M N K : schemeDerivedCategory Y}
      (g : M ⟶ N) (f : (A r).obj N ⟶ (A r).obj K) :
      τ r ((A r).map g ≫ f) = (A' r).map (L.map g) ≫ τ r f := by
    exact conjugated_map_natural (A r) (derivedPullback (b r)) (L ⋙ A' r) (κ r) g f
  have τt {T T' : Over (Spec (R.obj i))} (g : T' ⟶ T)
      {M K : schemeDerivedCategory Y} (f : (A T).obj M ⟶ (A T).obj K) :
      τ T' (perfectHomMap s g f) = perfectHomMap (B.ι ≫ s) g (τ T f) := by
    exact perfect_hom_open_transport_square s B a g M K f κ (fun _ ↦ rfl)
  let _ := Classical.choice (nonempty_derivedOpenLocalization Y)
  have test (M : schemeDerivedCategory B.toScheme) :
      ∃ N : schemeDerivedCategory Y, Nonempty (M ≅ L.obj N) ∧
        ∀ E : schemeDerivedCategory Y, Function.Bijective (fun f : N ⟶ E ↦ L.map f) := by
    exact Scheme.exists_derivedOpen_testObject Y B M
  choose X δ hx using test
  let t (M : schemeDerivedCategory B.toScheme) : M ≅ L.obj (X M) :=
    Classical.choice (δ M)
  let lift (M : schemeDerivedCategory B.toScheme) (E : schemeDerivedCategory Y) :
      (M ⟶ L.obj E) ≃ (X M ⟶ E) :=
    (Iso.homCongr (t M) (Iso.refl _)).trans (Equiv.ofBijective _ (hx M E)).symm
  have lift_spec (M : schemeDerivedCategory B.toScheme) (E : schemeDerivedCategory Y)
      (f : M ⟶ L.obj E) : L.map (lift M E f) = (t M).inv ≫ f := by
    simpa only [lift, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Equiv.ofBijective_apply] using
      (Equiv.ofBijective _ (hx M E)).apply_symm_apply ((t M).inv ≫ f)
  have τbij (r : Over (Spec (R.obj i))) (M : schemeDerivedCategory B.toScheme) :
      Function.Bijective (fun f : (A r).obj (X M) ⟶ (A r).obj Q ↦ τ r f) := by
    exact perfect_hom_open_test_bijective s B r.hom a (X M) Q (hx M) (κ r) rfl
  let transport (r : Over (Spec (R.obj i))) (M : schemeDerivedCategory B.toScheme) :
      ((A r).obj (X M) ⟶ (A r).obj Q) ≃ ((A' r).obj M ⟶ (A' r).obj (L.obj Q)) :=
    (Equiv.ofBijective _ (τbij r M)).trans
      (Iso.homCongr ((A' r).mapIso (t M)).symm (Iso.refl _))
  let rj (j : Set.Ici i) := Over.mk (Spec.map (R.map (homOfLE j.property)))
  let rLimit := Over.mk (Spec.map (c.ι.app i))
  let es (j : Set.Ici i) (M : schemeDerivedCategory B.toScheme) :=
    (lift M (F.obj j)).trans ((h.stageEquiv j (X M)).trans (transport (rj j) M))
  let el (M : schemeDerivedCategory B.toScheme) :=
    (lift M d.pt).trans ((h.limitEquiv (X M)).trans (transport rLimit M))
  have lift_comp (M : schemeDerivedCategory B.toScheme)
      (E E' : schemeDerivedCategory Y) (f : M ⟶ L.obj E) (g : E ⟶ E') :
      lift M E' (f ≫ L.map g) = lift M E f ≫ g := by
    apply (hx M E').injective
    dsimp only
    rw [L.map_comp, lift_spec, lift_spec, Category.assoc]
  let glift {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N) : X M ⟶ X N :=
    lift M (X N) (g ≫ (t N).hom)
  have glift_spec {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N) :
      L.map (glift g) = (t M).inv ≫ g ≫ (t N).hom := lift_spec _ _ _
  have lift_natural {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N)
      (E : schemeDerivedCategory Y) (f : N ⟶ L.obj E) :
      lift M E (g ≫ f) = glift g ≫ lift N E f := by
    apply (hx M E).injective
    dsimp only
    rw [L.map_comp, lift_spec, glift_spec, lift_spec]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have transport_apply (r : Over (Spec (R.obj i))) (M : schemeDerivedCategory B.toScheme)
      (f : (A r).obj (X M) ⟶ (A r).obj Q) :
      transport r M f = (A' r).map (t M).hom ≫ τ r f := by
    simp only [transport, Equiv.trans_apply, Equiv.ofBijective_apply,
      Iso.homCongr_apply, Iso.symm_inv, Functor.mapIso_hom, Iso.refl_hom,
      Category.comp_id]
  have transport_natural (r : Over (Spec (R.obj i)))
      {M N : schemeDerivedCategory B.toScheme} (g : M ⟶ N)
      (f : (A r).obj (X N) ⟶ (A r).obj Q) :
      transport r M ((A r).map (glift g) ≫ f) =
        (A' r).map g ≫ transport r N f := by
    rw [transport_apply, transport_apply, τn, ← Category.assoc, ← Functor.map_comp,
      glift_spec]
    simp only [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]
  have mapn {T T' : Over (Spec (R.obj i))} (g : T' ⟶ T)
      {M N K : schemeDerivedCategory B.toScheme} (v : M ⟶ N)
      (f : (A' T).obj N ⟶ (A' T).obj K) :
      perfectHomMap (B.ι ≫ s) g ((A' T).map v ≫ f) =
        (A' T').map v ≫ perfectHomMap (B.ι ≫ s) g f := by
    exact conjugated_map_natural (A' T) (derivedPullback (baseChangeMap (B.ι ≫ s) g))
      (A' T') (perfectHomComparison (B.ι ≫ s) g).symm v f
  have transport_map {T T' : Over (Spec (R.obj i))} (g : T' ⟶ T)
      (M : schemeDerivedCategory B.toScheme)
      (f : (A T).obj (X M) ⟶ (A T).obj Q) :
      transport T' M (perfectHomMap s g f) =
        perfectHomMap (B.ι ≫ s) g (transport T M f) := by
    rw [transport_apply, transport_apply, τt, mapn]
  refine ⟨{
    stageQCoh := hStage
    limitQCoh := hLimit
    stageEquiv := es
    limitEquiv := el
    stageNatural := ?_
    limitNatural := ?_
    stageMap := ?_
    limitMap := ?_ }⟩
  · intro j M N g f
    change transport (rj j) M (h.stageEquiv j (X M) (lift M (F.obj j) (g ≫ f))) = _
    exact (congrArg (fun v ↦ transport (rj j) M (h.stageEquiv j (X M) v))
      (lift_natural g (F.obj j) f)).trans
      ((congrArg (transport (rj j) M)
        (h.stageNatural j (X M) (X N) (glift g) (lift N (F.obj j) f))).trans
        (transport_natural (rj j) g (h.stageEquiv j (X N) (lift N (F.obj j) f))))
  · intro M N g f
    change transport rLimit M (h.limitEquiv (X M) (lift M d.pt (g ≫ f))) = _
    exact (congrArg (fun v ↦ transport rLimit M (h.limitEquiv (X M) v))
      (lift_natural g d.pt f)).trans
      ((congrArg (transport rLimit M)
        (h.limitNatural (X M) (X N) (glift g) (lift N d.pt f))).trans
        (transport_natural rLimit g (h.limitEquiv (X N) (lift N d.pt f))))
  · intro j k hjk M f
    change transport (rj k) M
      (h.stageEquiv k (X M) (lift M (F.obj k) (f ≫ L.map (F.map (homOfLE hjk))))) = _
    refine (congrArg (fun v ↦ transport (rj k) M (h.stageEquiv k (X M) v))
      (lift_comp M (F.obj j) (F.obj k) f (F.map (homOfLE hjk)))).trans ?_
    refine (congrArg (transport (rj k) M)
      (h.stageMap j k hjk (X M) (lift M (F.obj j) f))).trans ?_
    exact transport_map
      (T := rj j) (T' := rj k)
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp [rj]; rw [← Spec.map_comp, ← R.map_comp]; rfl)) M
      (h.stageEquiv j (X M) (lift M (F.obj j) f))
  · intro j M f
    change transport rLimit M
      (h.limitEquiv (X M) (lift M d.pt (f ≫ L.map (d.ι.app j)))) = _
    refine (congrArg (fun v ↦ transport rLimit M (h.limitEquiv (X M) v))
      (lift_comp M (F.obj j) d.pt f (d.ι.app j))).trans ?_
    refine (congrArg (transport rLimit M)
      (h.limitMap j (X M) (lift M (F.obj j) f))).trans ?_
    exact transport_map
      (T := rj j) (T' := rLimit)
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp [rj, rLimit]; rw [← Spec.map_comp, c.w (homOfLE j.property)])) M
      (h.stageEquiv j (X M) (lift M (F.obj j) f))
end
end AlgebraicGeometry
