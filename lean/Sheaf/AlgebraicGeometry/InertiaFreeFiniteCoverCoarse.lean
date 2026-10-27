module

public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
import Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties
import Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial
import Sheaf.AlgebraicGeometry.DmCoarseProperLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.StackProperLocallyQuasiFiniteComposition
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Inertia-free finite stack covers over a coarse scheme

Source: Stacks, Tag 0DUT (Keel--Mori), Tag 045H (trivial-inertia DM stacks),
Tag 03XX and Tag 02LS; the finite-cover consequence used in Pikaart--de Jong,
§2.3.5 and Remark 2.3.7 (blueprint: lem-sfb-inertia-free-finite-cover-coarse).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_map_exists {S : Scheme.{u}}
    {P R : (Over S)ᵒᵖ ⥤ Type u}
    (f : BasedFunctor (discreteModuli P) (discreteModuli R)) :
    ∃ a : P ⟶ R, Nonempty (ModuliTwoIso f (discreteModuliMap a)) := by
  classical
  let c : Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) :=
    { pt := R
      ι :=
        { app := fun x ↦ yoneda.map (eqToHom (f.w_obj x).symm) ≫ (f.obj x).hom
          naturality := by
            intro x y g
            dsimp
            rw [Category.comp_id, ← Category.assoc, ← yoneda.map_comp]
            have hw := (eqToIso f.w).inv.naturality g
            simp only [eqToIso.inv, eqToHom_app] at hw
            change g.left ≫ eqToHom (f.w_obj y).symm =
              eqToHom (f.w_obj x).symm ≫ (f.map g).left at hw
            change yoneda.map (g.left ≫ eqToHom (f.w_obj y).symm) ≫ _ = _
            rw [hw, yoneda.map_comp, Category.assoc]
            rw [CostructuredArrow.w (f.map g)] } }
  let a := (Presheaf.isColimitTautologicalCocone P).desc c
  have ha (x : (discreteModuli P).obj) :
      x.hom ≫ a = yoneda.map (eqToHom (f.w_obj x).symm) ≫ (f.obj x).hom :=
    (Presheaf.isColimitTautologicalCocone P).fac c x
  let e : f.toFunctor ≅ (discreteModuliMap a).toFunctor :=
    NatIso.ofComponents (fun x ↦ CostructuredArrow.isoMk (eqToIso (f.w_obj x)) (by
      change yoneda.map (eqToHom (f.w_obj x)) ≫ (x.hom ≫ a) = _
      rw [ha, ← Category.assoc, ← yoneda.map_comp]
      simp)) (by
        intro x y g
        apply CostructuredArrow.hom_ext
        change (f.map g).left ≫ eqToHom (f.w_obj y) =
          eqToHom (f.w_obj x) ≫ g.left
        simpa only [eqToIso.hom, eqToHom_app, Functor.comp_map, discreteModuli,
          BasedCategory.ofFunctor, CostructuredArrow.proj_map] using
          (eqToIso f.w).hom.naturality g)
  refine ⟨a, ⟨⟨e, ?_⟩⟩⟩
  intro x
  exact IsHomLift.of_fac _ _ _ (f.w_obj x) rfl (by
    change 𝟙 _ = eqToHom (f.w_obj x).symm ≫ eqToHom (f.w_obj x) ≫ eqToHom (Eq.refl _)
    simp)

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_twoiso_eq {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {P : (Over S)ᵒᵖ ⥤ Type u}
    {f g : BasedFunctor A (discreteModuli P)} (α : ModuliTwoIso f g) : f = g := by
  have hobj (x : A.obj) : f.obj x = g.obj x := by
    apply CostructuredArrow.obj_ext _ _ ((f.w_obj x).trans (g.w_obj x).symm)
    have := α.property x
    have h := IsHomLift.fac' (discreteModuli P).p (𝟙 (A.p.obj x)) (α.val.hom.app x)
    have he : (α.val.hom.app x).left =
        eqToHom ((f.w_obj x).trans (g.w_obj x).symm) := by
      simpa only [discreteModuli, BasedCategory.ofFunctor, CostructuredArrow.proj_map,
        Category.comp_id, Category.id_comp, eqToHom_trans] using h
    rw [← he]
    exact CostructuredArrow.w (α.val.hom.app x)
  have hf : f.toFunctor = g.toFunctor := Functor.ext_of_iso α.val hobj (by
    intro x
    apply CostructuredArrow.hom_ext
    have := α.property x
    have h := IsHomLift.fac' (discreteModuli P).p (𝟙 (A.p.obj x)) (α.val.hom.app x)
    simpa only [discreteModuli, BasedCategory.ofFunctor, CostructuredArrow.proj_map,
      CostructuredArrow.eqToHom_left, Category.comp_id, Category.id_comp, eqToHom_trans] using h)
  cases f
  cases g
  cases hf
  rfl

private theorem discrete_map_strict {S : Scheme.{u}}
    {P R : (Over S)ᵒᵖ ⥤ Type u}
    (f : BasedFunctor (discreteModuli P) (discreteModuli R)) :
    ∃ a : P ⟶ R, f = discreteModuliMap a := by
  obtain ⟨a, ⟨α⟩⟩ := discrete_map_exists f
  exact ⟨a, discrete_twoiso_eq α⟩

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_fibred {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u) :
    IsFibredInGroupoids (discreteModuli P) := by
  have hc {x y : (discreteModuli P).obj} (a : x ⟶ y) :
      (discreteModuli P).p.IsStronglyCartesian ((discreteModuli P).p.map a) a := by
    constructor
    intro z g b hb
    have : (discreteModuli P).p.IsHomLift (g ≫ a.left) b := hb
    let d : z ⟶ x := CostructuredArrow.homMk g (by
      rw [← CostructuredArrow.w a, ← Category.assoc, ← yoneda.map_comp]
      have hg : g ≫ a.left = b.left := by
        simpa only [discreteModuli, BasedCategory.ofFunctor,
          CostructuredArrow.proj_map] using
          (IsHomLift.eq_of_isHomLift (discreteModuli P).p (g ≫ a.left) b)
      rw [hg, CostructuredArrow.w b])
    refine ⟨d, ⟨by exact IsHomLift.map _ d, ?_⟩, ?_⟩
    · apply CostructuredArrow.hom_ext
      exact IsHomLift.eq_of_isHomLift (discreteModuli P).p (g ≫ a.left) b
    · intro d' hd'
      apply CostructuredArrow.hom_ext
      have := hd'.1
      exact (IsHomLift.eq_of_isHomLift (discreteModuli P).p g d').symm
  refine ⟨Functor.IsFibered.of_exists_isStronglyCartesian ?_, fun a ↦ hc a⟩
  intro x T a
  let y : (discreteModuli P).obj := CostructuredArrow.mk (yoneda.map a ≫ x.hom)
  let b : y ⟶ x := CostructuredArrow.homMk a
  exact ⟨y, b, hc b⟩

set_option backward.isDefEq.respectTransparency false in
private theorem scheme_moduli_stack {S : Scheme.{u}} (Q : Over S) :
    IsModuliStack (discreteModuli (yoneda.obj Q)) := by
  classical
  refine ⟨discrete_fibred _, ?_⟩
  intro T R hR D hD
  have hb : Nonempty (IsColimit R.arrows.cocone) :=
    R.forallYonedaIsSheaf_iff_colimit.mp (fun W ↦
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.etaleTopology.over S) (P := yoneda.obj W)) R hR)
  let b := hb.some
  let a (i : R.arrows.category) : (D.obj i).left ⟶ T :=
    eqToHom (Functor.congr_obj hD i) ≫ i.obj.hom
  let dc : Cocone (D ⋙ (discreteModuli (yoneda.obj Q)).p) :=
    { pt := T
      ι := { app := a
             naturality := by
               intro i j g
               have h := (eqToIso hD).hom.naturality g
               dsimp [a]
               simp only [eqToIso.hom, eqToHom_app, Functor.comp_map] at h
               rw [← Category.assoc, h, Category.assoc]
               exact congrArg (fun t ↦ eqToHom (Functor.congr_obj hD i) ≫ t)
                 (Over.w g.hom) } }
  have hdc : IsColimit dc := by
    apply IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv (eqToIso hD) R.arrows.cocone).symm b)
    exact Cocone.ext (Iso.refl _) (by intro i; simp [dc, a, eqToHom_app])
  let qc : Cocone (D ⋙ (discreteModuli (yoneda.obj Q)).p) :=
    { pt := Q
      ι := { app := fun i ↦ yoneda.preimage (D.obj i).hom
             naturality := by
               intro i j g
               apply yoneda.map_injective
               change yoneda.map (D.map g).left ≫
                 yoneda.map (yoneda.preimage (D.obj j).hom) =
                   yoneda.map (yoneda.preimage (D.obj i).hom) ≫ yoneda.map (𝟙 Q)
               rw [yoneda.map_preimage, yoneda.map_preimage, yoneda.map_id,
                 Category.comp_id]
               exact CostructuredArrow.w (D.map g) } }
  let qT := hdc.desc qc
  let c : Cocone D :=
    { pt := CostructuredArrow.mk (yoneda.map qT)
      ι := { app := fun i ↦ CostructuredArrow.homMk (a i) (by
               change yoneda.map (a i) ≫ yoneda.map qT = _
               rw [← yoneda.map_comp, hdc.fac qc i]
               exact yoneda.map_preimage _)
             naturality := by
               intro i j g
               apply CostructuredArrow.hom_ext
               exact dc.ι.naturality g } }
  refine ⟨c, rfl, ⟨?_⟩, ?_⟩
  · refine
      { desc := fun s ↦ CostructuredArrow.homMk
          (hdc.desc (((discreteModuli (yoneda.obj Q)).p).mapCocone s)) ?_
        fac := ?_
        uniq := ?_ }
    · change yoneda.map (hdc.desc ((discreteModuli (yoneda.obj Q)).p.mapCocone s)) ≫
        s.pt.hom = yoneda.map qT
      rw [← yoneda.map_preimage s.pt.hom, ← yoneda.map_comp]
      congr 1
      apply hdc.hom_ext
      intro i
      rw [← Category.assoc, hdc.fac, hdc.fac]
      apply yoneda.map_injective
      change yoneda.map (s.ι.app i).left ≫
        yoneda.map (yoneda.preimage s.pt.hom) =
          yoneda.map (yoneda.preimage (D.obj i).hom)
      rw [yoneda.map_preimage, yoneda.map_preimage]
      exact CostructuredArrow.w (s.ι.app i)
    · intro s i
      apply CostructuredArrow.hom_ext
      exact hdc.fac _ i
    · intro s m hm
      apply CostructuredArrow.hom_ext
      apply hdc.hom_ext
      intro i
      change dc.ι.app i ≫ m.left =
        dc.ι.app i ≫ hdc.desc ((discreteModuli (yoneda.obj Q)).p.mapCocone s)
      rw [hdc.fac]
      exact congrArg (fun a ↦ a.left) (hm i)
  · intro i
    change a i ≫ 𝟙 _ = a i
    exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_pullback {S : Scheme.{u}}
    {L P R H : (Over S)ᵒᵖ ⥤ Type u} {a : L ⟶ P} {b : L ⟶ R}
    {f : P ⟶ H} {g : R ⟶ H} (sq : IsPullback a b f g) :
    ∃ e : BasedFunctor (discreteModuli L)
        (moduliTwoFiberProduct (discreteModuliMap f) (discreteModuliMap g)),
      e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso
        (e.comp (moduliTwoFiberFst (discreteModuliMap f) (discreteModuliMap g)))
        (discreteModuliMap a)) := by
  classical
  let θ : (discreteModuliMap a).comp (discreteModuliMap f) ≅
      (discreteModuliMap b).comp (discreteModuliMap g) :=
    BasedNatIso.mkNatIso
      (NatIso.ofComponents (fun x ↦ CostructuredArrow.isoMk (Iso.refl _) (by
        change yoneda.map (𝟙 x.left) ≫ ((x.hom ≫ b) ≫ g) = (x.hom ≫ a) ≫ f
        rw [yoneda.map_id, Category.id_comp, Category.assoc, Category.assoc, sq.w]))
        (by intro x y h; apply CostructuredArrow.hom_ext; rfl))
      (by intro x; exact IsHomLift.of_fac _ _ _ rfl rfl (by rfl))
  let e := moduliTwoFiberLift (discreteModuliMap a) (discreteModuliMap b) θ
  have hefaithful : e.toFunctor.Faithful :=
    { map_injective := by
        intro x y h k hhk
        apply CostructuredArrow.hom_ext
        exact congrArg (fun t ↦ t.hom.left.left) hhk }
  have hefull : e.toFunctor.Full := by
    constructor
    intro x y h
    have hbase : h.hom.left.left = h.hom.right.left := by
      have hw := congrArg (fun t ↦ t.left) h.hom.w
      change h.hom.left.left ≫ 𝟙 _ = 𝟙 _ ≫ h.hom.right.left at hw
      simpa only [Category.comp_id, Category.id_comp] using hw
    refine ⟨CostructuredArrow.homMk h.hom.left.left ?_, ?_⟩
    · apply sq.hom_ext
      · have hh := CostructuredArrow.w h.hom.left
        change yoneda.map h.hom.left.left ≫ (y.hom ≫ a) = x.hom ≫ a at hh
        simpa only [Category.assoc] using hh
      · have hh := CostructuredArrow.w h.hom.right
        change yoneda.map h.hom.right.left ≫ (y.hom ≫ b) = x.hom ≫ b at hh
        simpa only [Category.assoc, hbase] using hh
    · apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · apply CostructuredArrow.hom_ext
        rfl
      · apply CostructuredArrow.hom_ext
        exact hbase
  have heess : e.toFunctor.EssSurj := by
    constructor
    intro z
    have : IsIso z.obj.hom := z.property.1
    have : IsIso z.obj.hom.left := (discreteModuli H).p.map_isIso z.obj.hom
    let l := sq.lift z.obj.left.hom
      (yoneda.map z.obj.hom.left ≫ z.obj.right.hom) (by
        have hh := (CostructuredArrow.w z.obj.hom).symm
        change z.obj.left.hom ≫ f = yoneda.map z.obj.hom.left ≫ (z.obj.right.hom ≫ g)
          at hh
        simpa only [Category.assoc] using hh)
    let x : (discreteModuli L).obj := CostructuredArrow.mk l
    refine ⟨x, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    refine Comma.isoMk
      (CostructuredArrow.isoMk (Iso.refl _) ?_)
      (CostructuredArrow.isoMk (asIso z.obj.hom.left) ?_) ?_
    · change yoneda.map (𝟙 _) ≫ z.obj.left.hom = l ≫ a
      simp [l]
    · change yoneda.map z.obj.hom.left ≫ z.obj.right.hom = l ≫ b
      exact (sq.lift_snd _ _ _).symm
    · apply CostructuredArrow.hom_ext
      change (𝟙 _) ≫ z.obj.hom.left = (𝟙 _) ≫ z.obj.hom.left
      rfl
  refine ⟨e, ⟨hefaithful, hefull, heess⟩, ⟨⟨Iso.refl _, ?_⟩⟩⟩
  intro x
  exact IsHomLift.id (discreteModuliMap a |>.w_obj x)

private theorem based_ext {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {f g : BasedFunctor A B} (h : f.toFunctor = g.toFunctor) : f = g := by
  cases f
  cases g
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_map_id {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u) :
    discreteModuliMap (𝟙 P) = BasedFunctor.id (discreteModuli P) := by
  apply based_ext
  apply CategoryTheory.Functor.ext
    (fun x ↦ CostructuredArrow.obj_ext _ _ rfl (by simp))

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_map_comp {S : Scheme.{u}}
    {P R H : (Over S)ᵒᵖ ⥤ Type u} (a : P ⟶ R) (b : R ⟶ H) :
    (discreteModuliMap a).comp (discreteModuliMap b) = discreteModuliMap (a ≫ b) := by
  apply based_ext
  apply CategoryTheory.Functor.ext
    (fun x ↦ CostructuredArrow.obj_ext _ _ rfl (by simp))

set_option backward.isDefEq.respectTransparency false in
private theorem scheme_moduli_dm {S : Scheme.{u}} (Q : Over S) :
    IsDeligneMumfordModuliStack (discreteModuli (yoneda.obj Q)) := by
  classical
  refine ⟨scheme_moduli_stack Q, ?_, Q, BasedFunctor.id _, ?_⟩
  · intro T U a b
    obtain ⟨a', rfl⟩ := discrete_map_strict a
    obtain ⟨b', rfl⟩ := discrete_map_strict b
    let f := yoneda.preimage a'
    let g := yoneda.preimage b'
    have sq : IsPullback (yoneda.map (pullback.fst f g))
        (yoneda.map (pullback.snd f g)) a' b' := by
      have hh := (IsPullback.of_hasPullback f g).map yoneda
      dsimp [f, g] at hh
      simpa only [yoneda.map_preimage] using hh
    obtain ⟨e, he, _⟩ := discrete_pullback sq
    exact ⟨AlgebraicSpace.schemeSpace (pullback f g), e, he⟩
  · intro T t
    obtain ⟨a, rfl⟩ := discrete_map_strict t
    have sq : IsPullback (yoneda.map (𝟙 T)) a a (𝟙 _) := by
      rw [yoneda.map_id]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    have hh := discrete_pullback sq
    rw [discrete_map_id] at hh
    obtain ⟨e, he, hfst⟩ := hh
    refine ⟨AlgebraicSpace.schemeSpace T, yoneda.map (𝟙 T), ⟨e, he, hfst⟩, ?_, ?_⟩
    · intro U b hb
      have ht := AlgebraicSpace.representable_etale_scheme_tests (S := S)
      change Etale (yoneda.preimage (b ≫ yoneda.map (𝟙 T))).left
      change yoneda.obj U ⟶ yoneda.obj T at b
      simp only [yoneda.map_id]
      apply (ht.2.2.2.2.2.2.2.1 U T (yoneda.preimage b)).mp
      simpa only [yoneda.map_preimage] using hb
    · intro x
      have ht := AlgebraicSpace.representable_etale_scheme_tests (S := S)
      refine ⟨T, 𝟙 _, ?_, x, ?_⟩
      · simpa only [yoneda.map_id] using
          (ht.2.2.2.2.2.2.2.1 T T (𝟙 T)).mpr (inferInstance : Etale (𝟙 T.left))
      · simp

set_option backward.isDefEq.respectTransparency false in
private theorem discrete_based_inverse {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type u} {A : BasedCategory.{v₁, w₁} (Over S)}
    (e : BasedFunctor (discreteModuli P) A) (he : e.toFunctor.IsEquivalence) :
    ∃ d : BasedFunctor A (discreteModuli P), d.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (d.comp e) (BasedFunctor.id A)) := by
  classical
  have := he
  let I := e.toFunctor.inv
  let c := e.toFunctor.asEquivalence.counitIso
  let ρ : I ⋙ (discreteModuli P).p ≅ A.p :=
    Functor.isoWhiskerLeft I (eqToIso e.w).symm ≪≫
      (Functor.associator I e.toFunctor A.p).symm ≪≫
      Functor.isoWhiskerRight c A.p ≪≫ Functor.leftUnitor A.p
  let d : BasedFunctor A (discreteModuli P) :=
    { toFunctor :=
        { obj := fun x ↦ CostructuredArrow.mk
            (yoneda.map (ρ.inv.app x) ≫ (I.obj x).hom)
          map := fun {x y} g ↦ CostructuredArrow.homMk (A.p.map g) (by
            change yoneda.map (A.p.map g) ≫
                (yoneda.map (ρ.inv.app y) ≫ (I.obj y).hom) = _
            rw [← Category.assoc, ← yoneda.map_comp, ρ.inv.naturality,
              yoneda.map_comp, Category.assoc]
            exact congrArg (fun t ↦ yoneda.map (ρ.inv.app x) ≫ t)
              (CostructuredArrow.w (I.map g))) }
      w := rfl }
  let σ : d.toFunctor ≅ I := NatIso.ofComponents
    (fun x ↦ CostructuredArrow.isoMk (ρ.symm.app x) (by rfl))
    (by intro x y g; apply CostructuredArrow.hom_ext; exact ρ.inv.naturality g)
  let γ : (d.comp e).toFunctor ≅ (BasedFunctor.id A).toFunctor :=
    Functor.isoWhiskerRight σ e.toFunctor ≪≫ c
  have hd : d.toFunctor.IsEquivalence := Functor.isEquivalence_of_iso σ.symm
  refine ⟨d, hd, ⟨⟨γ, ?_⟩⟩⟩
  intro x
  apply IsHomLift.of_fac _ _ _ ((d.comp e).w_obj x) rfl
  change 𝟙 _ = eqToHom ((d.comp e).w_obj x).symm ≫
    A.p.map (e.map (σ.hom.app x) ≫ c.hom.app x) ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.comp_id, A.p.map_comp]
  have hw := Functor.congr_hom e.w (σ.hom.app x)
  simp only [Functor.comp_map] at hw
  rw [hw]
  change 𝟙 _ = eqToHom _ ≫ (eqToHom _ ≫ ρ.inv.app x ≫ eqToHom _) ≫ _
  simp only [← Category.assoc, eqToHom_trans]
  dsimp [ρ]
  simp only [Category.id_comp, Category.comp_id, eqToHom_app, Functor.comp_obj, Category.assoc,
    eqToHom_trans, eqToHom_refl]
  rw [← A.p.map_comp, Iso.inv_hom_id_app]
  exact (A.p.map_id x).symm


set_option backward.isDefEq.respectTransparency false in
private theorem discrete_iso_equivalence {S : Scheme.{u}}
    {P R : (Over S)ᵒᵖ ⥤ Type u} (η : P ≅ R) :
    (discreteModuliMap η.hom).toFunctor.IsEquivalence := by
  change (CostructuredArrow.mapIso η).functor.IsEquivalence
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem twofiber_right_equivalence {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)}
    {B : BasedCategory.{v₂, w₂} (Over S)}
    {P R : (Over S)ᵒᵖ ⥤ Type u}
    (t : BasedFunctor A (discreteModuli R))
    (f : BasedFunctor B (discreteModuli R))
    (e : BasedFunctor (discreteModuli P) B) (he : e.toFunctor.IsEquivalence) :
    ∃ m : BasedFunctor (moduliTwoFiberProduct t (e.comp f))
        (moduliTwoFiberProduct t f),
      m.toFunctor.IsEquivalence ∧
        m.comp (moduliTwoFiberFst t f) = moduliTwoFiberFst t (e.comp f) := by
  classical
  have := he
  obtain ⟨d, hd, ⟨γ⟩⟩ := discrete_based_inverse e he
  let m := moduliTwoFiberMapRight t e (Iso.refl (e.comp f))
  have hfaithful : m.toFunctor.Faithful := by
    constructor
    intro x y a b h
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact congrArg (fun z ↦ z.hom.left) h
    · apply e.toFunctor.map_injective
      exact congrArg (fun z ↦ z.hom.right) h
  have hfull : m.toFunctor.Full := by
    constructor
    intro x y h
    let a := e.toFunctor.preimage h.hom.right
    refine ⟨ObjectProperty.homMk
      { left := h.hom.left
        right := a
        w := ?_ }, ?_⟩
    · have hh := h.hom.w
      change t.map h.hom.left ≫ (y.obj.hom ≫ 𝟙 _) =
        (x.obj.hom ≫ 𝟙 _) ≫ f.map h.hom.right at hh
      change t.map h.hom.left ≫ y.obj.hom = x.obj.hom ≫ f.map (e.map a)
      dsimp [a]
      simpa only [Category.comp_id, Functor.map_preimage] using hh
    · apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · rfl
      · exact e.toFunctor.map_preimage _
  have hess : m.toFunctor.EssSurj := by
    constructor
    intro z
    have : IsIso z.obj.hom := z.property.1
    have := z.property.2
    have hγ : B.p.IsHomLift (𝟙 (B.p.obj z.obj.right))
        (γ.val.app z.obj.right).hom := γ.property z.obj.right
    let δ := γ.val.app z.obj.right
    have : (discreteModuli R).p.IsHomLift
        (𝟙 (B.p.obj z.obj.right)) (f.map δ.inv) := by
      have : B.p.IsHomLift (𝟙 (B.p.obj z.obj.right)) δ.inv :=
        IsHomLift.lift_id_inv B.p _ (γ.val.app z.obj.right)
      exact f.preserves_isHomLift _ _
    let x : (moduliTwoFiberProduct t (e.comp f)).obj :=
      ⟨⟨z.obj.left, d.obj z.obj.right, z.obj.hom ≫ f.map δ.inv⟩,
        ⟨by infer_instance, by
          exact IsHomLift.comp_lift_id_right' (discreteModuli R).p
            (𝟙 (A.p.obj z.obj.left)) z.obj.hom (B.p.obj z.obj.right) (f.map δ.inv)⟩⟩
    refine ⟨x, ⟨ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) δ ?_)⟩⟩
    change t.map (𝟙 _) ≫ z.obj.hom =
      (z.obj.hom ≫ f.map δ.inv) ≫ 𝟙 _ ≫ f.map δ.hom
    simp only [Category.id_comp, Category.assoc]
    rw [← f.map_comp, δ.inv_hom_id]
    change t.toFunctor.map (𝟙 _) ≫ z.obj.hom = z.obj.hom ≫ f.toFunctor.map (𝟙 _)
    rw [t.toFunctor.map_id, f.toFunctor.map_id, Category.id_comp, Category.comp_id]
  exact ⟨m, ⟨hfaithful, hfull, hess⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- An inertia-free finite representable cover is an algebraic space, and its
composite to the given coarse scheme is finite and represented by a finite scheme.
There is no linear-reductivity or surjectivity hypothesis.
Source: Stacks, Tags 0DUT, 045H, 03XX and 02LS, applied as in Pikaart--de Jong,
§2.3.5 and Remark 2.3.7 (blueprint: lem-sfb-inertia-free-finite-cover-coarse).

Proof: (1) lem-sfb-representable-finite-stack-properties makes the source DM and
makes the finite cover proper and locally quasi-finite. (2) The geometric
hypothesis and lem-sfb-dm-geometric-inertia-trivial identify the source with an
algebraic space, including on nonreduced test schemes. (3) By
lem-sfb-dm-coarse-proper-locally-quasifinite, finite type, finite diagonal and the
coarse universal property make the coarse morphism proper and locally quasi-finite.
(4) The scheme Q is a DM stack: subcanonicity of the big etale topology glues
its morphisms, its atlas is the identity, and its diagonal is represented by scheme
fibre products. The scheme-space construction and representable etale scheme tests
identify the atlas projections. Apply
lem-sfb-stack-proper-locally-quasifinite-composition and its compatibility with
algebraic spaces. (5) lem-a1-separated-locally-qf-space-representable represents
the resulting separated locally quasi-finite space over Q by a scheme Z over Q.
(6) pqf-lem-proper-lqf-finite makes Z → Q finite. All the equivalences are over Q,
so the represented map is precisely the specified composite. No step uses
linear reductivity of stabilizers. For every scheme test of the composite, base
change the finite scheme map g and compose its pullback presentation with the
2-fibre-product equivalence induced by the equivalence h_Z → Y. The first projection
is retained by both functors, giving precisely representable finiteness. -/
theorem inertiaFreeFiniteCoverCoarse (k : Type u) [Field k]
    (X : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hX : IsDeligneMumfordModuliStack X) (hft : HasFiniteTypeEtaleModuliAtlas X)
    (hdiag : HasFiniteModuliDiagonal X) (hY : IsModuliStack Y)
    (Q : Over (Spec (.of k))) (q : BasedFunctor X (discreteModuli (yoneda.obj Q)))
    (hq : IsCoarseModuliScheme X Q q) (ν : BasedFunctor Y X)
    (hν : IsRepresentableFiniteModuliMap ν)
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))
      (y : Functor.Fiber Y.p (Over.mk a)) (α : y ≅ y), α = Iso.refl y) :
    (∃ (E : AlgebraicSpace (Spec (.of k)))
      (e : BasedFunctor (discreteModuli E.obj.obj) Y), e.toFunctor.IsEquivalence) ∧
    IsRepresentableFiniteModuliMap (ν.comp q) ∧
    ∃ (Z : Over (Spec (.of k))) (g : Z ⟶ Q), IsFinite g.left ∧
      ∃ e : BasedFunctor (discreteModuli (yoneda.obj Z)) Y,
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (ν.comp q)) (discreteModuliMap (yoneda.map g))) := by
  classical
  obtain ⟨hYdm, hνp, hνq⟩ := representableFinite_stack_properties _ X Y ν hX hY hν
  have hgeom' : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (.of Ω) ⟶ Spec (.of k)) (y : Functor.Fiber Y.p (Over.mk a))
      (α : y ⟶ y), α = 𝟙 y := by
    intro Ω _ _ a y α
    have := hY.1.2 α.val
    have : Y.p.IsHomLift (𝟙 (Over.mk a)) α.val := α.property
    have : IsIso (Y.p.map α.val) := by
      rw [IsHomLift.fac' Y.p (𝟙 (Over.mk a)) α.val]
      infer_instance
    have : IsIso α.val := Functor.IsStronglyCartesian.isIso_of_base_isIso
      Y.p (Y.p.map α.val) α.val
    let β : y ≅ y :=
      { hom := α
        inv := ⟨inv α.val, inferInstance⟩
        hom_inv_id := by apply Subtype.ext; exact IsIso.hom_inv_id α.val
        inv_hom_id := by apply Subtype.ext; exact IsIso.inv_hom_id α.val }
    exact congrArg Iso.hom (hgeom Ω a y β)
  obtain ⟨hspace, _⟩ := dm_geometric_inertia_trivial Y hYdm hgeom'
  obtain ⟨hqp, hqq⟩ := dmCoarseProperLocallyQuasiFinite k X hX hft hdiag Q q hq
  have hQdm := scheme_moduli_dm Q
  obtain ⟨hfp, hfq⟩ := proper_locallyQuasiFinite_moduli_comp
    hYdm hX hQdm ν q hνp hqp hνq hqq
  obtain ⟨E, e, he⟩ := hspace
  obtain ⟨f, hf⟩ := discrete_map_strict (e.comp (ν.comp q))
  obtain ⟨d, hd, ⟨γ⟩⟩ := discrete_based_inverse e he
  have htrans := proper_locallyQuasiFinite_moduli_equivalence
    hYdm hQdm (ν.comp q) (e.comp (ν.comp q)) d (BasedFunctor.id _) hd
    (show (𝟭 _).IsEquivalence from inferInstance) (by
      refine ⟨⟨Functor.isoWhiskerRight γ.val (ν.comp q).toFunctor, ?_⟩⟩
      intro x
      have := γ.property x
      exact (ν.comp q).preserves_isHomLift _ _)
  have hEp := htrans.1.mp hfp
  have hEq := htrans.2.mp hfq
  rw [hf] at hEp hEq
  let fspace : E ⟶ AlgebraicSpace.schemeSpace Q := ObjectProperty.homMk ⟨f⟩
  have hproper := (proper_locallyQuasiFinite_discrete_space fspace).1.mp hEp
  have hsep := hproper.2.2.2
  have hchart := locallyQuasiFinite_space_chart_to_scheme E Q f hEq
  obtain ⟨Z, g, η, hη⟩ :=
    AlgebraicSpace.exists_scheme_of_separated_locally_quasi_finite Q E f hchart hsep
  let eZ := (discreteModuliMap η.hom).comp e
  have hηe := discrete_iso_equivalence η
  have heZ : eZ.toFunctor.IsEquivalence := by
    have := he
    have := hηe
    exact Functor.isEquivalence_trans _ _
  have heZg : eZ.comp (ν.comp q) = discreteModuliMap (yoneda.map g) := by
    change (discreteModuliMap η.hom).comp (e.comp (ν.comp q)) = _
    rw [hf, discrete_map_comp, hη]
  have hzprops := proper_locallyQuasiFinite_moduli_equivalence
    (scheme_moduli_dm Z) hQdm (eZ.comp (ν.comp q)) (ν.comp q)
    eZ (BasedFunctor.id _) heZ (show (𝟭 _).IsEquivalence from inferInstance)
    ⟨⟨Iso.refl _, fun x ↦ IsHomLift.id ((eZ.comp (ν.comp q)).w_obj x)⟩⟩
  have hzp := hzprops.1.mpr hfp
  have hzq := hzprops.2.mpr hfq
  rw [heZg] at hzp hzq
  have := (proper_locallyQuasiFinite_discrete_scheme g).1.mp hzp
  have hlq := (proper_locallyQuasiFinite_discrete_scheme g).2.mp hzq
  have := ((Scheme.Hom.isLocallyQuasiFinite_iff g.left).mp hlq).1
  have hg : IsFinite g.left := IsFinite.of_isProper_of_locallyQuasiFinite g.left
  refine ⟨⟨E, e, he⟩, ?_, Z, g, hg, eZ, heZ, ?_⟩
  · intro T t
    obtain ⟨a, rfl⟩ := discrete_map_strict t
    let r := yoneda.preimage a
    let p := pullback.fst r g
    have hp : IsFinite p.left := by
      exact MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback r g).map (Over.forget _)).flip hg
    have sq := (IsPullback.of_hasPullback r g).map yoneda
    simp only [r, yoneda.map_preimage] at sq
    obtain ⟨b, hb, ⟨β⟩⟩ := discrete_pullback sq
    have hmexists := twofiber_right_equivalence (discreteModuliMap a) (ν.comp q) eZ heZ
    rw [heZg] at hmexists
    obtain ⟨m, hm, hmf⟩ := hmexists
    refine ⟨pullback r g, p, hp, b.comp m, ?_, ?_⟩
    · have := hb
      have := hm
      exact Functor.isEquivalence_trans _ _
    · rw [BasedFunctor.comp_assoc, hmf]
      exact ⟨β⟩
  · rw [heZg]
    exact ⟨⟨Iso.refl _, fun x ↦
      IsHomLift.id ((discreteModuliMap (yoneda.map g)).w_obj x)⟩⟩

end AlgebraicGeometry
