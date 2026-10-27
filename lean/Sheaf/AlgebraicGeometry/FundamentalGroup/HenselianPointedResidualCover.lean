/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.RingTheory.PairHenselization
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Etale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.PairHenselizationFlatQuotients
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Henselian lift of the pointed universal residual cover

Source: Stacks 0A02, 0AGV, 09XK, 09XI and 09ZS
(blueprint: lem-sfb-henselian-pointed-residual-cover-lift).

The indexing categories and universal covers are the existing small pointed Galois
systems. Quotient diagrams use the actual extended ideals and quotient ring maps.
-/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory Limits Opposite PreGaloisCategory
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.HenselianPointedResidualCover

/-- Reduction on algebras under E, using the actual quotient rings and induced maps.
Source: Stacks 09ZS and the quotient universal property
(blueprint: lem-sfb-henselian-pointed-residual-cover-lift). -/
def quotientDiagramFunctor (E : CommRingCat.{u}) (I : Ideal E) :
    Under E ⥤ CommRingCat.{u} where
  obj A := .of (A.right ⧸ I.map A.hom.hom)
  map {A D} f := CommRingCat.ofHom (Ideal.quotientMap _ f.right.hom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
    have h : f.right.hom.comp A.hom.hom = D.hom.hom := congrArg CommRingCat.Hom.hom f.w
    rw [h]))
  map_id A := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    rfl

/-- The canonical residual isomorphism, from the bijective map supplied by pair henselization.
Source: Stacks 0A02 (blueprint: lem-sfb-henselian-pointed-residual-cover-lift). -/
noncomputable def residualEquiv {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map)) :
    (B ⧸ J) ≃+* (E ⧸ J.map b.hom) :=
  RingEquiv.ofBijective _ h

/-- The closed residual immersion, including the canonical identification E/JE = B/J.
Source: Stacks 0A02 and 09ZS
(blueprint: lem-sfb-henselian-pointed-residual-cover-lift). -/
noncomputable def residualInclusion {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map)) :
    Spec (.of (B ⧸ J)) ⟶ Spec E :=
  Spec.map (CommRingCat.ofHom
    ((residualEquiv J b h).symm.toRingHom.comp (Ideal.Quotient.mk (J.map b.hom))))

/-- The residual structure map for any algebra under E; no algebra structure is chosen.
Source: Stacks 09ZS (blueprint: lem-sfb-henselian-pointed-residual-cover-lift). -/
noncomputable def residualProjection {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map))
    (A : Under E) : Spec ((quotientDiagramFunctor E (J.map b.hom)).obj A) ⟶
      Spec (.of (B ⧸ J)) :=
  Spec.map (CommRingCat.ofHom
    ((Ideal.quotientMap _ A.hom.hom Ideal.le_comap_map).comp
      (residualEquiv J b h).toRingHom))

/-- All comparison data for the lifted system, with their canonical normalizations.
Isomorphisms are tied to coprojections, marked points, and the reduction functor.
Source: Stacks 0A02, 0AGV, 09XK, 09XI and 09ZS
(blueprint: lem-sfb-henselian-pointed-residual-cover-lift). -/
structure LiftData {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    [ConnectedSpace (Spec E)] [ConnectedSpace (Spec (.of (B ⧸ J)))]
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J))) where
  /-- Reduction is an equivalence on finite etale covers, hence on their group actions. -/
  reduction_equivalence : (FiniteEtale.pullback (residualInclusion J b h)).IsEquivalence
  /-- The corresponding equivalence of the small pointed Galois systems. -/
  pointed_equivalence : UniversalCover.Index (s ≫ residualInclusion J b h) ≌
    UniversalCover.Index s
  /-- The underlying finite covers are identified by actual base change. -/
  finite_iso : UniversalCover.obj (s ≫ residualInclusion J b h) ⋙
    FiniteEtale.pullback (residualInclusion J b h) ≅
      pointed_equivalence.functor ⋙ UniversalCover.obj s
  /-- The preceding comparison takes the specified lifted point to the residual point. -/
  finite_point : ∀ j : UniversalCover.Index (s ≫ residualInclusion J b h),
    (FiniteEtale.fiber s).map (finite_iso.hom.app j)
      ((FiniteEtale.pullbackFiberIso (residualInclusion J b h) s).inv.app
        ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j)
        (UniversalCover.point (s ≫ residualInclusion J b h) j)) =
      UniversalCover.point s (pointed_equivalence.functor.obj j)
  /-- Automorphisms, and their group laws, are transported by the reduction functor. -/
  automorphisms : ∀ Y : (Spec E).FiniteEtale,
    Function.Bijective (fun a : Aut Y ↦
      (FiniteEtale.pullback (residualInclusion J b h)).mapIso a)
  /-- Affine coordinate rings of the prescribed pointed system, as E-algebras. -/
  stages : (UniversalCover.Index (s ≫ residualInclusion J b h))ᵒᵖ ⥤ Under E
  /-- These are the covers in the existing universal-cover diagram. -/
  stage_iso : ((stages ⋙ Under.forget E).rightOp ⋙ Scheme.Spec) ≅
    UniversalCover.diagram (s ≫ residualInclusion J b h)
  /-- The affine identifications respect the structure maps to Spec E. -/
  stage_over : ∀ j, Spec.map (stages.obj (op j)).hom =
    stage_iso.hom.app j ≫ UniversalCover.p (s ≫ residualInclusion J b h) j
  /-- Each finite stage is Noetherian. -/
  noetherian : ∀ j, IsNoetherianRing (stages.obj j).right
  /-- Henselianity of the extended marked ideal at each finite stage. -/
  henselian : ∀ j, HenselianRing (stages.obj j).right
    ((J.map b.hom).map (stages.obj j).hom.hom)
  /-- The marked ideals are in the intersections of maximal ideals. -/
  radical : ∀ j, (J.map b.hom).map (stages.obj j).hom.hom ≤ Ideal.jacobson ⊥
  /-- Connectedness includes nonemptiness. -/
  connected : ∀ j, ConnectedSpace (Spec (stages.obj j).right)
  /-- The composite maps from B to the finite stages are ind-etale. -/
  indEtale : ∀ j, RingHom.IndEtaleAcrossUniverses ((stages.obj j).hom.hom.comp b.hom)
  /-- H is the colimit in E-algebras, so its structural map is part of the cocone. -/
  colimit : Cocone stages
  /-- The cocone really computes the colimit. -/
  isColimit : IsColimit colimit
  /-- The integral colimit is henselian; no Noetherian assertion is imposed on H. -/
  henselian_colimit : HenselianRing colimit.pt.right
    ((J.map b.hom).map colimit.pt.hom.hom)
  /-- The colimit marked ideal is in its Jacobson radical. -/
  radical_colimit : (J.map b.hom).map colimit.pt.hom.hom ≤ Ideal.jacobson ⊥
  /-- B to H is ind-etale. -/
  indEtale_colimit : RingHom.IndEtaleAcrossUniverses (colimit.pt.hom.hom.comp b.hom)
  /-- The spectrum of H is the existing pointed universal cover. -/
  universal : Spec colimit.pt.right ≅ UniversalCover.cover (s ≫ residualInclusion J b h)
  /-- This comparison is over Spec E. -/
  universal_over : universal.hom ≫ UniversalCover.proj (s ≫ residualInclusion J b h) =
    Spec.map colimit.pt.hom
  /-- All its projections are the actual colimit coprojections. -/
  universal_stage : ∀ j, universal.hom ≫
    limit.π (UniversalCover.diagram (s ≫ residualInclusion J b h)) j =
      Spec.map (colimit.ι.app (op j)).right ≫ stage_iso.hom.app j
  /-- Quotient rings of finite stages give precisely the residual pointed Galois diagram. -/
  residual_stage_iso :
    ((stages ⋙ quotientDiagramFunctor E (J.map b.hom)).rightOp ⋙ Scheme.Spec) ≅
      pointed_equivalence.functor ⋙ UniversalCover.diagram s
  /-- The residual identifications respect their maps to Spec(B/J). -/
  residual_stage_over : ∀ j, residual_stage_iso.hom.app j ≫
    UniversalCover.p s (pointed_equivalence.functor.obj j) =
      residualProjection J b h (stages.obj (op j))
  /-- The two stage comparisons are induced by the canonical quotient map and base change. -/
  residual_stage_reduction : ∀ j,
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk ((J.map b.hom).map (stages.obj (op j)).hom.hom))) ≫
      stage_iso.hom.app j = residual_stage_iso.hom.app j ≫
        (finite_iso.inv.app j).hom.left ≫
          pullback.fst ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j).obj.hom
            (residualInclusion J b h)
  /-- The actual quotient H/JH is the colimit of the actual quotients C/JC. -/
  quotient_colimit : IsColimit ((quotientDiagramFunctor E (J.map b.hom)).mapCocone colimit)
  /-- The residual spectrum is the existing pointed universal finite-etale limit. -/
  residual_universal : Spec ((quotientDiagramFunctor E (J.map b.hom)).obj colimit.pt) ≅
    UniversalCover.cover s
  /-- The residual comparison is over Spec(B/J). -/
  residual_universal_over : residual_universal.hom ≫ UniversalCover.proj s =
    residualProjection J b h colimit.pt
  /-- The residual comparison has the specified coprojections at every finite stage. -/
  residual_universal_stage : ∀ j, residual_universal.hom ≫
    limit.π (UniversalCover.diagram s) (pointed_equivalence.functor.obj j) =
      Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map (colimit.ι.app (op j))) ≫
        residual_stage_iso.hom.app j
  /-- The marked residual point is the reduction of the marked point upstairs. -/
  residual_point : UniversalCover.pt s ≫ residual_universal.inv ≫
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk ((J.map b.hom).map colimit.pt.hom.hom))) ≫ universal.hom =
        UniversalCover.pt (s ≫ residualInclusion J b h)
  /-- Nonempty connected residual spectrum. -/
  residual_connected : ConnectedSpace
    (Spec ((quotientDiagramFunctor E (J.map b.hom)).obj colimit.pt))
  /-- The residual projection is weakly etale. -/
  residual_weaklyEtale : WeaklyEtale (residualProjection J b h colimit.pt)
  /-- Its singleton is a covering in the specified pro-etale topology. -/
  residual_covering : Presieve.singleton (residualProjection J b h colimit.pt) ∈
    proetalePrecoverage (Spec (.of (B ⧸ J)))

section Basic
private theorem connected_of_quotient (A : Type u) [CommRing A] (I : Ideal A)
    [HenselianRing A I] [ConnectedSpace (Spec (.of (A ⧸ I)))] :
    ConnectedSpace (Spec (.of A)) := by
  have hne : Nonempty (Spec (.of A)) :=
    Nonempty.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) inferInstance
  have : Nontrivial A := (PrimeSpectrum.nonempty_iff_nontrivial).mp hne
  apply PrimeSpectrum.connectedSpace_of_isIdempotentElem
  intro e he
  have hq : Ideal.Quotient.mk I e = 0 ∨ Ideal.Quotient.mk I e = 1 := by
    let q := Ideal.Quotient.mk I
    let θ := (Scheme.ΓSpecIso (.of (A ⧸ I))).inv.hom
    have hθ := (Scheme.connectedSpace_iff_isIdempotentElem (Spec (.of (A ⧸ I))))
    have hh := hθ.mp inferInstance (θ (q e)) ((he.map q).map θ)
    rcases hh with hh | hh
    · exact Or.inl ((ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1 (by simpa using hh))
    · exact Or.inr ((ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1 (by simpa using hh))
  have hinj {x : A} (hx : IsIdempotentElem x) (h : Ideal.Quotient.mk I x = 0) : x = 0 := by
    have hm : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp h
    have hu : IsUnit (1 - x) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _
      (by simpa using (HenselianRing.jac (R := A) (I := I)) (I.neg_mem hm))
    have hz : (1 - x) * x = 0 := by rw [sub_mul, one_mul, hx.eq, sub_self]
    exact (hu.mul_right_eq_zero.mp hz)
  rcases hq with hq | hq
  · exact Or.inl (hinj he hq)
  · right
    have hz := hinj he.one_sub (by simp [hq])
    exact sub_eq_zero.mp hz |>.symm

end Basic

section Hensel
private theorem henselian_given_colimit (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι (fun A : Under (CommRingCat.of B) ↦
      Etale (Spec.map A.hom) ∧ Function.Bijective
        (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map))))
    (hc : IsColimit c) : HenselianRing c.pt.right (J.map c.pt.hom.hom) := by
  obtain ⟨_, _, d, ⟨hd⟩, hH, _⟩ := RingTheory.pair_henselization B J
  let := hH
  let e := (Under.forget (CommRingCat.of B)).mapIso (hd.coconePointUniqueUpToIso hc)
  let : Algebra d.pt.right c.pt.right := e.hom.hom.toAlgebra
  have : Algebra.IsIntegral d.pt.right c.pt.right :=
    ⟨fun x ↦ by
      obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 x
      exact isIntegral_algebraMap⟩
  have h := henselianRing_of_isIntegral d.pt.right (J.map d.pt.hom.hom) c.pt.right
  have he : e.hom.hom.comp d.pt.hom.hom = c.pt.hom.hom :=
    congrArg CommRingCat.Hom.hom (Under.w (hd.coconePointUniqueUpToIso hc).hom)
  change HenselianRing c.pt.right ((J.map d.pt.hom.hom).map e.hom.hom) at h
  simpa only [Ideal.map_map, he] using h

private theorem indEtale_ulift {A D : Type u} [CommRing A] [CommRing D]
    (f : A →+* D) (hf : f.IndEtale) : f.IndEtaleAcrossUniverses := by
  rw [RingHom.IndEtaleAcrossUniverses, RingHom.IndEtale.iff_ind_etale]
  rw [RingHom.ulift, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
  have hind := RingHom.IndEtale.iff_ind_etale f |>.mp hf
  exact (MorphismProperty.ind CommRingCat.etale).comp_mem _ _
    ((MorphismProperty.ind CommRingCat.etale).comp_mem _ _
      (MorphismProperty.le_ind _ _ (by
        exact (RingHom.Etale.of_bijective (ULift.ringEquiv (R := A)).bijective))) hind)
    (MorphismProperty.le_ind _ _ (by
      exact RingHom.Etale.of_bijective (ULift.ringEquiv (R := D)).symm.bijective))

private theorem henselization_indEtale (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι (fun A : Under (CommRingCat.of B) ↦
      Etale (Spec.map A.hom) ∧ Function.Bijective
        (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map))))
    (hc : IsColimit c) : c.pt.hom.hom.IndEtale := by
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun A ↦
    Etale (Spec.map A.hom) ∧ Function.Bijective
      (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map)
  let : EssentiallySmall.{u} P.FullSubcategory := (RingTheory.pair_henselization B J).1
  let : IsFiltered P.FullSubcategory := (RingTheory.pair_henselization B J).2.1
  rw [RingHom.IndEtale.iff_ind_etale, MorphismProperty.ind_iff_ind_underMk]
  change ObjectProperty.ind.{u} CommRingCat.etale.underObj c.pt
  apply ObjectProperty.of_essentiallySmall_index
    (pres := { diag := P.ι, ι := c.ι, isColimit := hc })
  intro j
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp j.property.1

end Hensel

section Pointed
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [GaloisCategory C] [GaloisCategory D]

private theorem connected_map (e : C ≌ D) (X : C) [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsConnected (e.functor.obj X) := by
  constructor
  · intro h
    exact PreGaloisCategory.IsConnected.notInitial
      (h.isInitialOfObj e.functor X)
  · intro Y i hi hn
    let Y' := e.inverse.obj Y
    let i' : Y' ⟶ X := e.inverse.map i ≫ e.unitIso.inv.app X
    have : Mono i' := by dsimp [i']; infer_instance
    have hY' : IsInitial Y' → False := by
      intro h
      apply hn
      exact (h.isInitialObj e.functor Y').ofIso (e.counitIso.app Y)
    have : IsIso i' := PreGaloisCategory.IsConnected.noTrivialComponent _ i' hY'
    have : IsIso (e.functor.map i') := inferInstance
    have heq : e.functor.map i' = (e.counitIso.hom.app Y) ≫ i := by
      dsimp [i']
      rw [e.functor.map_comp, ← e.counit_app_functor]
      exact e.counitIso.hom.naturality i
    rw [heq] at this
    exact IsIso.of_isIso_comp_left (e.counitIso.hom.app Y) i

variable (F : C ⥤ FintypeCat.{u}) (G : D ⥤ FintypeCat.{u})
    [FiberFunctor F] [FiberFunctor G]

private theorem galois_map (e : C ≌ D) (α : e.functor ⋙ G ≅ F)
    (X : C) [IsGalois X] : IsGalois (e.functor.obj X) := by
  have : PreGaloisCategory.IsConnected (e.functor.obj X) := connected_map e X
  apply (isGalois_iff_pretransitive G _).mpr
  constructor
  intro a b
  obtain ⟨σ, hσ⟩ := evaluation_aut_surjective_of_isGalois F X (α.hom.app X a)
    (α.hom.app X b)
  refine ⟨e.functor.mapIso σ, ?_⟩
  change G.map (e.functor.map σ.hom) a = b
  apply (ConcreteCategory.bijective_of_isIso (α.hom.app X)).1
  have hnat := ConcreteCategory.congr_hom (α.hom.naturality σ.hom) a
  exact hnat.trans hσ

private noncomputable def pointedFunctor (e : C ≌ D) (α : e.functor ⋙ G ≅ F) :
    PointedGaloisObject F ⥤ PointedGaloisObject G where
  obj X := ⟨e.functor.obj X.obj, α.inv.app X.obj X.pt, galois_map F G e α X.obj⟩
  map {X Y} f := ⟨e.functor.map f.val, by
    have hnat := ConcreteCategory.congr_hom (α.inv.naturality f.val) X.pt
    change G.map (e.functor.map f.val) (α.inv.app X.obj X.pt) = _
    exact hnat.symm.trans (congrArg (α.inv.app Y.obj) f.comp)⟩
  map_id X := by apply PointedGaloisObject.hom_ext; exact e.functor.map_id _
  map_comp f g := by apply PointedGaloisObject.hom_ext; exact e.functor.map_comp _ _

private noncomputable def pointedEquiv (e : C ≌ D) (α : e.functor ⋙ G ≅ F) :
    PointedGaloisObject F ≌ PointedGaloisObject G := by
  let P := pointedFunctor F G e α
  have : P.Faithful := ⟨by
    intro X Y f g h
    apply PointedGaloisObject.hom_ext
    exact e.functor.map_injective (congrArg (fun k ↦ k.val) h)⟩
  have : P.Full := ⟨fun {X Y} f ↦ by
    let g := e.functor.preimage f.val
    refine ⟨⟨g, ?_⟩, ?_⟩
    · apply (ConcreteCategory.bijective_of_isIso (α.inv.app Y.obj)).1
      have hnat := ConcreteCategory.congr_hom (α.inv.naturality g) X.pt
      have hf := f.comp
      change G.map f.val (α.inv.app X.obj X.pt) = α.inv.app Y.obj Y.pt at hf
      dsimp only [Functor.comp_map, g] at hnat
      simp only [Functor.map_preimage] at hnat
      exact hnat.trans hf
    · apply PointedGaloisObject.hom_ext
      exact e.functor.map_preimage _⟩
  let β : e.inverse ⋙ F ≅ G :=
    (Functor.isoWhiskerLeft e.inverse α).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso G ≪≫ G.leftUnitor
  have : P.EssSurj := ⟨fun Y ↦ by
    let X := (pointedFunctor G F e.symm β).obj Y
    let a := e.counitIso.app Y.obj
    refine ⟨X, ⟨?_⟩⟩
    refine { hom := ⟨a.hom, ?_⟩
             inv := ⟨a.inv, ?_⟩
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · change G.map a.hom (α.inv.app _ (β.inv.app _ Y.pt)) = Y.pt
      have hα (z : F.obj (e.inverse.obj Y.obj)) :=
        ConcreteCategory.congr_hom (α.inv_hom_id_app (e.inverse.obj Y.obj)) z
      have hα' (z : G.obj (e.functor.obj (e.inverse.obj Y.obj))) :=
        ConcreteCategory.congr_hom (α.hom_inv_id_app (e.inverse.obj Y.obj)) z
      simp only [FintypeCat.comp_apply, FintypeCat.id_apply] at hα hα'
      dsimp [β, a]
      exact (congrArg (fun z ↦ G.map a.hom z)
        (hα' (G.map a.inv Y.pt))).trans
          (ConcreteCategory.congr_hom (G.mapIso a).inv_hom_id Y.pt)
    · change G.map a.inv Y.pt = α.inv.app _ (β.inv.app _ Y.pt)
      dsimp [β, a]
      exact (ConcreteCategory.congr_hom (α.hom_inv_id_app (e.inverse.obj Y.obj))
        (G.map a.inv Y.pt)).symm
    · apply PointedGaloisObject.hom_ext; exact a.hom_inv_id
    · apply PointedGaloisObject.hom_ext; exact a.inv_hom_id⟩
  have : P.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact P.asEquivalence

end Pointed

section SmallPointed
variable {E : CommRingCat.{u}} [ConnectedSpace (Spec E)]
    {R : CommRingCat.{u}} [ConnectedSpace (Spec R)] (i : Spec R ⟶ Spec E)
    [h : (FiniteEtale.pullback i).IsEquivalence]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec R)
attribute [local instance] FiniteEtale.fiberFunctor
private noncomputable def smallPointedEquiv :
    UniversalCover.Index (s ≫ i) ≌ UniversalCover.Index s :=
  (UniversalCover.indexEquiv (s ≫ i)).symm.trans
    ((pointedEquiv (FiniteEtale.fiber (s ≫ i)) (FiniteEtale.fiber s)
      (FiniteEtale.pullback i).asEquivalence (FiniteEtale.pullbackFiberIso i s)).trans
        (UniversalCover.indexEquiv s))

private noncomputable def smallFiniteIso :
    UniversalCover.obj (s ≫ i) ⋙ FiniteEtale.pullback i ≅
      (smallPointedEquiv i s).functor ⋙ UniversalCover.obj s :=
  NatIso.ofComponents (fun j ↦ (PointedGaloisObject.incl (FiniteEtale.fiber s)).mapIso
    ((UniversalCover.indexEquiv s).unitIso.app
      ((pointedEquiv (FiniteEtale.fiber (s ≫ i)) (FiniteEtale.fiber s)
        (FiniteEtale.pullback i).asEquivalence (FiniteEtale.pullbackFiberIso i s)).functor.obj
          ((UniversalCover.indexEquiv (s ≫ i)).inverse.obj j)))) (by
    intro j k f
    exact congrArg (fun g ↦ g.val) ((UniversalCover.indexEquiv s).unitIso.hom.naturality
      ((pointedFunctor (FiniteEtale.fiber (s ≫ i)) (FiniteEtale.fiber s)
        (FiniteEtale.pullback i).asEquivalence (FiniteEtale.pullbackFiberIso i s)).map
          ((UniversalCover.indexEquiv (s ≫ i)).inverse.map f))))

private theorem smallFinitePoint (j : UniversalCover.Index (s ≫ i)) :
    (FiniteEtale.fiber s).map ((smallFiniteIso i s).hom.app j)
      ((FiniteEtale.pullbackFiberIso i s).inv.app ((UniversalCover.obj (s ≫ i)).obj j)
        (UniversalCover.point (s ≫ i) j)) =
      UniversalCover.point s ((smallPointedEquiv i s).functor.obj j) := by
  exact ((UniversalCover.indexEquiv s).unitIso.hom.app _).comp

end SmallPointed

attribute [local irreducible] smallPointedEquiv smallFiniteIso

section Quotient
private noncomputable def quotientColimit {K : Type v} [Category K] [CategoryTheory.IsConnected K]
    {E : CommRingCat.{u}} (I : Ideal E) (D : K ⥤ Under E)
    (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((quotientDiagramFunctor E I).mapCocone c) := by
  classical
  let Q := quotientDiagramFunctor E I
  let liftCocone (s : Cocone (D ⋙ Q)) : Cocone (D ⋙ Under.forget E) :=
    { pt := s.pt
      ι :=
        { app := fun j ↦ CommRingCat.ofHom
            ((s.ι.app j).hom.comp (Ideal.Quotient.mk (I.map (D.obj j).hom.hom)))
          naturality := by
            intro i j f
            apply CommRingCat.hom_ext
            ext x
            exact ConcreteCategory.congr_hom (s.ι.naturality f)
              (Ideal.Quotient.mk (I.map (D.obj i).hom.hom) x) } }
  let h := isColimitOfPreserves (Under.forget E) hc
  let d (s : Cocone (D ⋙ Q)) := h.desc (liftCocone s)
  have kills (s : Cocone (D ⋙ Q)) : I.map c.pt.hom.hom ≤ RingHom.ker (d s).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨j⟩ := (inferInstance : Nonempty K)
    have hj := ConcreteCategory.congr_hom (h.fac (liftCocone s) j) ((D.obj j).hom.hom a)
    have hw : (c.ι.app j).right.hom.comp (D.obj j).hom.hom = c.pt.hom.hom :=
      congrArg CommRingCat.Hom.hom (Under.w (c.ι.app j))
    change (d s).hom (c.pt.hom.hom a) = 0
    rw [← hw]
    change (d s).hom ((c.ι.app j).right.hom ((D.obj j).hom.hom a)) = 0
    change (d s).hom ((c.ι.app j).right.hom ((D.obj j).hom.hom a)) =
      (s.ι.app j).hom (Ideal.Quotient.mk _ ((D.obj j).hom.hom a)) at hj
    rw [hj]
    change (s.ι.app j).hom
      (Ideal.Quotient.mk (I.map (D.obj j).hom.hom) ((D.obj j).hom.hom a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha), map_zero]
  refine { desc := fun s ↦ CommRingCat.ofHom (Ideal.Quotient.lift _ (d s).hom (kills s))
           fac := ?_, uniq := ?_ }
  · intro s j
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom (h.fac (liftCocone s) j)
  · intro s m hm
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    change m.hom.comp (Ideal.Quotient.mk (I.map c.pt.hom.hom)) = (d s).hom
    apply CommRingCat.hom_ext_iff.mp
    apply h.hom_ext
    intro j
    apply CommRingCat.hom_ext
    ext x
    have hh := ConcreteCategory.congr_hom (hm j)
      (Ideal.Quotient.mk (I.map (D.obj j).hom.hom) x)
    have hd := ConcreteCategory.congr_hom (h.fac (liftCocone s) j) x
    exact hh.trans hd.symm

end Quotient

section Geometry
variable {E : CommRingCat.{u}} [ConnectedSpace (Spec E)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec E)

private theorem stageAffine (j : UniversalCover.Index t) :
    IsAffine ((UniversalCover.diagram t).obj j) :=
  isAffine_of_isAffineHom (UniversalCover.p t j)

attribute [local instance] stageAffine

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def stageRings : (UniversalCover.Index t)ᵒᵖ ⥤ Under E where
  obj j := Under.mk ((Scheme.ΓSpecIso E).inv ≫ (UniversalCover.p t j.unop).appTop)
  map {i j} f := Under.homMk ((UniversalCover.diagram t).map f.unop).appTop (by
    change ((Scheme.ΓSpecIso E).inv ≫ _) ≫ _ = _
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, UniversalCover.map_p]
    rfl)
  map_id j := by
    apply Under.UnderMorphism.ext
    change ((UniversalCover.diagram t).map (𝟙 j.unop)).appTop = _
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    apply Under.UnderMorphism.ext
    change ((UniversalCover.diagram t).map (g.unop ≫ f.unop)).appTop =
      ((UniversalCover.diagram t).map f.unop).appTop ≫
        ((UniversalCover.diagram t).map g.unop).appTop
    rw [CategoryTheory.Functor.map_comp]
    exact Scheme.Hom.comp_appTop _ _

private noncomputable def stageIso :
    ((stageRings t ⋙ Under.forget E).rightOp ⋙ Scheme.Spec) ≅ UniversalCover.diagram t :=
  NatIso.ofComponents (fun j ↦ ((UniversalCover.diagram t).obj j).isoSpec.symm)
    (fun _ ↦ Scheme.isoSpec_inv_naturality _)

private theorem stageOver (j : UniversalCover.Index t) :
    Spec.map ((stageRings t).obj (op j)).hom =
      (stageIso t).hom.app j ≫ UniversalCover.p t j := by
  dsimp [stageRings, stageIso]
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact Scheme.isoSpec_inv_naturality _

private noncomputable def stageColimit : Cocone (stageRings t) where
  pt := Under.mk ((Scheme.ΓSpecIso E).inv ≫ (UniversalCover.proj t).appTop)
  ι :=
    { app := fun j ↦ Under.homMk (limit.π (UniversalCover.diagram t) j.unop).appTop (by
        change ((Scheme.ΓSpecIso E).inv ≫ _) ≫ _ = _
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, UniversalCover.π_p]
        rfl)
      naturality := by
        intro i j f
        apply Under.UnderMorphism.ext
        change ((UniversalCover.diagram t).map f.unop).appTop ≫
          (limit.π (UniversalCover.diagram t) j.unop).appTop = _ ≫ 𝟙 _
        rw [Category.comp_id, ← Scheme.Hom.comp_appTop, limit.w]
        rfl }

private noncomputable def stageIsColimit : IsColimit (stageColimit t) := by
  apply isColimitOfReflects (Under.forget E)
  have (j : (UniversalCover.Index t)ᵒᵖ) :
      IsAffine ((UniversalCover.diagram t).op.obj j).unop := stageAffine t j.unop
  exact isColimitOfPreserves Scheme.Γ (limit.isLimit (UniversalCover.diagram t)).op

private theorem stageSpecFinite (j : (UniversalCover.Index t)ᵒᵖ) :
    (((stageRings t).obj j).hom.hom).Finite := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mp
  rw [stageOver]
  infer_instance

private theorem stageSpecEtale (j : (UniversalCover.Index t)ᵒᵖ) :
    (((stageRings t).obj j).hom.hom).Etale := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
  rw [stageOver]
  infer_instance

private theorem stageConnected (j : (UniversalCover.Index t)ᵒᵖ) :
    ConnectedSpace (Spec ((stageRings t).obj j).right) := by
  have : ConnectedSpace ((UniversalCover.diagram t).obj j.unop) :=
    FiniteEtale.connectedSpace_of_isConnected _
  exact ((stageIso t).app j.unop).hom.homeomorph.connectedSpace_iff.mpr inferInstance

private theorem coverAffine : IsAffine (UniversalCover.cover t) :=
  isAffine_of_isAffineHom (UniversalCover.proj t)

attribute [local instance] coverAffine

private noncomputable def stageUniversal :
    Spec (stageColimit t).pt.right ≅ UniversalCover.cover t :=
  (UniversalCover.cover t).isoSpec.symm

private theorem stageUniversalOver :
    (stageUniversal t).hom ≫ UniversalCover.proj t = Spec.map (stageColimit t).pt.hom := by
  dsimp [stageUniversal, stageColimit]
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact (Scheme.isoSpec_inv_naturality _).symm

private theorem stageUniversalStage (j : UniversalCover.Index t) :
    (stageUniversal t).hom ≫ limit.π (UniversalCover.diagram t) j =
      Spec.map ((stageColimit t).ι.app (op j)).right ≫ (stageIso t).hom.app j := by
  exact (Scheme.isoSpec_inv_naturality _).symm

private theorem stageNoetherian [IsNoetherianRing E] (j : (UniversalCover.Index t)ᵒᵖ) :
    IsNoetherianRing ((stageRings t).obj j).right := by
  let f := ((stageRings t).obj j).hom.hom
  let : Algebra E ((stageRings t).obj j).right := f.toAlgebra
  have : Module.Finite E ((stageRings t).obj j).right := stageSpecFinite t j
  exact IsNoetherianRing.of_finite E _

private theorem stageHenselian (I : Ideal E) [HenselianRing E I]
    (j : (UniversalCover.Index t)ᵒᵖ) :
    HenselianRing ((stageRings t).obj j).right (I.map ((stageRings t).obj j).hom.hom) := by
  let f := ((stageRings t).obj j).hom.hom
  let : Algebra E ((stageRings t).obj j).right := f.toAlgebra
  have : Algebra.IsIntegral E ((stageRings t).obj j).right :=
    ⟨(stageSpecFinite t j).to_isIntegral⟩
  exact henselianRing_of_isIntegral E I _

private theorem stageColimitIntegral : (stageColimit t).pt.hom.hom.IsIntegral := by
  let D := stageRings t ⋙ Under.forget E
  have hc := isColimitOfPreserves (Under.forget E) (stageIsColimit t)
  intro x
  obtain ⟨j, a, ha⟩ := Concrete.isColimit_exists_rep D hc x
  have hi := ((stageSpecFinite t j).to_isIntegral a).map
    ((stageColimit t).ι.app j).right.hom
  rw [show ((stageColimit t).ι.app j).right.hom.comp
      ((stageRings t).obj j).hom.hom = (stageColimit t).pt.hom.hom from
    congrArg CommRingCat.Hom.hom (Under.w ((stageColimit t).ι.app j))] at hi
  exact ha ▸ hi

private theorem colimitHenselian (I : Ideal E) [HenselianRing E I] :
    HenselianRing (stageColimit t).pt.right (I.map (stageColimit t).pt.hom.hom) := by
  let : Algebra E (stageColimit t).pt.right := (stageColimit t).pt.hom.hom.toAlgebra
  have : Algebra.IsIntegral E (stageColimit t).pt.right := ⟨stageColimitIntegral t⟩
  exact henselianRing_of_isIntegral E I _

private theorem stageColimitEtale : (stageColimit t).pt.hom.hom.IndEtale := by
  rw [RingHom.IndEtale.iff_ind_etale, MorphismProperty.ind_iff_ind_underMk]
  change ObjectProperty.ind.{u} CommRingCat.etale.underObj (stageColimit t).pt
  apply ObjectProperty.of_essentiallySmall_index
    (pres :=
      { diag := stageRings t, ι := (stageColimit t).ι, isColimit := stageIsColimit t })
  exact stageSpecEtale t

end Geometry

section Reduction

set_option backward.isDefEq.respectTransparency false
variable {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map))

private theorem residual_square :
    IsPullback (residualInclusion J b h)
      (Spec.map (CommRingCat.ofHom (residualEquiv J b h).symm.toRingHom))
      (𝟙 (Spec E))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map b.hom)))) := by
  apply IsPullback.of_vert_isIso
  constructor
  simp [residualInclusion, Spec.map_comp]

private theorem reduction_equivalence [HenselianRing E (J.map b.hom)] :
    (FiniteEtale.pullback (residualInclusion J b h)).IsEquivalence := by
  let i := residualInclusion J b h
  let T (X : Scheme.{u}) : X.FiniteEtale ⥤
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ X :=
    { obj := fun P ↦ MorphismProperty.Over.mk ⊤ P.obj.hom ⟨P.property, P.obj.prop⟩
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left (FiniteEtale.hom_left_comp f) }
  have hT (X : Scheme.{u}) : (T X).IsEquivalence := by
    have : (T X).Faithful := ⟨fun h ↦ FiniteEtale.hom_ext
      (congrArg (fun f ↦ f.left) h)⟩
    have : (T X).Full := ⟨fun f ↦ ⟨ObjectProperty.homMk
      (MorphismProperty.Over.homMk f.left f.w), rfl⟩⟩
    have : (T X).EssSurj := ⟨fun P ↦
      ⟨⟨MorphismProperty.Over.mk ⊤ P.hom P.prop.2, P.prop.1⟩, ⟨Iso.refl _⟩⟩⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hp : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence :=
    Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing
      (J.map b.hom) (𝟙 (Spec E)) i
      (Spec.map (CommRingCat.ofHom (residualEquiv J b h).symm.toRingHom))
      (residual_square J b h)
  have := hT (Spec E)
  have := hT (Spec (.of (B ⧸ J)))
  let α : FiniteEtale.pullback i ⋙ T (Spec (.of (B ⧸ J))) ≅
      T (Spec E) ⋙ MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext
      · change pullback.map P.obj.hom i Q.obj.hom i f.hom.left (𝟙 _) (𝟙 _)
          ((Category.comp_id _).trans (FiniteEtale.hom_left_comp f).symm)
          (by simp) ≫
          pullback.fst Q.obj.hom i =
          pullback.lift (pullback.fst P.obj.hom i ≫ f.hom.left)
            (pullback.snd P.obj.hom i) _ ≫ pullback.fst Q.obj.hom i
        simp only [pullback.map, pullback.lift_fst]
      · change pullback.map P.obj.hom i Q.obj.hom i f.hom.left (𝟙 _) (𝟙 _)
          ((Category.comp_id _).trans (FiniteEtale.hom_left_comp f).symm)
          (by simp) ≫
          pullback.snd Q.obj.hom i =
          pullback.lift (pullback.fst P.obj.hom i ≫ f.hom.left)
            (pullback.snd P.obj.hom i) _ ≫ pullback.snd Q.obj.hom i
        simp only [pullback.map, pullback.lift_snd, Category.comp_id])
  have : (FiniteEtale.pullback i ⋙ T (Spec (.of (B ⧸ J)))).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso α).mpr inferInstance
  exact Functor.isEquivalence_of_comp_right (FiniteEtale.pullback i)
    (T (Spec (.of (B ⧸ J))))

private theorem quotientNaturality {A D : Under E} (f : A ⟶ D) :
    Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map f) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J.map b.hom).map A.hom.hom))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J.map b.hom).map D.hom.hom))) ≫
      Spec.map f.right := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

private theorem residualProjectionNaturality {A D : Under E} (f : A ⟶ D) :
    Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map f) ≫
      residualProjection J b h A = residualProjection J b h D := by
  dsimp only [residualProjection]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change ((quotientDiagramFunctor E (J.map b.hom)).map f).hom
      (Ideal.quotientMap _ A.hom.hom Ideal.le_comap_map ((residualEquiv J b h) x)) =
      Ideal.quotientMap _ D.hom.hom Ideal.le_comap_map ((residualEquiv J b h) x)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((residualEquiv J b h) x)
  rw [← ha]
  change Ideal.Quotient.mk ((J.map b.hom).map D.hom.hom)
    (f.right.hom (A.hom.hom a)) =
      Ideal.Quotient.mk ((J.map b.hom).map D.hom.hom) (D.hom.hom a)
  exact congrArg (Ideal.Quotient.mk ((J.map b.hom).map D.hom.hom))
    (ConcreteCategory.congr_hom f.w a)

private theorem residualStageSquare (A : Under E) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J.map b.hom).map A.hom.hom))))
      (residualProjection J b h A) (Spec.map A.hom) (residualInclusion J b h) := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (J.map b.hom))
  let e := (residualEquiv J b h).symm.toCommRingCatIso
  have hp := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_quotient A.hom (J.map b.hom))).flip
  have hi : IsPullback (Spec.map q) (Spec.map e.inv) (𝟙 (Spec E))
      (residualInclusion J b h) := by
    apply IsPullback.of_vert_isIso
    refine ⟨?_⟩
    change Spec.map q ≫ 𝟙 (Spec E) = Spec.map e.inv ≫ residualInclusion J b h
    erw [Category.comp_id]
    dsimp [residualInclusion]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x
    exact ((residualEquiv J b h).apply_symm_apply _).symm
  have hh := hp.paste_vert hi
  have he : Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap _ A.hom.hom Ideal.le_comap_map)) ≫ Spec.map e.inv =
        residualProjection J b h A := by
    rw [← Spec.map_comp]
    rfl
  rw [he] at hh
  erw [Category.comp_id] at hh
  exact hh

end Reduction

section ResidualGeometry
variable {B : Type u} [CommRing B] (J : Ideal B)
    {E : CommRingCat.{u}} (b : CommRingCat.of B ⟶ E)
    [ConnectedSpace (Spec E)] [ConnectedSpace (Spec (.of (B ⧸ J)))]
    (h : Function.Bijective (Ideal.quotientMap (J.map b.hom) b.hom Ideal.le_comap_map))
    [(FiniteEtale.pullback (residualInclusion J b h)).IsEquivalence]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J)))

omit [ConnectedSpace (Spec (.of (B ⧸ J)))]
  [(FiniteEtale.pullback (residualInclusion J b h)).IsEquivalence] in
private theorem residualStagePullback
    (j : UniversalCover.Index (s ≫ residualInclusion J b h)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((J.map b.hom).map ((stageRings (s ≫ residualInclusion J b h)).obj (op j)).hom.hom))) ≫
        (stageIso (s ≫ residualInclusion J b h)).hom.app j)
      (residualProjection J b h ((stageRings (s ≫ residualInclusion J b h)).obj (op j)))
      (UniversalCover.p (s ≫ residualInclusion J b h) j) (residualInclusion J b h) := by
  apply (residualStageSquare J b h
    ((stageRings (s ≫ residualInclusion J b h)).obj (op j))).of_iso (Iso.refl _)
    ((stageIso (s ≫ residualInclusion J b h)).app j) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simpa using stageOver (s ≫ residualInclusion J b h) j
  · simp

private theorem pullbackIsoNaturality {C : Type*} [Category C]
    {X₁ X₂ T S Q₁ Q₂ : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {g : T ⟶ S}
    {a₁ : Q₁ ⟶ X₁} {a₂ : Q₂ ⟶ X₂} {b₁ : Q₁ ⟶ T} {b₂ : Q₂ ⟶ T}
    (h₁ : IsPullback a₁ b₁ f₁ g) (h₂ : IsPullback a₂ b₂ f₂ g)
    [HasPullback f₁ g] [HasPullback f₂ g]
    (x : X₁ ⟶ X₂) (y : Q₁ ⟶ Q₂) (w : f₁ ≫ 𝟙 S = x ≫ f₂)
    (ha : y ≫ a₂ = a₁ ≫ x) (hb : y ≫ b₂ = b₁) :
    y ≫ h₂.isoPullback.hom = h₁.isoPullback.hom ≫
      pullback.map f₁ g f₂ g x (𝟙 T) (𝟙 S) w (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.map,
      pullback.lift_fst]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact ha
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.map,
      pullback.lift_snd, Category.comp_id]
    exact hb

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def residualStageIso :
    ((stageRings (s ≫ residualInclusion J b h) ⋙
      quotientDiagramFunctor E (J.map b.hom)).rightOp ⋙ Scheme.Spec) ≅
      (smallPointedEquiv (residualInclusion J b h) s).functor ⋙ UniversalCover.diagram s :=
  NatIso.ofComponents (fun j ↦
    (residualStagePullback J b h s j).isoPullback ≪≫
      asIso ((smallFiniteIso (residualInclusion J b h) s).hom.app j).hom.left) (by
    intro j k f
    let t := s ≫ residualInclusion J b h
    let a := smallFiniteIso (residualInclusion J b h) s
    have ha := congrArg (fun g ↦ g.hom.left) (a.hom.naturality f)
    change ((FiniteEtale.pullback (residualInclusion J b h)).map
      ((UniversalCover.obj t).map f)).hom.left ≫ (a.hom.app k).hom.left =
        (a.hom.app j).hom.left ≫
          (UniversalCover.diagram s).map ((smallPointedEquiv _ s).functor.map f) at ha
    change Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map
      ((stageRings t).map f.op)) ≫
        ((residualStagePullback J b h s k).isoPullback.hom ≫ (a.hom.app k).hom.left) =
      ((residualStagePullback J b h s j).isoPullback.hom ≫ (a.hom.app j).hom.left) ≫ _
    have hn : Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map
        ((stageRings t).map f.op)) ≫ (residualStagePullback J b h s k).isoPullback.hom =
        (residualStagePullback J b h s j).isoPullback.hom ≫
          ((FiniteEtale.pullback (residualInclusion J b h)).map
            ((UniversalCover.obj t).map f)).hom.left := by
      apply pullbackIsoNaturality
        (residualStagePullback J b h s j) (residualStagePullback J b h s k)
        ((UniversalCover.diagram t).map f)
        (Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map
          ((stageRings t).map f.op)))
        ((Category.comp_id _).trans (UniversalCover.map_p t f).symm)
      · rw [← Category.assoc, quotientNaturality, Category.assoc]
        exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((J.map b.hom).map ((stageRings t).obj (op j)).hom.hom))) ≫ g)
            ((stageIso t).hom.naturality f)
      · exact residualProjectionNaturality J b h ((stageRings t).map f.op)
    change _ = (_ ≫ (a.hom.app j).hom.left) ≫
      (UniversalCover.diagram s).map ((smallPointedEquiv _ s).functor.map f)
    rw [← Category.assoc, hn, Category.assoc, ha, ← Category.assoc])

private theorem residualStageOver (j : UniversalCover.Index (s ≫ residualInclusion J b h)) :
    (residualStageIso J b h s).hom.app j ≫
      UniversalCover.p s ((smallPointedEquiv (residualInclusion J b h) s).functor.obj j) =
        residualProjection J b h ((stageRings (s ≫ residualInclusion J b h)).obj (op j)) := by
  dsimp only [residualStageIso, NatIso.ofComponents, Iso.trans_hom, asIso_hom]
  have hw := FiniteEtale.hom_left_comp
    ((smallFiniteIso (residualInclusion J b h) s).hom.app j)
  change ((smallFiniteIso (residualInclusion J b h) s).hom.app j).hom.left ≫
    UniversalCover.p s ((smallPointedEquiv (residualInclusion J b h) s).functor.obj j) =
      pullback.snd ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j).obj.hom
        (residualInclusion J b h) at hw
  change _ ≫ ((smallFiniteIso (residualInclusion J b h) s).hom.app j).hom.left ≫
    ((UniversalCover.obj s).obj
      ((smallPointedEquiv (residualInclusion J b h) s).functor.obj j)).obj.hom = _
  erw [hw]
  exact (residualStagePullback J b h s j).isoPullback_hom_snd

set_option backward.isDefEq.respectTransparency.types false in
private theorem residualStageReduction
    (j : UniversalCover.Index (s ≫ residualInclusion J b h)) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((J.map b.hom).map ((stageRings (s ≫ residualInclusion J b h)).obj (op j)).hom.hom))) ≫
      (stageIso (s ≫ residualInclusion J b h)).hom.app j =
    (residualStageIso J b h s).hom.app j ≫
      ((smallFiniteIso (residualInclusion J b h) s).inv.app j).hom.left ≫
        pullback.fst ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j).obj.hom
          (residualInclusion J b h) := by
  dsimp only [residualStageIso, NatIso.ofComponents, Iso.trans_hom, asIso_hom]
  have hh := congrArg (fun f ↦ f.hom.left)
    ((smallFiniteIso (residualInclusion J b h) s).hom_inv_id_app j)
  change _ ≫ _ = 𝟙 _ at hh
  simp only [Category.assoc]
  rw [← Category.assoc
    (((smallFiniteIso (residualInclusion J b h) s).hom.app j).hom.left)
    (((smallFiniteIso (residualInclusion J b h) s).inv.app j).hom.left)
    (pullback.fst ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j).obj.hom
      (residualInclusion J b h)), hh, Category.id_comp]
  exact (residualStagePullback J b h s j).isoPullback_hom_fst.symm

private noncomputable def residualCone : Cone
    ((smallPointedEquiv (residualInclusion J b h) s).functor ⋙ UniversalCover.diagram s) :=
  (Cone.postcompose (residualStageIso J b h s).hom).obj
    (Scheme.Spec.mapCone (coneRightOpOfCocone
      ((quotientDiagramFunctor E (J.map b.hom)).mapCocone
        (stageColimit (s ≫ residualInclusion J b h)))))

private noncomputable def residualConeIsLimit : IsLimit (residualCone J b h s) := by
  let : CategoryTheory.IsConnected (UniversalCover.Index
      (s ≫ residualInclusion J b h))ᵒᵖ := IsFiltered.isConnected _
  apply (IsLimit.postcomposeHomEquiv (residualStageIso J b h s) _).symm.toFun
  apply isLimitOfPreserves Scheme.Spec
  apply isLimitConeRightOpOfCocone
  exact quotientColimit (J.map b.hom) _ _ (stageIsColimit (s ≫ residualInclusion J b h))

private noncomputable def residualUniversal :
    Spec ((quotientDiagramFunctor E (J.map b.hom)).obj
      (stageColimit (s ≫ residualInclusion J b h)).pt) ≅ UniversalCover.cover s :=
  (residualConeIsLimit J b h s).conePointUniqueUpToIso
    ((limit.isLimit (UniversalCover.diagram s)).whiskerEquivalence
      (smallPointedEquiv (residualInclusion J b h) s))

private theorem residualUniversalStage
    (j : UniversalCover.Index (s ≫ residualInclusion J b h)) :
    (residualUniversal J b h s).hom ≫
      limit.π (UniversalCover.diagram s)
        ((smallPointedEquiv (residualInclusion J b h) s).functor.obj j) =
    Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map
      ((stageColimit (s ≫ residualInclusion J b h)).ι.app (op j))) ≫
        (residualStageIso J b h s).hom.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

private theorem residualUniversalOver :
    (residualUniversal J b h s).hom ≫ UniversalCover.proj s =
      residualProjection J b h (stageColimit (s ≫ residualInclusion J b h)).pt := by
  classical
  let j : UniversalCover.Index (s ≫ residualInclusion J b h) := UniversalCover.j₀ _
  rw [← UniversalCover.π_p s ((smallPointedEquiv _ s).functor.obj j),
    ← Category.assoc, residualUniversalStage, Category.assoc, residualStageOver]
  exact residualProjectionNaturality J b h _

set_option backward.isDefEq.respectTransparency.types false in
private theorem residualPoint :
    UniversalCover.pt s ≫ (residualUniversal J b h s).inv ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((J.map b.hom).map (stageColimit (s ≫ residualInclusion J b h)).pt.hom.hom))) ≫
      (stageUniversal (s ≫ residualInclusion J b h)).hom =
        UniversalCover.pt (s ≫ residualInclusion J b h) := by
  apply limit.hom_ext
  intro j
  rw [Category.assoc, Category.assoc, Category.assoc, stageUniversalStage,
    ← Category.assoc (Spec.map _), ← quotientNaturality, Category.assoc,
    residualStageReduction]
  have hr := residualUniversalStage J b h s j
  have hi : (residualUniversal J b h s).inv ≫
      Spec.map ((quotientDiagramFunctor E (J.map b.hom)).map
        ((stageColimit (s ≫ residualInclusion J b h)).ι.app (op j))) ≫
          (residualStageIso J b h s).hom.app j =
      limit.π (UniversalCover.diagram s)
        ((smallPointedEquiv (residualInclusion J b h) s).functor.obj j) := by
    rw [← hr, Iso.inv_hom_id_assoc]
  have hi' := congrArg (fun f ↦ UniversalCover.pt s ≫ f ≫
    ((smallFiniteIso (residualInclusion J b h) s).inv.app j).hom.left ≫
      pullback.fst ((UniversalCover.obj (s ≫ residualInclusion J b h)).obj j).obj.hom
        (residualInclusion J b h)) hi
  simp only [Category.assoc] at hi'
  apply hi'.trans
  rw [← Category.assoc, UniversalCover.pt_π, UniversalCover.pt_π]
  have hp := congrArg (fun x ↦ x.left) (smallFinitePoint (residualInclusion J b h) s j)
  simp only [FiniteEtale.fiber_map_left] at hp
  have ha := congrArg (fun f ↦ f.hom.left)
    ((smallFiniteIso (residualInclusion J b h) s).hom_inv_id_app j)
  change _ ≫ _ = 𝟙 _ at ha
  rw [← hp, Category.assoc, ← Category.assoc
    (((smallFiniteIso (residualInclusion J b h) s).hom.app j).hom.left), ha,
    Category.id_comp]
  exact pullback.lift_fst _ _ _

end ResidualGeometry

section Zero
private theorem bijective_of_quotient_bot {B D : Type u} [CommRing B] [CommRing D]
    (f : B →+* D)
    (hf : Function.Bijective (Ideal.quotientMap ((⊥ : Ideal B).map f) f
      Ideal.le_comap_map)) : Function.Bijective f := by
  have hi : (⊥ : Ideal B).map f = ⊥ := Ideal.map_bot
  constructor
  · intro x y hxy
    have h : Ideal.Quotient.mk (⊥ : Ideal B) x = Ideal.Quotient.mk ⊥ y :=
      hf.1 (by simpa using congrArg (Ideal.Quotient.mk _) hxy)
    have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
    exact sub_eq_zero.mp ((Ideal.mem_bot).mp hm)
  · intro y
    obtain ⟨x, hx⟩ := hf.2 (Ideal.Quotient.mk _ y)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨b, ?_⟩
    have hm : f b - y ∈ (⊥ : Ideal D) := by
      rw [← hi]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hx
    exact sub_eq_zero.mp ((Ideal.mem_bot).mp hm)

end Zero

/-- Pair henselization lifts the pointed universal residual finite-etale cover.
Source: Stacks 0A02, 0AGV, 09XK, 09XI, 09ZS
(blueprint: lem-sfb-henselian-pointed-residual-cover-lift).

Proof: (1) Apply pair_henselization and pair_henselization_noetherian_completion to
obtain henselianity, the canonical residual isomorphism, Noetherianity and ind-etaleness.
(2) Unique idempotent lifting and connectedSpace_iff_isIdempotentElem give connectedness
of Spec E; its residual geometric point gives nonemptiness.
(3) Apply finite-etale lifting to the proper identity of Spec E (Stacks 09ZS).
(4) The canonical pullback fibre isomorphism identifies pointed morphisms and intertwines
automorphisms. Idempotent lifting preserves and reflects connectedness; simple transitivity
of the automorphism action is therefore preserved. Restrict to pointed Galois covers and
pass to the existing small models to obtain pointed_equivalence and finite_iso.
(5) Use the cofiltered pointed Galois system (lem-sfb-pointed-galois-limit-geometry),
which has common refinements and unique pointed arrows. Finite morphisms are affine, so
choose their coordinate rings compatibly by global sections. The Spec-limit equivalence
identifies their ring colimit with the existing universal cover. Finite E-algebras are
Noetherian (lem-weil-pbc-finite-algebra-noetherian).
(6) Every colimit element comes from a finite stage and is integral over E; hence the
colimit is integral. Apply henselianRing_of_isIntegral both to finite stages and to H.
(7) Henselian ideals lie in the Jacobson radical (09XI): otherwise CRT in the finite
algebra A/(I intersect m) gives two distinct idempotents with the same reduction.
(8) Finite etale maps are ind-etale; compose with B to E and pass to the filtered colimit
using indEtale_principalZariski_stability.
(9) Compatible maps from C/JC to a test ring are compatible maps from C killing J.
The colimit universal property then gives precisely maps from H/JH. This proves the
asserted quotient colimit with its canonical coprojections. The finite-etale equivalence
identifies its diagram and its pointed limit with the residual universal cover; the
pointed finite-etale limit-cover theorem supplies connectedness and the covering.
(10) When J=0 every algebra in the henselization diagram is already isomorphic to B,
so the canonical map B to E is itself an isomorphism. -/
theorem henselian_pointed_residual_cover_lift (B : Type u) [CommRing B]
    [IsNoetherianRing B] (J : Ideal B) [ConnectedSpace (Spec (.of (B ⧸ J)))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J)))
    (c : Cocone (ObjectProperty.ι (fun A : Under (CommRingCat.of B) ↦
      Etale (Spec.map A.hom) ∧ Function.Bijective
        (Ideal.quotientMap (J.map A.hom.hom) A.hom.hom Ideal.le_comap_map))))
    (hc : IsColimit c) :
    ∃ (hE : ConnectedSpace (Spec c.pt.right))
      (h : Function.Bijective
        (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom Ideal.le_comap_map)),
      IsNoetherianRing c.pt.right ∧ HenselianRing c.pt.right (J.map c.pt.hom.hom) ∧
      J.map c.pt.hom.hom ≤ Ideal.jacobson ⊥ ∧
      RingHom.IndEtaleAcrossUniverses c.pt.hom.hom ∧
      (J = ⊥ → Function.Bijective c.pt.hom.hom) ∧
      Nonempty (@LiftData B _ J c.pt.right c.pt.hom hE inferInstance h Ω _ _ s) := by
  classical
  have hH := henselian_given_colimit B J c hc
  let := hH
  have h : Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom)
      c.pt.hom.hom Ideal.le_comap_map) := by
    have hh := (RingTheory.pair_henselization_flat_quotients B J c hc).2
    have hh' := hh 1 (by omega)
    convert hh' using 1 <;> rw [pow_one]
  have hq : ConnectedSpace (Spec (.of (c.pt.right ⧸ J.map c.pt.hom.hom))) :=
    (Spec.map (CommRingCat.ofHom (residualEquiv J c.pt.hom h).toRingHom)).homeomorph
      |>.connectedSpace_iff.mpr inferInstance
  let := hq
  have hE := connected_of_quotient c.pt.right (J.map c.pt.hom.hom)
  let := hE
  have hN := (RingTheory.pair_henselization_noetherian_completion B J c hc).1
  let := hN
  have hInd := henselization_indEtale B J c hc
  have hRed := reduction_equivalence J c.pt.hom h
  let := hRed
  let t := s ≫ residualInclusion J c.pt.hom h
  let : CategoryTheory.IsConnected (UniversalCover.Index t)ᵒᵖ := IsFiltered.isConnected _
  have hComp {D : Type u} [CommRing D] (f : c.pt.right →+* D) (hf : f.IndEtale) :
      (f.comp c.pt.hom.hom).IndEtaleAcrossUniverses := by
    apply indEtale_ulift
    rw [RingHom.IndEtale.iff_ind_etale, CommRingCat.ofHom_comp]
    exact (MorphismProperty.ind CommRingCat.etale).comp_mem _ _
      ((RingHom.IndEtale.iff_ind_etale _).mp hInd)
      ((RingHom.IndEtale.iff_ind_etale _).mp hf)
  refine ⟨hE, h, hN, hH, HenselianRing.jac, indEtale_ulift _ hInd, ?_, ?_⟩
  · intro hJ
    subst J
    exact bijective_of_quotient_bot c.pt.hom.hom h
  · refine ⟨{
      reduction_equivalence := hRed
      pointed_equivalence := smallPointedEquiv (residualInclusion J c.pt.hom h) s
      finite_iso := smallFiniteIso (residualInclusion J c.pt.hom h) s
      finite_point := smallFinitePoint (residualInclusion J c.pt.hom h) s
      automorphisms := fun Y ↦ (Functor.FullyFaithful.ofFullyFaithful
        (FiniteEtale.pullback (residualInclusion J c.pt.hom h))).isoEquiv.bijective
      stages := stageRings t
      stage_iso := stageIso t
      stage_over := stageOver t
      noetherian := stageNoetherian t
      henselian := stageHenselian t (J.map c.pt.hom.hom)
      radical := fun j ↦ by
        let := stageHenselian t (J.map c.pt.hom.hom) j
        exact HenselianRing.jac
      connected := stageConnected t
      indEtale := ?_
      colimit := stageColimit t
      isColimit := stageIsColimit t
      henselian_colimit := colimitHenselian t (J.map c.pt.hom.hom)
      radical_colimit := by
        let := colimitHenselian t (J.map c.pt.hom.hom)
        exact HenselianRing.jac
      indEtale_colimit := hComp _ (stageColimitEtale t)
      universal := stageUniversal t
      universal_over := stageUniversalOver t
      universal_stage := stageUniversalStage t
      residual_stage_iso := residualStageIso J c.pt.hom h s
      residual_stage_over := residualStageOver J c.pt.hom h s
      residual_stage_reduction := residualStageReduction J c.pt.hom h s
      quotient_colimit := quotientColimit _ _ _ (stageIsColimit t)
      residual_universal := residualUniversal J c.pt.hom h s
      residual_universal_over := residualUniversalOver J c.pt.hom h s
      residual_universal_stage := residualUniversalStage J c.pt.hom h s
      residual_point := residualPoint J c.pt.hom h s
      residual_connected := ?_
      residual_weaklyEtale := ?_
      residual_covering := ?_ }⟩
    · intro j
      apply hComp
      exact (RingHom.IndEtale.iff_ind_etale _).mpr
        (MorphismProperty.le_ind _ _ (stageSpecEtale t j))
    · exact (residualUniversal J c.pt.hom h s).hom.homeomorph.connectedSpace_iff.mpr
        inferInstance
    · rw [← residualUniversalOver J c.pt.hom h s]
      infer_instance
    · rw [← residualUniversalOver J c.pt.hom h s]
      let : Surjective (UniversalCover.proj s) := ⟨UniversalCover.surjective_proj s⟩
      exact Scheme.Hom.singleton_mem_propQCPrecoverage inferInstance

end AlgebraicGeometry.Scheme.HenselianPointedResidualCover
