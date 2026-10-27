module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Group.TransferInstance

/-!
# Filtered colimits of varying prelog pushouts

Source: Stacks, Categories, Tag 04AX, following Definition 002V; the finite-witness
argument for varying prelog monoids in the node proof
(blueprint: lem-trf-filtered-varying-prelog-pushout).

All quotients use `divisorialChartPushout` via range restriction. Its generators
`(e,1) ~ (1,γ(e))` generate exactly the relations `(me,a) ~ (m,γ(e)a)`.
The comparison is the canonical map from the chosen colimit in sets, not a chosen
bijection. All maps below are specified on the exhaustive pair representatives.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A compatible prelog map sends the generating congruence into the target
congruence. Source: Stacks 04AX, node proof Step 2: a ring map preserves units and
`r(γ(e)) = δ(h(e))`, so each generating pair maps to a generating pair; closure
under multiplication and equivalence gives the kernel inclusion.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogPushoutMap_wellDefined {P S A D : Type u}
    [CommMonoid P] [CommMonoid S] [CommRing A] [CommRing D]
    (γ : P →* A) (δ : S →* D) (h : P →* S) (r : A →+* D)
    (_w : r.toMonoidHom.comp γ = δ.comp h) :
    divisorialChartCongruence γ.mrangeRestrict ≤
      Con.ker (((divisorialChartCongruence δ.mrangeRestrict).mk').comp
        (h.prodMap (Units.map r.toMonoidHom))) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨p, a, ha, rfl, rfl⟩
  apply (divisorialChartCongruence δ.mrangeRestrict).eq.mpr
  change divisorialChartCongruence δ.mrangeRestrict
    (h p, Units.map r.toMonoidHom 1) (h 1, Units.map r.toMonoidHom a)
  rw [map_one, map_one]
  apply Con.le_conGen
  refine ⟨h p, Units.map r.toMonoidHom a, ?_, rfl, rfl⟩
  change δ (h p) = r (a : A)
  exact (DFunLike.congr_fun _w p).symm.trans (congrArg r ha)

/-- The canonical map on prelog pushouts, sending `[p,a]` to `[h(p),r(a)]`.
Source: Stacks 04AX, node proof Step 2
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
def prelogPushoutMap {P S A D : Type u}
    [CommMonoid P] [CommMonoid S] [CommRing A] [CommRing D]
    (γ : P →* A) (δ : S →* D) (h : P →* S) (r : A →+* D)
    (w : r.toMonoidHom.comp γ = δ.comp h) :
    divisorialChartPushout γ.mrangeRestrict ⟶ divisorialChartPushout δ.mrangeRestrict :=
  CommMonCat.ofHom ((divisorialChartCongruence γ.mrangeRestrict).lift
    (((divisorialChartCongruence δ.mrangeRestrict).mk').comp
      (h.prodMap (Units.map r.toMonoidHom)))
    (prelogPushoutMap_wellDefined γ δ h r w))

/-- Identity on pair representatives gives the identity quotient map.
Source: Stacks 04AX, node proof Step 2; pair representatives exhaust the quotient.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogPushoutMap_id {P A : Type u} [CommMonoid P] [CommRing A]
    (γ : P →* A) :
    prelogPushoutMap γ γ (MonoidHom.id P) (RingHom.id A) (by rfl) = 𝟙 _ := by
  ext x
  obtain ⟨⟨p, a⟩, rfl⟩ := Con.mk'_surjective x
  rfl

/-- Composition on representatives gives composition of quotient maps.
Source: Stacks 04AX, node proof Step 2: both sides send `[p,a]` to
`[k(h(p)),s(r(a))]`; quotient surjectivity gives equality.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogPushoutMap_comp {P S T A D E : Type u}
    [CommMonoid P] [CommMonoid S] [CommMonoid T]
    [CommRing A] [CommRing D] [CommRing E]
    (γ : P →* A) (δ : S →* D) (ε : T →* E)
    (h : P →* S) (k : S →* T) (r : A →+* D) (s : D →+* E)
    (w : r.toMonoidHom.comp γ = δ.comp h)
    (v : s.toMonoidHom.comp δ = ε.comp k)
    (wv : (s.comp r).toMonoidHom.comp γ = ε.comp (k.comp h)) :
    prelogPushoutMap γ ε (k.comp h) (s.comp r) wv =
      prelogPushoutMap γ δ h r w ≫ prelogPushoutMap δ ε k s v := by
  ext x
  obtain ⟨⟨p, a⟩, rfl⟩ := Con.mk'_surjective x
  rfl

/-- The structural map on pairs annihilates the pushout congruence.
Source: Stacks 04AX, node proof Step 2: `γ(me)a = γ(m)γ(e)a`, so each generator
has equal structural image, and hence so does its generated congruence.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogPushoutStructural_wellDefined {P A : Type u} [CommMonoid P] [CommRing A]
    (γ : P →* A) :
    divisorialChartCongruence γ.mrangeRestrict ≤
      Con.ker (γ.coprod (Units.coeHom A)) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨p, a, ha, rfl, rfl⟩
  change γ p * (1 : Aˣ).val = γ 1 * a.val
  simpa using ha

/-- The structural map `[p,a] ↦ γ(p)a` of the actual quotient.
Source: Stacks 04AX, node proof Step 2
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
def prelogPushoutStructural {P A : Type u} [CommMonoid P] [CommRing A] (γ : P →* A) :
    divisorialChartPushout γ.mrangeRestrict →* A :=
  (divisorialChartCongruence γ.mrangeRestrict).lift (γ.coprod (Units.coeHom A))
    (prelogPushoutStructural_wellDefined γ)

/-- The component of a prelog natural transformation, with its ring codomain explicit.
Source: Stacks 04AX, the compatible maps γᵢ in the node statement
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
def prelogComponent {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u})
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) (i : I) : M.obj i →* B.obj i :=
  (γ.app i).hom

/-- The diagram of the actual quotient pushouts with their prescribed transition maps.
Source: Stacks 04AX, node proof Step 2
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
def prelogPushoutDiagram {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u})
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) : I ⥤ CommMonCat.{u} where
  obj i := divisorialChartPushout (prelogComponent M B γ i).mrangeRestrict
  map {i j} f := prelogPushoutMap (prelogComponent M B γ i) (prelogComponent M B γ j) (M.map f).hom
    (B.map f).hom (congrArg CommMonCat.Hom.hom (γ.naturality f)).symm
  map_id i := by
    simpa using prelogPushoutMap_id (prelogComponent M B γ i)
  map_comp {i j k} f g := by
    simpa using prelogPushoutMap_comp (prelogComponent M B γ i)
      (prelogComponent M B γ j) (prelogComponent M B γ k)
      (M.map f).hom (M.map g).hom (B.map f).hom (B.map g).hom
      (congrArg CommMonCat.Hom.hom (γ.naturality f)).symm
      (congrArg CommMonCat.Hom.hom (γ.naturality g)).symm
      (by
        ext x
        exact (congrArg (B.map g)
          (ConcreteCategory.congr_hom (γ.naturality f) x).symm).trans
            (ConcreteCategory.congr_hom (γ.naturality g) (M.map f x)).symm)

/-- The cocone to the ring colimit obtained by composing the prelog maps with the
ring coprojections. Source: Stacks 04AX, compatibility of the given diagram maps
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
noncomputable def prelogRingColimitCocone {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) : Cocone M where
  pt := CommMonCat.of ↥(colimit B)
  ι.app i := CommMonCat.ofHom ((colimit.ι B i).hom.toMonoidHom.comp (prelogComponent M B γ i))
  ι.naturality {i j} f := by
    ext x
    have h := ConcreteCategory.congr_hom (γ.naturality f) x
    have k := ConcreteCategory.congr_hom (colimit.w B f) (γ.app i x)
    exact (congrArg (colimit.ι B j) h).trans k

/-- The induced prelog map on the two chosen colimits. This is the colimit desc
of the given compatible maps, so it is uniquely characterized.
Source: Stacks 04AX, node proof Step 2
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
noncomputable def prelogColimitMap {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) : ↥(colimit M) →* ↥(colimit B) :=
  (colimit.desc M (prelogRingColimitCocone M B γ)).hom

/-- The coprojections are compatible with the induced prelog map.
Source: Stacks 04AX, node proof Step 2, by the defining colimit factorization.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogColimitMap_ι {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) (i : I) :
    (colimit.ι B i).hom.toMonoidHom.comp (prelogComponent M B γ i) =
      (prelogColimitMap M B γ).comp (colimit.ι M i).hom := by
  exact (congrArg CommMonCat.Hom.hom
    (colimit.ι_desc (prelogRingColimitCocone M B γ) i)).symm

/-- The canonical quotient maps from each stage to the limiting pushout form a cocone.
Source: Stacks 04AX, node proof Step 2. On `[m,a]` both routes send the two entries
through the same colimit coprojections, by the cocone laws.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogPushoutCocone_naturality {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) {i j : I} (f : i ⟶ j) :
    (prelogPushoutDiagram M B γ).map f ≫
      prelogPushoutMap (prelogComponent M B γ j) (prelogColimitMap M B γ)
        (colimit.ι M j).hom (colimit.ι B j).hom (prelogColimitMap_ι M B γ j) =
      prelogPushoutMap (prelogComponent M B γ i) (prelogColimitMap M B γ)
        (colimit.ι M i).hom (colimit.ι B i).hom (prelogColimitMap_ι M B γ i) := by
  ext x
  obtain ⟨⟨p, a⟩, rfl⟩ := Con.mk'_surjective x
  change (divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict).mk'
    (colimit.ι M j (M.map f p),
      Units.map (colimit.ι B j).hom.toMonoidHom (Units.map (B.map f).hom.toMonoidHom a)) =
    (divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict).mk'
      (colimit.ι M i p, Units.map (colimit.ι B i).hom.toMonoidHom a)
  congr 1
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (colimit.w M f) p
  · apply Units.ext
    exact ConcreteCategory.congr_hom (colimit.w B f) a.val

/-- The canonical cocone from the stage quotients to the limiting quotient.
Source: Stacks 04AX, node proof Step 2
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
noncomputable def prelogPushoutCocone {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) : Cocone (prelogPushoutDiagram M B γ) where
  pt := divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict
  ι.app i := prelogPushoutMap (prelogComponent M B γ i) (prelogColimitMap M B γ)
    (colimit.ι M i).hom (colimit.ι B i).hom (prelogColimitMap_ι M B γ i)
  ι.naturality {i j} f := by
    simpa using prelogPushoutCocone_naturality M B γ f

/-- The canonical set-colimit comparison, formed by the universal property of colimits.
Source: Stacks 04AX, node proof Step 3
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
noncomputable def filteredPrelogPushoutComparison {I : Type u} [SmallCategory I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) :
    colimit (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) →
      divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict :=
  fun x ↦ colimit.desc _ ((forget CommMonCat).mapCocone (prelogPushoutCocone M B γ)) x

private def prelogUnitDiagram {I : Type u} [SmallCategory I]
    (B : I ⥤ CommRingCat.{u}) : I ⥤ CommMonCat.{u} where
  obj i := CommMonCat.of (B.obj i)ˣ
  map f := CommMonCat.ofHom (Units.map (B.map f).hom.toMonoidHom)
  map_id i := by ext a; simp
  map_comp f g := by ext a; simp

private noncomputable def prelogUnitCocone {I : Type u} [SmallCategory I]
    (B : I ⥤ CommRingCat.{u}) [HasColimit B] : Cocone (prelogUnitDiagram B) where
  pt := CommMonCat.of (↥(colimit B))ˣ
  ι.app i := CommMonCat.ofHom (Units.map (colimit.ι B i).hom.toMonoidHom)
  ι.naturality {i j} f := by
    apply CommMonCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Units.ext
    exact ConcreteCategory.congr_hom (colimit.w B f) a.val

private theorem prelog_eventually_unit {I : Type u} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommRingCat.{u}) [HasColimit B] (i : I) (x : B.obj i)
    (hx : IsUnit (colimit.ι B i x)) :
    ∃ (j : I) (f : i ⟶ j), IsUnit (B.map f x) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨j, y, hy⟩ := Concrete.colimit_exists_rep B (a⁻¹ : (↥(colimit B))ˣ).val
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  have hxy : colimit.ι B k (B.map f x * B.map g y) = colimit.ι B k 1 := by
    have hf : colimit.ι B k (B.map f x) = colimit.ι B i x :=
      ConcreteCategory.congr_hom (colimit.w B f) x
    have hg : colimit.ι B k (B.map g y) = colimit.ι B j y :=
      ConcreteCategory.congr_hom (colimit.w B g) y
    rw [map_mul, hf, hg, hy, ← ha, map_one]
    exact a.val_inv
  have hR := isColimitOfPreserves (forget CommRingCat) (colimit.isColimit B)
  obtain ⟨l, q, hq⟩ := (Types.FilteredColimit.isColimit_eq_iff' hR _ _).mp hxy
  change B.map q (B.map f x * B.map g y) = B.map q 1 at hq
  have he : B.map q (B.map f x) * B.map q (B.map g y) = 1 := by
    simpa only [map_mul, map_one] using hq
  refine ⟨l, f ≫ q, ?_⟩
  rw [B.map_comp]
  exact ⟨⟨B.map q (B.map f x), B.map q (B.map g y), he,
    by rwa [mul_comm]⟩, rfl⟩

private noncomputable def prelogUnitCoconeIsColimit {I : Type u}
    [SmallCategory I] [IsFiltered I] (B : I ⥤ CommRingCat.{u}) [HasColimit B] :
    IsColimit (prelogUnitCocone B) := by
  let : HasColimit (prelogUnitDiagram B) :=
    ⟨⟨_, CommMonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} (prelogUnitDiagram B)⟩⟩
  let : ReflectsColimit (prelogUnitDiagram B) (forget CommMonCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommMonCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    change (↥(colimit B))ˣ at a
    obtain ⟨i, x, hx⟩ := Concrete.colimit_exists_rep B a.val
    obtain ⟨j, f, b, hb⟩ := prelog_eventually_unit B i x (hx.symm ▸ a.isUnit)
    refine ⟨j, b, ?_⟩
    apply Units.ext
    change a.val = colimit.ι B j b.val
    rw [hb]
    exact hx.symm.trans (ConcreteCategory.congr_hom (colimit.w B f) x).symm
  · intro i a b hab
    have hR := isColimitOfPreserves (forget CommRingCat) (colimit.isColimit B)
    have hv : colimit.ι B i a.val = colimit.ι B i b.val := congrArg Units.val hab
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hR _ _).mp hv
    exact ⟨j, f, Units.ext hf⟩

section PrelogDescent

variable {I : Type u} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat)

private noncomputable def prelogMonoidLegs
    (s : Cocone (prelogPushoutDiagram M B γ)) : Cocone M where
  pt := s.pt
  ι.app i := CommMonCat.ofHom ((s.ι.app i).hom.comp
    ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk'.comp
      (MonoidHom.inl (M.obj i) (B.obj i)ˣ)))
  ι.naturality {i j} f := by
    ext m
    have hn := ConcreteCategory.congr_hom (s.w f)
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, 1))
    change s.ι.app j
      ((divisorialChartCongruence (prelogComponent M B γ j).mrangeRestrict).mk'
        (M.map f m, Units.map (B.map f).hom.toMonoidHom 1)) = _ at hn
    rw [map_one] at hn
    exact hn

private noncomputable def prelogUnitLegs
    (s : Cocone (prelogPushoutDiagram M B γ)) : Cocone (prelogUnitDiagram B) where
  pt := s.pt
  ι.app i := CommMonCat.ofHom ((s.ι.app i).hom.comp
    ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk'.comp
      (MonoidHom.inr (M.obj i) (B.obj i)ˣ)))
  ι.naturality {i j} f := by
    ext a
    have hn := ConcreteCategory.congr_hom (s.w f)
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (1, a))
    change s.ι.app j
      ((divisorialChartCongruence (prelogComponent M B γ j).mrangeRestrict).mk'
        (M.map f 1, Units.map (B.map f).hom.toMonoidHom a)) = _ at hn
    rw [map_one] at hn
    exact hn

private noncomputable def prelogPairLift
    (s : Cocone (prelogPushoutDiagram M B γ)) :
    (↥(colimit M) × (↥(colimit B))ˣ) →* s.pt :=
  (colimit.desc M (prelogMonoidLegs M B γ s)).hom.coprod
    ((prelogUnitCoconeIsColimit B).desc (prelogUnitLegs M B γ s)).hom

private theorem prelogPairLift_ι (s : Cocone (prelogPushoutDiagram M B γ))
    (i : I) (m : M.obj i) (a : (B.obj i)ˣ) :
    prelogPairLift M B γ s
      (colimit.ι M i m, Units.map (colimit.ι B i).hom.toMonoidHom a) =
    s.ι.app i
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, a)) := by
  have hm := ConcreteCategory.congr_hom (colimit.ι_desc (prelogMonoidLegs M B γ s) i) m
  have ha := ConcreteCategory.congr_hom
    ((prelogUnitCoconeIsColimit B).fac (prelogUnitLegs M B γ s) i) a
  change (colimit.desc M (prelogMonoidLegs M B γ s)) (colimit.ι M i m) =
    s.ι.app i
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, 1)) at hm
  change ((prelogUnitCoconeIsColimit B).desc (prelogUnitLegs M B γ s))
    (Units.map (colimit.ι B i).hom.toMonoidHom a) =
    s.ι.app i
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (1, a)) at ha
  refine (congrArg₂ (fun x y : s.pt ↦ x * y) hm ha).trans ?_
  let q := (divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk'
  have hq : q (m, 1) * q (1, a) = q (m, a) := by
    rw [← map_mul]
    congr 1
    simp
  exact ((s.ι.app i).hom.map_mul _ _).symm.trans (congrArg (s.ι.app i) hq)

private theorem prelogPairLift_wellDefined (s : Cocone (prelogPushoutDiagram M B γ)) :
    divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict ≤
      Con.ker (prelogPairLift M B γ s) := by
  apply Con.conGen_le.mpr
  rintro x y ⟨p, a, ha, rfl, rfl⟩
  change prelogColimitMap M B γ p = a.val at ha
  obtain ⟨i, m, hm⟩ := Concrete.colimit_exists_rep M p
  have hi : IsUnit (colimit.ι B i (prelogComponent M B γ i m)) := by
    have he := DFunLike.congr_fun (prelogColimitMap_ι M B γ i) m
    change colimit.ι B i (prelogComponent M B γ i m) =
      prelogColimitMap M B γ (colimit.ι M i m) at he
    rw [he, hm]
    exact ha.symm ▸ a.isUnit
  obtain ⟨j, f, b, hb⟩ := prelog_eventually_unit B i (prelogComponent M B γ i m) hi
  have hp : colimit.ι M j (M.map f m) = p :=
    (ConcreteCategory.congr_hom (colimit.w M f) m).trans hm
  have hβ : prelogComponent M B γ j (M.map f m) = b.val :=
    (ConcreteCategory.congr_hom (γ.naturality f) m).trans hb.symm
  have hu : Units.map (colimit.ι B j).hom.toMonoidHom b = a := by
    apply Units.ext
    change colimit.ι B j b.val = a.val
    rw [← hβ]
    have he := DFunLike.congr_fun (prelogColimitMap_ι M B γ j) (M.map f m)
    change colimit.ι B j (prelogComponent M B γ j (M.map f m)) =
      prelogColimitMap M B γ (colimit.ι M j (M.map f m)) at he
    exact he.trans ((congrArg (prelogColimitMap M B γ) hp).trans ha)
  change prelogPairLift M B γ s (p, 1) = prelogPairLift M B γ s (1, a)
  have hl := prelogPairLift_ι M B γ s j (M.map f m) 1
  have hr := prelogPairLift_ι M B γ s j 1 b
  simp only [map_one, hp, hu] at hl hr
  rw [hl, hr]
  apply congrArg (s.ι.app j)
  apply (divisorialChartCongruence (prelogComponent M B γ j).mrangeRestrict).eq.mpr
  apply Con.le_conGen
  exact ⟨M.map f m, b, hβ, rfl, rfl⟩

private noncomputable def prelogDesc (s : Cocone (prelogPushoutDiagram M B γ)) :
    divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict ⟶ s.pt :=
  CommMonCat.ofHom ((divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict).lift
    (prelogPairLift M B γ s) (prelogPairLift_wellDefined M B γ s))

private theorem prelogDesc_ι (s : Cocone (prelogPushoutDiagram M B γ)) (i : I) :
    (prelogPushoutCocone M B γ).ι.app i ≫ prelogDesc M B γ s = s.ι.app i := by
  ext x
  obtain ⟨⟨m, a⟩, rfl⟩ := Con.mk'_surjective x
  exact prelogPairLift_ι M B γ s i m a

end PrelogDescent

private theorem prelogPushout_hom_ext {I : Type u} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) {S : CommMonCat.{u}}
    (f g : divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict ⟶ S)
    (h : ∀ i, (prelogPushoutCocone M B γ).ι.app i ≫ f =
      (prelogPushoutCocone M B γ).ι.app i ≫ g) : f = g := by
  let q := (divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict).mk'
  have hm : ∀ p : ↥(colimit M), f (q (p, 1)) = g (q (p, 1)) := by
    intro p
    obtain ⟨i, m, rfl⟩ := Concrete.colimit_exists_rep M p
    have he := ConcreteCategory.congr_hom (h i)
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, 1))
    change f (q (colimit.ι M i m, Units.map (colimit.ι B i).hom.toMonoidHom 1)) =
      g (q (colimit.ι M i m, Units.map (colimit.ι B i).hom.toMonoidHom 1)) at he
    simpa only [map_one] using he
  have hu : ∀ a : (↥(colimit B))ˣ, f (q (1, a)) = g (q (1, a)) := by
    intro a
    obtain ⟨i, b, hb⟩ := Concrete.isColimit_exists_rep
      (prelogUnitDiagram B) (prelogUnitCoconeIsColimit B) a
    change Units.map (colimit.ι B i).hom.toMonoidHom b = a at hb
    have he := ConcreteCategory.congr_hom (h i)
      ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (1, b))
    change f (q (colimit.ι M i 1, Units.map (colimit.ι B i).hom.toMonoidHom b)) =
      g (q (colimit.ι M i 1, Units.map (colimit.ι B i).hom.toMonoidHom b)) at he
    simpa only [map_one, hb] using he
  ext x
  obtain ⟨⟨p, a⟩, rfl⟩ := Con.mk'_surjective x
  change f (q (p, a)) = g (q (p, a))
  have hq : q (p, a) = q (p, 1) * q (1, a) := by
    rw [← map_mul]
    simp
  rw [hq, map_mul, map_mul, hm, hu]

private noncomputable def prelogPushoutIsColimit {I : Type u} [SmallCategory I]
    [IsFiltered I] (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u})
    [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) :
    IsColimit (prelogPushoutCocone M B γ) where
  desc s := prelogDesc M B γ s
  fac s i := prelogDesc_ι M B γ s i
  uniq s m hm := prelogPushout_hom_ext M B γ m (prelogDesc M B γ s)
    (fun i ↦ (hm i).trans (prelogDesc_ι M B γ s i).symm)

/-- Filtered colimits commute with adjoining ring units to varying prelog monoids.
Source: Stacks 04AX, eventual equality after Definition 002V, node proof Steps 1--9.
Proof: combine finitely many objects and arrows at one compatible target, equalizing
parallel arrows. Forgetting a filtered monoid colimit gives a set colimit. An inverse
of a ring element has a stage representative; its inverse equation holds eventually,
so every limiting unit has a stage unit representative, including from any prescribed
stage where its value is represented. Represent a limiting monoid element and a unit
at a common stage and send the pair to that stage's quotient class in the colimit.
Eventual equality of both coordinates proves independence, using one target commuting
with both witness diagrams. Common-stage products make this a monoid map. For a
limiting generator, eventually its monoid element maps to a unit; the corresponding
stage relation therefore identifies its two images. The map descends through the
generated congruence and is inverse to the displayed canonical comparison on every
pair representative. Multiplication is precisely common-stage multiplication. The
structural and inclusion formulas follow by evaluation on pairs. No cancellation,
finiteness or injectivity is used. Naturality is stated below on exhaustive representatives.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem filtered_varying_prelog_pushout {I : Type u} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat) :
    Function.Bijective (filteredPrelogPushoutComparison M B γ) ∧
    (∀ (i : I) (m : M.obj i) (a : (B.obj i)ˣ),
      filteredPrelogPushoutComparison M B γ
        (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i
          ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, a))) =
      (divisorialChartCongruence (prelogColimitMap M B γ).mrangeRestrict).mk'
        (colimit.ι M i m, Units.map (colimit.ι B i).hom.toMonoidHom a)) ∧
    (∃ c : CommMonoid (colimit (prelogPushoutDiagram M B γ ⋙ forget CommMonCat)),
      ∃ e : @MulEquiv
          (colimit (prelogPushoutDiagram M B γ ⋙ forget CommMonCat))
          (divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict) c.toMul _,
        e.toFun = filteredPrelogPushoutComparison M B γ ∧
        (∀ (i j k : I) (f : i ⟶ k) (g : j ⟶ k)
          (x : (prelogPushoutDiagram M B γ).obj i)
          (y : (prelogPushoutDiagram M B γ).obj j),
          @Mul.mul _ c.toMul
            (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i x)
            (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) j y) =
          colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) k
            ((prelogPushoutDiagram M B γ).map f x *
              (prelogPushoutDiagram M B γ).map g y)) ∧
        (∀ i : I, @One.one _ c.toOne =
          colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i 1)) ∧
    (∀ (i : I) (m : M.obj i) (a : (B.obj i)ˣ),
      prelogPushoutStructural (prelogColimitMap M B γ)
        (filteredPrelogPushoutComparison M B γ
          (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i
            ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, a)))) =
      colimit.ι B i (prelogPushoutStructural (prelogComponent M B γ i)
        ((divisorialChartCongruence (prelogComponent M B γ i).mrangeRestrict).mk' (m, a)))) := by
  classical
  let s := prelogPushoutCocone M B γ
  let c := (forget CommMonCat).mapCocone s
  let hc := isColimitOfPreserves (forget CommMonCat) (prelogPushoutIsColimit M B γ)
  let hL := colimit.isColimit (prelogPushoutDiagram M B γ ⋙ forget CommMonCat)
  let e := hL.coconePointUniqueUpToIso hc
  have he : e.hom = colimit.desc _ c := by
    apply colimit.hom_ext
    intro i
    exact ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc i).trans
      (colimit.ι_desc c i).symm
  have hb : Function.Bijective (filteredPrelogPushoutComparison M B γ) := by
    change Function.Bijective (colimit.desc _ c)
    rw [← he]
    exact e.toEquiv.bijective
  have hι : ∀ (i : I) (z : (prelogPushoutDiagram M B γ).obj i),
      filteredPrelogPushoutComparison M B γ
        (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i z) =
      s.ι.app i z := by
    intro i z
    exact ConcreteCategory.congr_hom (colimit.ι_desc c i) z
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro i m a
    exact hι i _
  · let E := Equiv.ofBijective (filteredPrelogPushoutComparison M B γ) hb
    let cM := E.commMonoid
    let eM : colimit (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) ≃*
        divisorialChartPushout (prelogColimitMap M B γ).mrangeRestrict := E.mulEquiv
    refine ⟨cM, eM, rfl, ?_, ?_⟩
    · intro i j k f g x y
      apply hb.injective
      change eM (_ * _) = eM _
      rw [map_mul]
      change filteredPrelogPushoutComparison M B γ _ *
        filteredPrelogPushoutComparison M B γ _ =
        filteredPrelogPushoutComparison M B γ _
      rw [hι, hι, hι, map_mul]
      have hf := ConcreteCategory.congr_hom (s.w f) x
      have hg := ConcreteCategory.congr_hom (s.w g) y
      exact congrArg₂ (· * ·) hf.symm hg.symm
    · intro i
      apply hb.injective
      change eM 1 = eM _
      rw [map_one]
      change 1 = filteredPrelogPushoutComparison M B γ _
      rw [hι, map_one]
  · intro i m a
    rw [hι]
    change prelogColimitMap M B γ (colimit.ι M i m) *
      (colimit.ι B i).hom a.val =
      colimit.ι B i (prelogComponent M B γ i m * a.val)
    rw [map_mul]
    exact congrArg (· * (colimit.ι B i a.val))
      (DFunLike.congr_fun (prelogColimitMap_ι M B γ i) m).symm

/-- The induced colimit maps commute with the induced prelog structures.
Source: Stacks 04AX, node proof Step 9. Test the two monoid maps on a stage
representative. The two coprojection identities, compatibility at that stage, and
`prelogColimitMap_ι` identify their values. Coprojections jointly determine monoid maps.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem prelogColimitMap_naturality {I J : Type u} [SmallCategory I] [SmallCategory J]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat)
    (N : J ⥤ CommMonCat.{u}) (D : J ⥤ CommRingCat.{u}) [HasColimit N] [HasColimit D]
    (δ : N ⟶ D ⋙ forget₂ CommRingCat CommMonCat)
    (H : I ⥤ J) (h : M ⟶ H ⋙ N) (r : B ⟶ H ⋙ D)
    (_w : ∀ i : I, (r.app i).hom.toMonoidHom.comp (prelogComponent M B γ i) =
      (prelogComponent N D δ (H.obj i)).comp (h.app i).hom)
    (hL : colimit M ⟶ colimit N) (rL : colimit B ⟶ colimit D)
    (_hι : ∀ i : I, colimit.ι M i ≫ hL = h.app i ≫ colimit.ι N (H.obj i))
    (_rι : ∀ i : I, colimit.ι B i ≫ rL = r.app i ≫ colimit.ι D (H.obj i)) :
    rL.hom.toMonoidHom.comp (prelogColimitMap M B γ) =
      (prelogColimitMap N D δ).comp hL.hom := by
  apply MonoidHom.ext
  intro x
  suffices he : CommMonCat.ofHom
      (rL.hom.toMonoidHom.comp (prelogColimitMap M B γ)) =
      CommMonCat.ofHom ((prelogColimitMap N D δ).comp hL.hom) by
    exact ConcreteCategory.congr_hom he x
  apply colimit.hom_ext
  intro i
  ext m
  change rL (prelogColimitMap M B γ (colimit.ι M i m)) =
    prelogColimitMap N D δ (hL (colimit.ι M i m))
  rw [← MonoidHom.comp_apply, ← prelogColimitMap_ι]
  change rL (colimit.ι B i (prelogComponent M B γ i m)) = _
  have hr := ConcreteCategory.congr_hom (_rι i) (prelogComponent M B γ i m)
  have hh := ConcreteCategory.congr_hom (_hι i) m
  change rL (colimit.ι B i (prelogComponent M B γ i m)) =
    colimit.ι D (H.obj i) (r.app i (prelogComponent M B γ i m)) at hr
  change hL (colimit.ι M i m) = colimit.ι N (H.obj i) (h.app i m) at hh
  rw [hr, hh]
  rw [← MonoidHom.comp_apply, ← prelogColimitMap_ι]
  exact congrArg (colimit.ι D (H.obj i)) (DFunLike.congr_fun (_w i) m)

/-- Naturality of the comparison, including reindexing between filtered categories.
It is written after precomposition with every set-colimit coprojection, which are
jointly surjective; hence this is equality of the two canonical maps on the entire
set colimit. The maps `hL` and `rL` are characterized as the induced maps by their
coprojection identities, not arbitrary additional structure.
Source: Stacks 04AX, node proof Step 9. On a pair `[m,a]` both routes give
`[ι'(hᵢ(m)),b'(rᵢ(a))]`. Every stage quotient has pair representatives, and every
set-colimit element has a stage representative, proving the full naturality square.
(blueprint: lem-trf-filtered-varying-prelog-pushout). -/
theorem filtered_varying_prelog_pushout_naturality
    {I J : Type u} [SmallCategory I] [SmallCategory J] [IsFiltered I] [IsFiltered J]
    (M : I ⥤ CommMonCat.{u}) (B : I ⥤ CommRingCat.{u}) [HasColimit M] [HasColimit B]
    (γ : M ⟶ B ⋙ forget₂ CommRingCat CommMonCat)
    (N : J ⥤ CommMonCat.{u}) (D : J ⥤ CommRingCat.{u}) [HasColimit N] [HasColimit D]
    (δ : N ⟶ D ⋙ forget₂ CommRingCat CommMonCat)
    (H : I ⥤ J) (h : M ⟶ H ⋙ N) (r : B ⟶ H ⋙ D)
    (w : ∀ i : I, (r.app i).hom.toMonoidHom.comp (prelogComponent M B γ i) =
      (prelogComponent N D δ (H.obj i)).comp (h.app i).hom)
    (hL : colimit M ⟶ colimit N) (rL : colimit B ⟶ colimit D)
    (hι : ∀ i : I, colimit.ι M i ≫ hL = h.app i ≫ colimit.ι N (H.obj i))
    (rι : ∀ i : I, colimit.ι B i ≫ rL = r.app i ≫ colimit.ι D (H.obj i))
    (i : I) (z : (prelogPushoutDiagram M B γ).obj i) :
    prelogPushoutMap (prelogColimitMap M B γ) (prelogColimitMap N D δ) hL.hom rL.hom
      (prelogColimitMap_naturality M B γ N D δ H h r w hL rL hι rι)
      (filteredPrelogPushoutComparison M B γ
        (colimit.ι (prelogPushoutDiagram M B γ ⋙ forget CommMonCat) i z)) =
      filteredPrelogPushoutComparison N D δ
        (colimit.ι (prelogPushoutDiagram N D δ ⋙ forget CommMonCat) (H.obj i)
          (prelogPushoutMap (prelogComponent M B γ i) (prelogComponent N D δ (H.obj i))
            (h.app i).hom (r.app i).hom (w i) z)) := by
  have formula : ∀ {K : Type u} [SmallCategory K]
      (P : K ⥤ CommMonCat.{u}) (A : K ⥤ CommRingCat.{u})
      [HasColimit P] [HasColimit A]
      (η : P ⟶ A ⋙ forget₂ CommRingCat CommMonCat)
      (k : K) (x : (prelogPushoutDiagram P A η).obj k),
      filteredPrelogPushoutComparison P A η
        (colimit.ι (prelogPushoutDiagram P A η ⋙ forget CommMonCat) k x) =
      (prelogPushoutCocone P A η).ι.app k x := by
    intro K _ P A _ _ η k x
    exact ConcreteCategory.congr_hom
      (colimit.ι_desc ((forget CommMonCat).mapCocone (prelogPushoutCocone P A η)) k) x
  rw [formula, formula]
  obtain ⟨⟨m, a⟩, rfl⟩ := Con.mk'_surjective z
  change (divisorialChartCongruence (prelogColimitMap N D δ).mrangeRestrict).mk'
    (hL (colimit.ι M i m),
      Units.map rL.hom.toMonoidHom (Units.map (colimit.ι B i).hom.toMonoidHom a)) =
    (divisorialChartCongruence (prelogColimitMap N D δ).mrangeRestrict).mk'
      (colimit.ι N (H.obj i) (h.app i m),
        Units.map (colimit.ι D (H.obj i)).hom.toMonoidHom
          (Units.map (r.app i).hom.toMonoidHom a))
  congr 1
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (hι i) m
  · apply Units.ext
    exact ConcreteCategory.congr_hom (rι i) a.val

end AlgebraicGeometry
