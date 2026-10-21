module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.FiniteType

@[expose] public section

/-! # Colimit of localizations

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/`,
node `lem-kun-colim-of-localizations`, order 1748 (blueprint: lem-kun-colim-of-localizations).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Pairs (i,g) with g a nonzero element of the i-th subalgebra. Source: blueprint
node lem-kun-colim-of-localizations (blueprint: lem-kun-colim-of-localizations). -/
abbrev LocalizationPair {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B) :=
  {p : I × B // p.2 ∈ Bi p.1 ∧ p.2 ≠ 0}

/-- The principal localization attached to a pair. Source: blueprint
node lem-kun-colim-of-localizations (blueprint: lem-kun-colim-of-localizations). -/
abbrev PairLocalization {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B) (p : LocalizationPair Bi) :=
  Localization.Away (⟨p.1.2, p.2.1⟩ : Bi p.1.1)

/-- Inclusion of the subalgebras and invertibility of the source denominator in the target
localization. Source: blueprint node lem-kun-colim-of-localizations
(blueprint: lem-kun-colim-of-localizations). -/
def PairLocalizationLE {K : Type v} {B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {I : Type w} (Bi : I → Subalgebra K B)
    (p q : LocalizationPair Bi) : Prop :=
  Bi p.1.1 ≤ Bi q.1.1 ∧
    ∃ x : Bi q.1.1, (x : B) = p.1.2 ∧
      IsUnit (algebraMap (Bi q.1.1) (PairLocalization Bi q) x)

section Construction

variable {K : Type v} {B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    [IsDomain B] {I : Type w} (Bi : I → Subalgebra K B)

private abbrev denom (p : LocalizationPair Bi) : Bi p.1.1 := ⟨p.1.2, p.2.1⟩

@[irreducible]
private noncomputable def embedding (p : LocalizationPair Bi) :
    PairLocalization Bi p →ₐ[K] FractionRing B :=
  IsLocalization.Away.liftAlgHom (denom Bi p)
    (f := (IsScalarTower.toAlgHom K B (FractionRing B)).comp (Bi p.1.1).val)
    (by
      apply isUnit_iff_ne_zero.mpr
      change algebraMap B (FractionRing B) p.1.2 ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective B (FractionRing B)).ne p.2.2)

private theorem embedding_base (p : LocalizationPair Bi) (x : Bi p.1.1) :
    embedding Bi p (algebraMap _ _ x) = algebraMap B (FractionRing B) (x : B) :=
  by
    simp only [embedding, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq]
    rfl

private theorem embedding_injective (p : LocalizationPair Bi) :
    Function.Injective (embedding Bi p) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (denom Bi p)) (embedding Bi p).toRingHom).mpr
  intro x y
  constructor
  · intro h
    exact congrArg (embedding Bi p) h
  · intro h
    change embedding Bi p (algebraMap _ _ x) = embedding Bi p (algebraMap _ _ y) at h
    rw [embedding_base, embedding_base] at h
    have hxy : x = y := Subtype.ext (IsFractionRing.injective B (FractionRing B) h)
    rw [hxy]

@[irreducible]
private noncomputable def transition (p q : LocalizationPair Bi)
    (h : PairLocalizationLE Bi p q) : PairLocalization Bi p →ₐ[K] PairLocalization Bi q :=
  IsLocalization.Away.liftAlgHom (denom Bi p)
    (f := (IsScalarTower.toAlgHom K (Bi q.1.1) (PairLocalization Bi q)).comp
      (Subalgebra.inclusion h.1)) (by
      obtain ⟨x, hx, hu⟩ := h.2
      have hx' : x = Subalgebra.inclusion h.1 (denom Bi p) := Subtype.ext hx
      change IsUnit (algebraMap (Bi q.1.1) (PairLocalization Bi q)
        (Subalgebra.inclusion h.1 (denom Bi p)))
      rw [← hx']
      exact hu)

omit [IsDomain B] in
private theorem transition_base (p q : LocalizationPair Bi)
    (h : PairLocalizationLE Bi p q) (x : Bi p.1.1) :
    transition Bi p q h (algebraMap _ _ x) =
      algebraMap (Bi q.1.1) (PairLocalization Bi q) (Subalgebra.inclusion h.1 x) :=
  by
    simp only [transition, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq]
    rfl

omit [IsDomain B] in
private theorem localization_ext (p : LocalizationPair Bi)
    {A : Type*} [CommRing A] [Algebra K A]
    {f g : PairLocalization Bi p →ₐ[K] A}
    (h : ∀ x : Bi p.1.1, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (denom Bi p))
  exact AlgHom.ext h

private theorem embedding_transition (p q : LocalizationPair Bi)
    (h : PairLocalizationLE Bi p q) :
    (embedding Bi q).comp (transition Bi p q h) = embedding Bi p := by
  apply localization_ext Bi p
  intro x
  simp only [AlgHom.comp_apply, transition_base, embedding_base]
  rfl

omit [IsDomain B] in
private theorem pair_refl (p : LocalizationPair Bi) : PairLocalizationLE Bi p p :=
  ⟨le_rfl, denom Bi p, rfl, IsLocalization.Away.algebraMap_isUnit (denom Bi p)⟩

omit [IsDomain B] in
private theorem pair_trans (p q r : LocalizationPair Bi)
    (hpq : PairLocalizationLE Bi p q) (hqr : PairLocalizationLE Bi q r) :
    PairLocalizationLE Bi p r := by
  obtain ⟨x, hx, hu⟩ := hpq.2
  refine ⟨hpq.1.trans hqr.1, Subalgebra.inclusion hqr.1 x, hx, ?_⟩
  rw [← transition_base Bi q r hqr x]
  exact hu.map (transition Bi q r hqr).toRingHom

private theorem pair_upper (hdirected : ∀ i j : I, ∃ k, Bi i ≤ Bi k ∧ Bi j ≤ Bi k)
    (p q : LocalizationPair Bi) :
    ∃ r, PairLocalizationLE Bi p r ∧ PairLocalizationLE Bi q r := by
  obtain ⟨k, hp, hq⟩ := hdirected p.1.1 q.1.1
  let a : Bi k := ⟨p.1.2, hp p.2.1⟩
  let b : Bi k := ⟨q.1.2, hq q.2.1⟩
  let r : LocalizationPair Bi :=
    ⟨(k, p.1.2 * q.1.2), (Bi k).mul_mem a.2 b.2, mul_ne_zero p.2.2 q.2.2⟩
  refine ⟨r, ⟨hp, a, rfl, ?_⟩, ⟨hq, b, rfl, ?_⟩⟩
  · exact IsLocalization.Away.isUnit_of_dvd (a * b) (dvd_mul_right a b)
  · exact IsLocalization.Away.isUnit_of_dvd (a * b) (dvd_mul_left b a)

private theorem embedding_cover
    (hcover : ∀ b : B, ∃ i, b ∈ Bi i)
    (hdirected : ∀ i j : I, ∃ k, Bi i ≤ Bi k ∧ Bi j ≤ Bi k)
    (x : FractionRing B) :
    ∃ (p : LocalizationPair Bi) (y : PairLocalization Bi p), embedding Bi p y = x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  obtain ⟨i, ha⟩ := hcover a
  obtain ⟨j, hb'⟩ := hcover b
  obtain ⟨k, hi, hj⟩ := hdirected i j
  let p : LocalizationPair Bi := ⟨(k, b), hj hb', nonZeroDivisors.ne_zero hb⟩
  let a' : Bi k := ⟨a, hi ha⟩
  let b' : Submonoid.powers (denom Bi p) := ⟨denom Bi p, Submonoid.mem_powers _⟩
  refine ⟨p, IsLocalization.mk' (PairLocalization Bi p) a' b', ?_⟩
  apply (eq_div_iff (by
    simpa only [map_zero] using (IsFractionRing.injective B (FractionRing B)).ne p.2.2)).mpr
  have h := congrArg (embedding Bi p)
    (IsLocalization.mk'_spec (PairLocalization Bi p) a' b')
  rw [map_mul] at h
  change embedding Bi p (IsLocalization.mk' (PairLocalization Bi p) a' b') *
    embedding Bi p (algebraMap (Bi p.1.1) (PairLocalization Bi p) (denom Bi p)) =
      embedding Bi p (algebraMap (Bi p.1.1) (PairLocalization Bi p) a') at h
  rw [embedding_base, embedding_base] at h
  exact h

end Construction

private theorem cocone_eq_of_eq
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c s : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (i j : J) (a : F.obj i) (b : F.obj j)
    (h : (c.ι.app i).hom a = (c.ι.app j).hom b) :
    (s.ι.app i).hom a = (s.ι.app j).hom b := by
  let k := IsFiltered.max i j
  let l := IsFiltered.leftToMax i j
  let r := IsFiltered.rightToMax i j
  have hc (i : J) (f : i ⟶ k) (x : F.obj i) :
      (c.ι.app k).hom ((F.map f).hom x) = (c.ι.app i).hom x :=
    ConcreteCategory.congr_hom (c.w f) x
  have hs (i : J) (f : i ⟶ k) (x : F.obj i) :
      (s.ι.app k).hom ((F.map f).hom x) = (s.ι.app i).hom x :=
    ConcreteCategory.congr_hom (s.w f) x
  have hab : (F.map l).hom a = (F.map r).hom b :=
    hinj k ((hc i l a).trans (h.trans (hc j r b).symm))
  exact (hs i l a).symm.trans ((congrArg (s.ι.app k).hom hab).trans (hs j r b))

@[irreducible]
private noncomputable def ringDesc
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c s : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (a : F.obj j), (c.ι.app j).hom a = x)
    (f : c.pt → s.pt)
    (hf : ∀ (j : J) (a : F.obj j), f ((c.ι.app j).hom a) = (s.ι.app j).hom a) :
    c.pt →+* s.pt := by
  classical
  have hbinary (op : ∀ R : CommRingCat.{u}, R → R → R)
      (hop : ∀ {R S : CommRingCat.{u}} (g : R ⟶ S) a b,
        g.hom (op R a b) = op S (g.hom a) (g.hom b))
      (x y : c.pt) : f (op c.pt x y) = op s.pt (f x) (f y) := by
    obtain ⟨i, a, rfl⟩ := hsurj x
    obtain ⟨j, b, rfl⟩ := hsurj y
    let k := IsFiltered.max i j
    let l := IsFiltered.leftToMax i j
    let r := IsFiltered.rightToMax i j
    have ha := ConcreteCategory.congr_hom (c.w l) a
    have hb := ConcreteCategory.congr_hom (c.w r) b
    change (c.ι.app k).hom ((F.map l).hom a) = (c.ι.app i).hom a at ha
    change (c.ι.app k).hom ((F.map r).hom b) = (c.ι.app j).hom b at hb
    have hc := hop (R := F.obj k) (S := c.pt) (c.ι.app k)
    have hs := hop (R := F.obj k) (S := s.pt) (s.ι.app k)
    rw [← ha, ← hb]
    exact (congrArg f (hc ((F.map l).hom a) ((F.map r).hom b)).symm).trans
      ((hf k _).trans ((hs _ _).trans (congrArg₂ (op s.pt) (hf k _).symm
        (hf k _).symm)))
  let j : J := Classical.choice (IsFiltered.nonempty (C := J))
  exact
    { toFun := f
      map_zero' := by rw [← (c.ι.app j).hom.map_zero, hf, map_zero]
      map_one' := by rw [← (c.ι.app j).hom.map_one, hf, map_one]
      map_add' := hbinary (fun _ a b ↦ a + b) (fun g ↦ g.hom.map_add)
      map_mul' := hbinary (fun _ a b ↦ a * b) (fun g ↦ g.hom.map_mul) }
private theorem ringDesc_apply
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c s : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (a : F.obj j), (c.ι.app j).hom a = x)
    (f : c.pt → s.pt)
    (hf : ∀ (j : J) (a : F.obj j), f ((c.ι.app j).hom a) = (s.ι.app j).hom a)
    (x : c.pt) : ringDesc F c s hsurj f hf x = f x := by
  unfold ringDesc
  rfl

@[irreducible]
private noncomputable def ringColimit
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (a : F.obj j), (c.ι.app j).hom a = x) :
    IsColimit c := by
  classical
  have hcover := hsurj
  choose stage repr hrepr using hcover
  let f (s : Cocone F) (x : c.pt) : s.pt := (s.ι.app (stage x)).hom (repr x)
  have hf (s : Cocone F) (j : J) (a : F.obj j) :
      f s ((c.ι.app j).hom a) = (s.ι.app j).hom a :=
    cocone_eq_of_eq F c s hinj _ j _ a (hrepr _)
  let desc (s : Cocone F) := ringDesc F c s hsurj (f s) (hf s)
  have hdesc (s : Cocone F) (j : J) (a : F.obj j) :
      desc s ((c.ι.app j).hom a) = (s.ι.app j).hom a :=
    (ringDesc_apply F c s hsurj (f s) (hf s) _).trans (hf s j a)
  exact
    { desc := fun s ↦ CommRingCat.ofHom (desc s)
      fac := fun s j ↦ by ext a; exact hdesc s j a
      uniq := fun s m hm ↦ by
        ext x
        obtain ⟨j, a, rfl⟩ := hsurj x
        exact (ConcreteCategory.congr_hom (hm j) a).trans (hdesc s j a).symm }

@[irreducible]
private noncomputable def algColimit
    {J : Type w} [SmallCategory J] [Nonempty J]
    {K : Type v} [CommRing K] (D : J ⥤ CommAlgCat.{u} K) (c : Cocone D)
    (hc : IsColimit ((forget₂ (CommAlgCat.{u} K) CommRingCat).mapCocone c)) :
    IsColimit c := by
  classical
  let U := forget₂ (CommAlgCat.{u} K) CommRingCat
  let desc (s : Cocone D) : c.pt →ₐ[K] s.pt :=
    { __ := (hc.desc (U.mapCocone s)).hom
      commutes' := fun k ↦ by
        let j : J := Classical.arbitrary J
        have h := ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) j)
          (algebraMap K (D.obj j) k)
        change (hc.desc (U.mapCocone s)).hom
          ((c.ι.app j).hom (algebraMap K (D.obj j) k)) =
            (s.ι.app j).hom (algebraMap K (D.obj j) k) at h
        rw [AlgHom.commutes, AlgHom.commutes] at h
        exact h }
  exact
    { desc := fun s ↦ CommAlgCat.ofHom (desc s)
      fac := fun s j ↦ by
        ext a
        exact ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) j) a
      uniq := fun s m hm ↦ by
        apply (forget₂ (CommAlgCat.{u} K) CommRingCat).map_injective
        exact hc.uniq (U.mapCocone s) (U.map m) (fun j ↦ congrArg U.map (hm j)) }

/-- Source: Stacks Project, Tags 00CO, 002F, and 002V; blueprint node
`lem-kun-colim-of-localizations` (blueprint: lem-kun-colim-of-localizations).

Proof:
1. Send a fraction a/gⁿ in each principal localization to the same fraction in Frac(B).
   The localization relation implies equality in the field by cancellation in B. Conversely,
   equality in the field gives cross-multiplication in the subalgebra, proving injectivity.
2. For p ≤ q, invert the image of g in the q-stage and send a/gⁿ to a times this inverse
   to the nth power. The fraction relation proves well-definedness. A ring map extending
   the inclusion must send 1/g to this inverse, proving uniqueness. These maps preserve
   scalars and commute with the embeddings; their identities and compositions follow.
3. The relation is reflexive because g is a unit in its own localization. Transitivity
   follows by transporting inverses along transition maps. Choose (i,1) for nonemptiness.
   For (i,g) and (j,h), choose a stage containing both subalgebras and localize at gh.
   The domain condition gives gh ≠ 0, and h/(gh) and g/(gh) invert g and h. This supplies
   a common upper bound. In the associated thin category parallel arrows are equal.
4. Write any fraction as a/b with b ≠ 0. The union and directedness hypotheses put both
   a and b in one subalgebra, so this fraction comes from its localization at b.
   This includes zero by using a = 0 and b = 1.
5. Given a compatible cocone, evaluate a field element at any stage representing it.
   A common upper stage and the injective embeddings prove independence of the choice.
   Compute sums, products, zero, and one at a common stage to get a ring map. Coverage
   forces uniqueness. When the cocone maps preserve K-scalars, the same construction
   preserves them too, giving the K-algebra universal property.
-/
theorem colim_of_localizations
    {K : Type v} {B : Type u} [CommRing K] [CommRing B] [Algebra K B] [IsDomain B]
    {I : Type w} (Bi : I → Subalgebra K B)
    (hI : Nonempty I)
    (hfin : ∀ i : I, Algebra.FiniteType K (Bi i))
    (hcover : ∀ b : B, ∃ i : I, b ∈ Bi i)
    (hdirected : ∀ i j : I, ∃ k : I, Bi i ≤ Bi k ∧ Bi j ≤ Bi k) :
    ∃ (e : ∀ p : LocalizationPair Bi, PairLocalization Bi p →ₐ[K] FractionRing B)
      (t : ∀ (p q : LocalizationPair Bi),
        PairLocalizationLE Bi p q → PairLocalization Bi p →ₐ[K] PairLocalization Bi q),
      (∀ (p : LocalizationPair Bi), Function.Injective (e p)) ∧
      (∀ (p : LocalizationPair Bi) (x : Bi p.1.1),
        e p (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
          algebraMap B (FractionRing B) (x : B)) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q) (x : Bi p.1.1),
        t p q h (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
          algebraMap (Bi q.1.1) (PairLocalization Bi q) ⟨(x : B), (h.1 x.property)⟩) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q),
        ∀ f : PairLocalization Bi p →ₐ[K] PairLocalization Bi q,
          (∀ x : Bi p.1.1,
            f (algebraMap (Bi p.1.1) (PairLocalization Bi p) x) =
              algebraMap (Bi q.1.1) (PairLocalization Bi q) ⟨(x : B), (h.1 x.property)⟩) →
          f = t p q h) ∧
      (∀ (p q : LocalizationPair Bi) (h : PairLocalizationLE Bi p q),
        (e q).comp (t p q h) = e p) ∧
      (∀ x : FractionRing B,
        ∃ (p : LocalizationPair Bi) (y : PairLocalization Bi p), e p y = x) ∧
      ∃ (P : Preorder (LocalizationPair Bi))
        (D : @CategoryTheory.Functor (LocalizationPair Bi)
          (@Preorder.smallCategory (LocalizationPair Bi) P) (CommAlgCat.{u} K) inferInstance)
        (c : @Cocone _ _ _ _ D),
        (∀ p q : LocalizationPair Bi,
          @LE.le _ P.toLE p q ↔ PairLocalizationLE Bi p q) ∧
        @IsFiltered (LocalizationPair Bi)
          (@Preorder.smallCategory (LocalizationPair Bi) P) ∧
        (∀ p : LocalizationPair Bi, D.obj p = CommAlgCat.of K (PairLocalization Bi p)) ∧
        c.pt = CommAlgCat.of K (FractionRing B) ∧
        (∀ p : LocalizationPair Bi, HEq (c.ι.app p) (CommAlgCat.ofHom (e p))) ∧
        Nonempty (IsColimit c) ∧
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} K) CommRingCat).mapCocone c)) := by
  classical
  have _hfin := hfin
  let e := embedding Bi
  let t := transition Bi
  have he := embedding_base Bi
  have ht := transition_base Bi
  have hinj := embedding_injective Bi
  have hcompat := embedding_transition Bi
  have hsurj := embedding_cover Bi hcover hdirected
  refine ⟨e, t, hinj, he, ht, ?_, hcompat, hsurj, ?_⟩
  · intro p q h f hf
    apply localization_ext Bi p
    intro x
    exact (hf x).trans (ht p q h x).symm
  · let P : Preorder (LocalizationPair Bi) :=
      { le := PairLocalizationLE Bi
        le_refl := pair_refl Bi
        le_trans := pair_trans Bi }
    let := P
    let : Nonempty (LocalizationPair Bi) := by
      obtain ⟨i⟩ := hI
      exact ⟨⟨(i, 1), (Bi i).one_mem, one_ne_zero⟩⟩
    let : IsDirectedOrder (LocalizationPair Bi) :=
      ⟨pair_upper Bi hdirected⟩
    let D : LocalizationPair Bi ⥤ CommAlgCat.{u} K :=
      { obj := fun p ↦ CommAlgCat.of K (PairLocalization Bi p)
        map := fun {p q} f ↦ CommAlgCat.ofHom (t p q (leOfHom f))
        map_id := fun p ↦ by
          apply CommAlgCat.hom_ext
          apply localization_ext Bi p
          intro x
          exact ht p p (leOfHom (𝟙 p)) x
        map_comp := fun {p q r} f g ↦ by
          apply CommAlgCat.hom_ext
          apply localization_ext Bi p
          intro x
          change t p r (leOfHom (f ≫ g)) (algebraMap _ _ x) =
            t q r (leOfHom g) (t p q (leOfHom f) (algebraMap _ _ x))
          rw [ht, ht, ht]
          rfl }
    let c : Cocone D :=
      { pt := CommAlgCat.of K (FractionRing B)
        ι :=
          { app := fun p ↦ CommAlgCat.ofHom (e p)
            naturality := fun {p q} f ↦ by
              change CommAlgCat.ofHom ((e q).comp (t p q (leOfHom f))) = _
              rw [hcompat]
              rfl } }
    let U := forget₂ (CommAlgCat.{u} K) CommRingCat
    have hc : IsColimit (U.mapCocone c) :=
      ringColimit (D ⋙ U) (U.mapCocone c) hinj hsurj
    refine ⟨P, D, c, (fun _ _ ↦ Iff.rfl), inferInstance, (fun _ ↦ rfl), rfl,
      (fun _ ↦ HEq.rfl), ⟨algColimit D c hc⟩, ⟨hc⟩⟩

end RingTheory
