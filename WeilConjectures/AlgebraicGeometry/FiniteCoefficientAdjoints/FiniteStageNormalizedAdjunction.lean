/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor

/-! # Normalized adjunction at one finite coefficient stage

Source: current blueprint reduction-exceptional, Locality and Charts, with the
ordinary closed-chart preservation argument in the parent node, proof steps 1--4.
(blueprint: lem-pur-finite-stage-normalized-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

section Construction

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [IsNoetherian X] [IsNoetherian Y]
  (c : Compactification f)

private theorem rnu_ctf (T : Scheme.{u}) (K : D A T) (hK : ctf A T K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((rnu A T).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK.1
  have hLt : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T L := by
    obtain ⟨a, b, ht⟩ :=
      (ctf A T).prop_of_iso e.symm hK |>.2
    exact ⟨a, b, (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      a b L).mp ht⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) T L hL.1.1
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso
    (asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L) ≪≫
      (rnu A T).mapIso e) ⟨hL, hLt⟩

private theorem etale_preserves
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent A Y]
    [QuasiCompact f] (K : Etale.DerivedCategoryModule A Y)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y K) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
      ((etaleUpper A c).obj K) := by
  let : HasCompactification f := c.hasCompactification
  let adj := (Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso A c).symm
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
    (((etaleAdjunction A c).rightAdjointUniq adj).app K).symm
    (Etale.constructibleFiniteTor_rightDerivedUpperShriek A aY f hK)

private theorem upper_preserves
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent A Y]
    [QuasiCompact f] (K : D A Y) (hK : ctf A Y K) :
    ctf A X ((upper A c).obj K) := by
  exact ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
    (etale_preserves A c k aY _ (rnu_ctf A Y K hK))

variable
  (hL : ∀ K, ctf A X K → ctf A Y ((lower A c).obj K))
  (hR : ∀ K, ctf A Y K → ctf A X ((upper A c).obj K))
  (hb : ∀ K, ctf A Y K → DerivedCategory.TStructure.t.plus
    ((etaleUpper A c).obj ((rnu A Y).obj K)))

private def normalizedCounit (K : (ctf A Y).FullSubcategory) :
    (lower A c).obj ((upper A c).obj K.obj) ⟶ K.obj :=
  (ProEtale.compactSupportSiteComparison A c).hom.app
      ⟨(etaleUpper A c).obj ((rnu A Y).obj K.obj), hb K.obj K.property⟩ ≫
    (nu A Y).map ((etaleAdjunction A c).counit.app ((rnu A Y).obj K.obj)) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K.obj

private theorem normalizedCounit_naturality
    {K K' : (ctf A Y).FullSubcategory} (v : K ⟶ K') :
    (lower A c).map ((upper A c).map v.hom) ≫ normalizedCounit A c hb K' =
      normalizedCounit A c hb K ≫ v.hom := by
  have h := (ProEtale.compactSupportSiteComparison A c).hom.naturality
    (X := ⟨_, hb K.obj K.property⟩) (Y := ⟨_, hb K'.obj K'.property⟩)
    (ObjectProperty.homMk ((etaleUpper A c).map ((rnu A Y).map v.hom)))
  dsimp at h
  dsimp only [normalizedCounit, upper, Functor.comp_map]
  rw [reassoc_of% h, ← Functor.map_comp_assoc]
  erw [(etaleAdjunction A c).counit_naturality ((rnu A Y).map v.hom)]
  rw [Functor.map_comp_assoc]
  erw [(ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit_naturality]
  simp only [Category.assoc]

private theorem normalizedCounit_bijective
    (M : (ctf A X).FullSubcategory) (K : (ctf A Y).FullSubcategory) :
    Function.Bijective (fun g : M.obj ⟶ (upper A c).obj K.obj ↦
      (lower A c).map g ≫ normalizedCounit A c hb K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := M.property.1
  let F := lower A c
  let N := nu A X
  let eps := normalizedCounit A c hb K
  have hi : Function.Bijective (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) := by
    let E := (((etaleAdjunction A c).homEquiv L _).symm.trans
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj).symm).trans
        (((ProEtale.compactSupportSiteComparison A c).app
          ⟨L, hL.1.1⟩).symm.homFromEquiv (Z := K.obj))
    have he : (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) ∘
        (fun g ↦ N.map g) = ⇑E := by
      funext g
      have hn := (ProEtale.compactSupportSiteComparison A c).hom.naturality
        (X := ⟨L, hL.1.1⟩) (Y := ⟨_, hb K.obj K.property⟩)
        (ObjectProperty.homMk g)
      dsimp at hn
      change F.map (N.map g) ≫ eps =
        ((ProEtale.compactSupportSiteComparison A c).app ⟨L, hL.1.1⟩).hom ≫
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv
            _ K.obj).symm (((etaleAdjunction A c).homEquiv L _).symm g)
      simp only [Adjunction.homEquiv_counit, normalizedCounit, eps, Functor.map_comp,
        Category.assoc, Iso.app_hom]
      erw [reassoc_of% hn]
      rfl
    apply (Function.Bijective.of_comp_iff _
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map L _
        (hb K.obj K.property))).1
    rw [he]
    exact E.bijective
  have he : (fun g : M.obj ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) =
      ⇑(F.mapIso e).homFromEquiv ∘
        (fun g : N.obj L ⟶ (upper A c).obj K.obj ↦ F.map g ≫ eps) ∘
          ⇑e.symm.homFromEquiv := by
    funext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [he]
  exact (F.mapIso e).homFromEquiv.bijective.comp (hi.comp e.symm.homFromEquiv.bijective)

private def normalizedAdjunction : restrict (lower A c) hL ⊣ restrict (upper A c) hR := by
  let e (M : (ctf A X).FullSubcategory) (K : (ctf A Y).FullSubcategory) :
      (M ⟶ (restrict (upper A c) hR).obj K) ≃
        ((restrict (lower A c) hL).obj M ⟶ K) :=
    ((ObjectProperty.fullyFaithfulι (ctf A X)).homEquiv
      (X := M) (Y := (restrict (upper A c) hR).obj K)).trans
      ((Equiv.ofBijective _ (normalizedCounit_bijective A c hb M K)).trans
        ((ObjectProperty.fullyFaithfulι (ctf A Y)).homEquiv
          (X := (restrict (lower A c) hL).obj M) (Y := K)).symm)
  exact Adjunction.mkOfHomEquiv
    { homEquiv := fun M K ↦ (e M K).symm
      homEquiv_naturality_left_symm := by
        intro M' M K v g
        apply ObjectProperty.hom_ext
        change (lower A c).map (v.hom ≫ g.hom) ≫ normalizedCounit A c hb K =
          (lower A c).map v.hom ≫
            ((lower A c).map g.hom ≫ normalizedCounit A c hb K)
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro M K K' v g
        apply (e M K').injective
        rw [(e M K').apply_symm_apply]
        apply ObjectProperty.hom_ext
        change _ = (lower A c).map
          (((e M K).symm v).hom ≫ (upper A c).map g.hom) ≫ normalizedCounit A c hb K'
        rw [Functor.map_comp, Category.assoc, normalizedCounit_naturality A c hb g]
        have he := congrArg (fun t ↦ t.hom) ((e M K).apply_symm_apply v)
        change (lower A c).map ((e M K).symm v).hom ≫ normalizedCounit A c hb K = v.hom at he
        rw [← Category.assoc, he]
        rfl }

private theorem normalizedAdjunction_counit (K : (ctf A Y).FullSubcategory) :
    ((normalizedAdjunction A c hL hR hb).counit.app K).hom =
      normalizedCounit A c hb K := by
  change (lower A c).map (𝟙 ((upper A c).obj K.obj)) ≫ normalizedCounit A c hb K = _
  rw [(lower A c).map_id, Category.id_comp]

private theorem datum_unique (d e : AdjointDatum A c) : d = e := by
  obtain ⟨hl, hr, a, hb, hc⟩ := d
  obtain ⟨hl', hr', a', hb', hc'⟩ := e
  have ha : a = a' := by
    apply Adjunction.ext_counit
    ext K
    exact (hc K).trans (hc' K).symm
  cases ha
  rfl

/-- A single compactification and coefficient stage have a unique adjunction with the
specified transported geometric counit.

Source: current blueprint reduction-exceptional, Locality and Charts; parent
lem-pur-finite-coefficient-adjoint-comparisons, proof steps 1--4.
(blueprint: lem-pur-finite-stage-normalized-adjunction).

Proof: stage finiteness is already proved in the data module. Ramification identifies
its defining ideal with an upper-uniformizer power. The DVR valuation criterion
makes a power of l vanish in this quotient, while l is invertible over k, giving
the exponent hypothesis for the native etale preservation theorems. Apply those
theorems to the specified compactification; uniqueness of right adjoints identifies
its chosen etale right adjoint with the global etale exceptional inverse image.
For an etale-origin object K, reflect its Tor interval to an antecedent L and use
the derived comparison unit to identify L with Rnu_* K. This proves preservation
by the fixed upper functor and its etaleBound. The specified compact-support
comparison is used in the Hom construction. The native pro-etale theorem supplies
preservation by the lower functor directly.
Define the counit as exactly the specified threefold composite. Naturality follows
from that of its constituents. For a source nu L, composing the two adjunction Hom
bijections with the compact-support comparison gives the map lower(g) followed by
this counit. Full faithfulness of nu on the bounded-below upper value makes this a
bijection; transport along an origin isomorphism treats every finite-Tor source.
Restrict it to the full subcategories and construct the adjunction. Evaluating its
inverse Hom map on the identity computes its counit. Finally normalization fixes
all counit components, so Adjunction.ext_counit and proof irrelevance prove
uniqueness of the entire datum. No nonemptiness or perfection assumption is used. -/
theorem finite_stage_normalized_adjunction
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (s : Stage l E) (c : Compactification f) :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∃! d : AdjointDatum s.ring c, True := by
  classical
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  obtain ⟨e, z, hz, hideal, _⟩ := stage_ramification s
  let n : ℕ := (e : ℕ) * (s.exponent : ℕ)
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have hlmem : (l : s.integers) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) := by
    have hgen : Ideal.span
        ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) =
        Padic.coefficientExtensionMaximalIdeal l s.field :=
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    rw [hgen]
    apply (hF.2.1 _).mpr
    change spectralNorm (Padic l) s.field (l : s.field) < 1
    rw [← map_natCast (algebraMap (Padic l) s.field) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hzero : (l : s.ring) ^ n = 0 := by
    have hm : (l : s.integers) ^ n ∈ s.ideal := by
      change _ ∈ Ideal.span ({s.parameter} : Set s.integers) ^ (s.exponent : ℕ)
      rw [hideal]
      exact Ideal.pow_mem_pow hlmem n
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_pow, map_natCast] using hq
  have hnonzero : (l : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) hlp.symm
  let : HasInvertibleExponent s.ring (Spec (.of k)) :=
    ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, by simpa using hzero, by
      have hu : IsUnit ((l ^ n : ℕ) : k) := by
        rw [Nat.cast_pow]
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hnonzero)
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  let : HasInvertibleExponent s.ring Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  let hL : ∀ K, ctf s.ring X K → ctf s.ring Y ((lower s.ring c).obj K) :=
    fun _ hK ↦ ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification
      s.ring (Y ↘ Spec (.of k)) c hK
  let hR := upper_preserves s.ring c k (Y ↘ Spec (.of k))
  have hb : ∀ K, ctf s.ring Y K → DerivedCategory.TStructure.t.plus
      ((etaleUpper s.ring c).obj ((rnu s.ring Y).obj K)) := by
    intro K hK
    exact (etale_preserves s.ring c k (Y ↘ Spec (.of k)) _
      (rnu_ctf s.ring Y K hK)).1.1.1
  let d : AdjointDatum s.ring c :=
    { lower_preserves := hL
      upper_preserves := hR
      adjunction := normalizedAdjunction s.ring c hL hR hb
      etaleBound := hb
      counit_normalization := normalizedAdjunction_counit s.ring c hL hR hb }
  exact ⟨d, trivial, fun d' _ ↦ datum_unique s.ring c d' d⟩

end Construction

set_option linter.unusedVariables false in
end AlgebraicGeometry.FiniteCoefficientAdjoints
