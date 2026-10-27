/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.PointSystemPowerRoosData
import Sheaf.Paper.PointPowerStrictInsertionSpecialization
import Sheaf.Paper.PointPowerRoosComparisonSpecialization

/-! Specialization of the point-power composition argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.roosF
attribute [local irreducible] WeilConjectures.PointSystemTransport.pull
  WeilConjectures.PointSystemTransport.sections

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSystemTransport.PowerRoos
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem insertion_model (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    (I D l E hl r hr).app (DerivedCategory.Q.obj M) ≫
        (sections D l E).mapDerivedCategory.map
          ((pull D l E r).mapDerivedCategoryFactors.hom.app M) ≫
        (sections D l E).mapDerivedCategoryFactors.hom.app ((Gc D l E r).obj M) =
      (sections D l E).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((u D l E hl r hr).app M) := by
  let e := Functor.mapHomologicalComplexCompIso
    (Iso.refl (pull D l E r ⋙ sections D l E)) (.up ℤ)
  apply (cancel_mono (DerivedCategory.Q.map (e.hom.app M))).1
  have hc := Functor.mapDerivedCategoryCompIso_fac (pull D l E r) (sections D l E) M
  have hn := ((point_system_transport_descent D l E hl r hr).2.exists.choose_spec).1 M
  change (derivedTransport D l E hl r hr).app (DerivedCategory.Q.obj M) ≫
      (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M = _ at hn
  dsimp only [I, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hc, hn]
  dsimp only [u, NatTrans.comp_app]
  change _ = _ ≫ DerivedCategory.Q.map
    ((chainTransport D l E hl r hr).app M ≫ e.inv.app M) ≫
      DerivedCategory.Q.map (e.hom.app M)
  rw [← DerivedCategory.Q.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

attribute [local irreducible] I u

set_option maxHeartbeats 800000 in
-- Normalization rewrites carry the full strict coefficient-system categories.
/-- The derived point insertion identity follows from the strict chain identity.
Source: blueprint trace-transport, Step 1, Global powers; Stacks 015F, 03CB.
(blueprint: lem-trf-point-power-derived-transport-coherence).

Proof: represent every derived system object by a strict complex through the recorded
localization factors. The normalization equation for `derivedTransport` identifies each
representative with the corresponding `chainTransport`. Substitute the strict identity,
then use naturality of the derived factorization maps and the defining equation for the
map of the derived compositor. Equality of the resulting localized arrows follows from
full faithfulness of precomposition with the localization functor. This argument retains
all tower transitions and applies to arbitrary unbounded derived objects. -/
theorem derived_transport_coherence_from_strict (hl : l ≠ D.p) (P : Compositors D l E)
    (m : ℕ) (hm : 1 ≤ m) (hs : StrictTransportCoherence D l E hl P m hm) :
    DerivedTransportCoherence D l E hl P m hm := by
  suffices h : I D l E hl (m + 1) (Nat.le_trans hm (Nat.le_succ m)) =
      I D l E hl m hm ≫
        Functor.whiskerLeft (pull D l E m).mapDerivedCategory
          (I D l E hl 1 (Nat.le_refl 1)) ≫
        Functor.whiskerRight (td D l E P m).hom (derivedSections D l E) from
    fun C ↦ congr_app h C
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E (Spec (.of D.k))) (.up ℤ))
  intro M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let e := (sections D l E).mapDerivedCategory.mapIso
      ((pull D l E (m + 1)).mapDerivedCategoryFactors.app M) ≪≫
    (sections D l E).mapDerivedCategoryFactors.app ((Gc D l E (m + 1)).obj M)
  apply (cancel_mono e.hom).1
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Iso.app_hom]
  simp only [Category.assoc]
  rw [insertion_model]
  have ht := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (P.t m) M
  have he : Functor.mapHomologicalComplexCompIsoHomOfIso (P.t m) M =
      (tc D l E P m).hom.app M := by
    ext p
    simp [Functor.mapHomologicalComplexCompIsoHomOfIso]
  rw [he] at ht
  have hn := (I D l E hl 1 (Nat.le_refl 1)).naturality
    ((pull D l E m).mapDerivedCategoryFactors.hom.app M)
  dsimp only [Functor.comp_map] at hn
  have hf := (sections D l E).mapDerivedCategoryFactors.hom.naturality
    ((tc D l E P m).hom.app M)
  dsimp only [Functor.comp_map] at hf
  change _ = _ ≫ _ ≫ (sections D l E).mapDerivedCategory.map
    ((td D l E P m).hom.app (DerivedCategory.Q.obj M)) ≫ _
  rw [← (sections D l E).mapDerivedCategory.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [hf]
  erw [← reassoc_of% hn]
  erw [reassoc_of% (insertion_model D l E hl 1 (Nat.le_refl 1) ((Gc D l E m).obj M))]
  erw [reassoc_of% (insertion_model D l E hl m hm M)]
  simp only [← DerivedCategory.Q.map_comp]
  rw [hs M]

/-- Point insertion composes on strict system complexes and their ordinary derived
category. The normalized inverse-image/product comparison has the same compositor
on the product, on both signed cone coordinates, and on the entire derived object.

Source: blueprint main-20261015, trace-transport proof, Step 1, Global powers;
`prop-trf-rational-frobenius-integral-model`, proof (3); Stacks 03CB, 0H7J, 0941
(blueprint: lem-trf-point-system-power-roos-coherence).

Proof, following the seven steps of the node:
1. Apply lem-trf-constant-coefficient-composition to the two point powers and A_n.
The finite coefficient comparisons commute with reduction by the isomorphism inverse-image
lemma. Project the completed coefficient equation to every finite level; the limit
universal property proves it. Thus d, t and b respect the actual scalar actions.
2. Apply lem-trf-point-sheaf-insertion-calculus to every finite module in every degree.
Two restrictions compose by presheaf functoriality. The inverse of the canonical
pullback-composition map multiplies the two inserted tensor units. This gives HasTensorUnits
and the equality of section maps, read through the recorded finite j comparisons.
3. The transition squares and differential squares are those of point-system transport
descent. Naturality of the compositor and equality of all strict components give the
first displayed chain-map equality. Localize this equality, using the representative
normalization of derivedTransport and functoriality of localization, to get the second.
4. Exact countable products, exact inverse image and its product preservation allow
lem-cbc-exact-product-functor-strict-limit on the full completed-module category.
Its normalized comparison, together with lem-weil-strict-roos-comparison, supplies N,
psi, kappa and a with the displayed representative normalization, without constructibility.
5. Compose the two candidate product maps with the nth product projection. The defining
projection equations and naturality of d give the same twice-reindexed projection.
Product uniqueness proves the third equality, before any derived localization.
6. Naturality of t with the original transitions makes its product map commute with
shift and hence with 1-shift. In the signed coordinates the differential is
D(x,y)=(dx,(1-shift)x-dy). Apply step 5 to each coordinate: the diagonal entries agree
and both off-diagonal entries vanish. This proves the fourth, whole-cone equality.
7. Substitute HasDerivedModel into the two sides of the last equality. Naturality of theta
moves it through t and d; the two middle inverse theta factors cancel. Step 6 makes
what remains identical. The natural transformations descend through localization,
so the result holds naturally for every derived system object and morphism. No
faithfulness of derived evaluation or constructibility of the realized object is used. -/
theorem point_system_power_roos_coherence (hl : l ≠ D.p) :
    ∃ (P : Compositors D l E) (N : RoosNormalization D l E) (A : Comparisons D l E),
      HasSiteSections D l E P ∧ HasSystemSections D l E P ∧
      HasRestrictionSections D l E P ∧ HasTensorUnits D l E P ∧
      HasProducts D l E P A ∧ HasFirstCoordinate D l E A ∧
      HasSecondCoordinate D l E A ∧ HasDerivedModel D l E N A ∧
      ∀ (m : ℕ) (hm : 1 ≤ m),
      StrictTransportCoherence D l E hl P m hm ∧
      DerivedTransportCoherence D l E hl P m hm ∧
      ProductCoherence D l E P A m ∧ ConeCoherence D l E P A m ∧
      DerivedComparisonCoherence D l E P A m := by
  obtain ⟨P, hd, ht, hb, hj, hu⟩ := point_power_strict_insertion_specialization D l E hl
  obtain ⟨N, A, hp, hx, hy, ha, hc⟩ :=
    point_power_roos_comparison_specialization D l E P hd ht hb
  refine ⟨P, N, A, hd, ht, hb, hj, hp, hx, hy, ha, ?_⟩
  intro m hm
  exact ⟨hu m hm, derived_transport_coherence_from_strict D l E hl P m hm (hu m hm), hc m⟩

end WeilConjectures.PointSystemTransport.PowerRoos
