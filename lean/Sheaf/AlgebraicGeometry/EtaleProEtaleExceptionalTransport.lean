/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Exceptional adjunction transport from etale to pro-etale sheaves

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph; the explicit transport
argument of the DAG (blueprint: lem-sf-etale-proetale-exceptional-transport).

The domain below uses intrinsic constructible cohomology, rather than assuming etale
origin. All Tor predicates test every module sheaf on the respective site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The etale objects occurring in the transport statement: the intersection of the
recorded bounded constructibility and finite Tor predicates. Source: blueprint
main-20261015, sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportEtaleObjects (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : ObjectProperty (Etale.DerivedCategoryModule A T) :=
  Etale.DerivedCategory.isBoundedConstructible A T ⊓
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A T a b K

/-- The intrinsic pro-etale domain of transport: bounded cohomology, every cohomology
sheaf constructible on a global finite partition, and finite Tor amplitude against all
pro-etale module sheaves. Source: blueprint main-20261015,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportProEtaleObjects (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  fun K ↦ _root_.DerivedCategory.TStructure.t.bounded K ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b K

/-- The functor `K ↦ ν_X^* R(E(K))`, for a functorial etale origin `E` and the ordinary
etale right adjoint `R`. This is a composite of the specified functors, with no choice of
an ambient pro-etale adjoint. Source: blueprint main-20261015,
sk-prop-sf-rf-shriek-preservation, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportImage (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (R : Etale.DerivedCategoryModule A Y ⥤
      Etale.DerivedCategoryModule A X)
    (E : (exceptionalTransportProEtaleObjects A Y).FullSubcategory ⥤
      Etale.DerivedCategoryModule A Y) :=
  E ⋙ R ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

private theorem exceptionalTransportEtale_plus
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) (hK : exceptionalTransportEtaleObjects A T K) :
    _root_.DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, b, hab, h⟩ := hK.1.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ h i (Or.inl hi))⟩

private theorem exceptionalTransport_object_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] :
    exceptionalTransportProEtaleObjects A T =
      (exceptionalTransportEtaleObjects A T).map
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  have hc := exceptionalTransport_constructible_comparison A T
  funext K
  apply propext
  constructor
  · rintro ⟨hbd, hcs, a, b, hab, ht⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N K :=
      (congrFun hc K).mp ⟨hbd, hcs⟩
    obtain ⟨H, hH, ⟨e⟩⟩ := hbc
    have ht' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b (N.obj H) :=
      (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
    refine ⟨H, ⟨hH, a, b, hab, ?_⟩, ⟨e⟩⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b H).mp ht')
  · rintro ⟨H, ⟨hH, a, b, hab, ht⟩, ⟨e⟩⟩
    have hbc : (Etale.DerivedCategory.isBoundedConstructible A T).map N K :=
      ⟨H, hH, ⟨e⟩⟩
    obtain ⟨hbd, hcs⟩ := (congrFun hc K).mpr hbc
    refine ⟨hbd, hcs, a, b, hab, ?_⟩
    exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
      ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b H).mpr
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht))

private theorem exceptionalTransport_functorial_origins
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T] :
    ∃ E : (exceptionalTransportProEtaleObjects A T).FullSubcategory ⥤
        Etale.DerivedCategoryModule A T,
    ∃ _α : E ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ≅
        (exceptionalTransportProEtaleObjects A T).ι,
      ∀ K, exceptionalTransportEtaleObjects A T (E.obj K) := by
  classical
  let P := exceptionalTransportEtaleObjects A T
  let Q := exceptionalTransportProEtaleObjects A T
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  have h : Q = P.map N := exceptionalTransport_object_comparison A T
  let F := P.ι ⋙ N
  have hF (K : P.FullSubcategory) : Q (F.obj K) := by
    rw [h]
    exact ObjectProperty.prop_map_obj P N K.property
  let H := Q.lift F hF
  have hbij (K L : P.FullSubcategory) : Function.Bijective
      (fun v : K ⟶ L ↦ H.map v) := by
    constructor
    · intro v w hvw
      apply ObjectProperty.hom_ext
      exact (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
        (exceptionalTransportEtale_plus A T L.obj L.property)).1
          (congrArg (fun z ↦ z.hom) hvw)
    · intro v
      obtain ⟨w, hw⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
        (exceptionalTransportEtale_plus A T L.obj L.property)).2 v.hom
      exact ⟨ObjectProperty.homMk w, Q.hom_ext hw⟩
  have : H.Full := ⟨fun v ↦ (hbij _ _).surjective v⟩
  have : H.Faithful := ⟨fun hvw ↦ (hbij _ _).injective hvw⟩
  have : H.EssSurj := ⟨fun K ↦ by
    have hK : (P.map N) K.obj := (congrFun h K.obj).mp K.property
    obtain ⟨L, hL, ⟨e⟩⟩ := hK
    exact ⟨⟨L, hL⟩, ⟨Q.isoMk e⟩⟩⟩
  have : H.IsEquivalence := {}
  let e := H.asEquivalence
  refine ⟨e.inverse ⋙ P.ι, ?_, fun K ↦ (e.inverse.obj K).property⟩
  exact Functor.isoWhiskerRight e.counitIso Q.ι

/-- Exceptional adjunction transport for one fixed compactification, including functorial
etale origins and the transported ordinary counit. Naturality in `K` is expressed by the
functor `E`, its natural origin isomorphism, and the natural transformation `t`.
Bijectivity of `h ↦ G(h) ≫ t_K` expresses the Hom equivalence and its naturality in `M`.
Source: blueprint main-20261015, sk-prop-sf-rf-shriek-preservation, final restriction
paragraph; the six-step DAG transport argument
(blueprint: lem-sf-etale-proetale-exceptional-transport).

Proof:
1. Finite coefficients and finite-type schemes over a field are Noetherian. Apply
`sk-thm-pe-constructible-comparison` to obtain bounded constructible etale origins.
`lem-exc-comparison-tor-interval` reflects the given finite Tor interval to each origin.
2. The assumed preservation by `R` makes its value bounded constructible of finite Tor
amplitude. Exact comparison commutes with cohomology, and inverse image on each finite
constructible stratum preserves local trivializations with finite values. The forward
Tor-interval comparison tests all pro-etale module sheaves. A quasi-inverse to comparison
on constructible complexes supplies the functor `E`.
3. Compose the exact open-extension comparison
`lem-cbc-proetale-extension-zero-comparison` with the proper direct-image comparison
`sk-thm-pe-direct-image-comparison`. Bounded below injective resolutions identify these
with the unbounded compact-support composites restricted to D-plus, giving beta.
4. For bounded below `M`, comparison full faithfulness identifies Hom(GPM,K) with
Hom(FM,E(K)); the ordinary etale adjunction identifies this with Hom(M,R(E(K))).
Comparison full faithfulness on X identifies the latter with Hom(PM,PR(E(K))).
5. Full faithfulness lifts every map of origins uniquely. Identity and composition
therefore lift to identity and composition; two choices of origins give canonically
isomorphic functors. The Hom bijections respect these maps and isomorphisms.
6. Define t_K as beta inverse at R(E(K)), then comparison of the ordinary counit,
then the origin isomorphism. Counit naturality makes t natural. Lift h uniquely as P(u);
naturality of beta rewrites the Hom bijection as G(h) followed by t_K.
-/
theorem etale_proEtale_exceptional_transport
    (k : Type u) [Field k] (p l : ℕ) [CharP k p]
    (_hp : p.Prime) (_hl : l.Prime) (_hlp : l ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, (l ^ n : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IsSeparated (f ≫ s)] [LocallyOfFiniteType (f ≫ s)] [QuasiCompact (f ≫ s)]
    (c : Compactification f) [IsSeparated (c.g ≫ s)]
    [LocallyOfFiniteType (c.g ≫ s)] [QuasiCompact (c.g ≫ s)]
    (R : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (_hR : ∀ K, exceptionalTransportEtaleObjects A Y K →
      exceptionalTransportEtaleObjects A X (R.obj K)) :
    ∃ β : _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
      _root_.DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c,
    ∃ E : (exceptionalTransportProEtaleObjects A Y).FullSubcategory ⥤
        Etale.DerivedCategoryModule A Y,
    ∃ α : E ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
        (exceptionalTransportProEtaleObjects A Y).ι,
      (∀ K, exceptionalTransportEtaleObjects A Y (E.obj K)) ∧
      (∀ K, exceptionalTransportProEtaleObjects A X
        ((exceptionalTransportImage A R E).obj K)) ∧
      ∃ t : exceptionalTransportImage A R E ⋙
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⟶
          (exceptionalTransportProEtaleObjects A Y).ι,
        (∀ K, ∃ hRE : _root_.DerivedCategory.TStructure.t.plus (R.obj (E.obj K)),
          t.app K = β.inv.app ⟨R.obj (E.obj K), hRE⟩ ≫
            (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
              (adj.counit.app (E.obj K)) ≫ α.hom.app K) ∧
        ∀ (K : (exceptionalTransportProEtaleObjects A Y).FullSubcategory)
          (M : _root_.DerivedCategory.Plus
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
          Function.Bijective
            (fun h : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M.obj ⟶
                (exceptionalTransportImage A R E).obj K ↦
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map h ≫
                t.app K) := by
  classical
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType s
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (f ≫ s)
  let β := (rightDerivedLowerShriekOfCompactificationComparisonIso
    (ModuleCat.{u + 1} A) c).symm
  obtain ⟨E, α, hEY⟩ := exceptionalTransport_functorial_origins A Y
  have hEX (K) : exceptionalTransportProEtaleObjects A X
      ((exceptionalTransportImage A R E).obj K) := by
    change exceptionalTransportProEtaleObjects A X
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (R.obj (E.obj K)))
    rw [exceptionalTransport_object_comparison A X]
    exact ObjectProperty.prop_map_obj _ _ (_hR _ (hEY K))
  have hE (K) := exceptionalTransportEtale_plus A Y (E.obj K) (hEY K)
  have hRE (K) := exceptionalTransportEtale_plus A X (R.obj (E.obj K)) (_hR _ (hEY K))
  let P := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let Q := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let t : exceptionalTransportImage A R E ⋙ G ⟶
      (exceptionalTransportProEtaleObjects A Y).ι :=
    { app := fun K ↦ β.inv.app ⟨R.obj (E.obj K), hRE K⟩ ≫
        Q.map (adj.counit.app (E.obj K)) ≫ α.hom.app K
      naturality := by
        intro K L v
        have hb := β.inv.naturality
          (ObjectProperty.homMk (R.map (E.map v)) :
            (⟨R.obj (E.obj K), hRE K⟩ : _root_.DerivedCategory.Plus _) ⟶
              ⟨R.obj (E.obj L), hRE L⟩)
        have hc := congrArg Q.map (adj.counit.naturality (E.map v))
        change G.map (P.map (R.map (E.map v))) ≫
            β.inv.app ⟨R.obj (E.obj L), hRE L⟩ =
          β.inv.app ⟨R.obj (E.obj K), hRE K⟩ ≫
            Q.map (F.map (R.map (E.map v))) at hb
        have hc' : Q.map (F.map (R.map (E.map v))) ≫
            Q.map (adj.counit.app (E.obj L)) =
          Q.map (adj.counit.app (E.obj K)) ≫ Q.map (E.map v) := by
          simpa only [F, Functor.map_comp, Functor.comp_map, Functor.id_map] using hc
        change G.map (P.map (R.map (E.map v))) ≫ _ = _
        have ha : Q.map (E.map v) ≫ α.hom.app L = α.hom.app K ≫ v.hom :=
          α.hom.naturality v
        rw [← Category.assoc, ← Category.assoc, hb, Category.assoc,
          Category.assoc, ← Category.assoc (Q.map _), hc', Category.assoc,
          Category.assoc, ha]
        simp only [Category.assoc, ObjectProperty.ι_map] }
  refine ⟨β, E, α, hEY, hEX, t, ?_, ?_⟩
  · intro K
    exact ⟨hRE K, rfl⟩
  · intro K M
    let eP : (M.obj ⟶ R.obj (E.obj K)) ≃
        (P.obj M.obj ⟶ P.obj (R.obj (E.obj K))) :=
      Equiv.ofBijective _
        (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (hRE K))
    let eQ : (F.obj M.obj ⟶ E.obj K) ≃
        (Q.obj (F.obj M.obj) ⟶ Q.obj (E.obj K)) :=
      Equiv.ofBijective _
        (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (hE K))
    let e : (P.obj M.obj ⟶ P.obj (R.obj (E.obj K))) ≃
        (G.obj (P.obj M.obj) ⟶ K.obj) :=
      eP.symm.trans ((adj.homEquiv M.obj (E.obj K)).symm.trans
        (eQ.trans (((β.app M).homFromEquiv).trans
          ((α.app K).homToEquiv))))
    have he (h : P.obj M.obj ⟶ P.obj (R.obj (E.obj K))) :
        e h = G.map h ≫ t.app K := by
      obtain ⟨u, rfl⟩ := eP.surjective h
      have hb := β.inv.naturality
        (ObjectProperty.homMk u : M ⟶ ⟨R.obj (E.obj K), hRE K⟩)
      change G.map (P.map u) ≫ β.inv.app ⟨R.obj (E.obj K), hRE K⟩ =
        β.inv.app M ≫ Q.map (F.map u) at hb
      simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
      dsimp [eQ, eP, Iso.homFromEquiv, Iso.homToEquiv, Equiv.ofBijective, Equiv.coe_fn_mk]
      change (β.inv.app M ≫ Q.map ((adj.homEquiv _ _).symm u)) ≫ α.hom.app K = _
      rw [Adjunction.homEquiv_counit, Functor.map_comp]
      simpa only [Category.assoc, t, F] using congrArg
        (fun z ↦ z ≫ Q.map (adj.counit.app (E.obj K)) ≫ α.hom.app K) hb.symm
    change Function.Bijective (fun h ↦ G.map h ≫ t.app K)
    have heq : (fun h ↦ G.map h ≫ t.app K) = e := funext (fun h ↦ (he h).symm)
    rw [heq]
    exact e.bijective

end AlgebraicGeometry.ProEtale
