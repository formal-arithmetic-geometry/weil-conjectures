/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.CoefficientTowerGeometricCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientTowerEtaleCalculus
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin

/-! # Geometric composition and etale comparison

Source: blueprint Local pairs and Levels, coefficient tower shriek calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finite_normalization_exists_aux
    (k : Type u) [Field k]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) :
    Nonempty (FiniteNormalization l E k b o q z) := by
  classical
  have eval {S T : Scheme.{u}} {f : S ⟶ T} (c : Compactification f) (n : ℕ) :
      SpTowerCalculus.Evaluation l E b o q c n := by
    letI := (q.abelian S).hasDerived
    letI := (q.abelian T).hasDerived
    refine ⟨(Functor.isoWhiskerLeft _ (SpTowerCalculus.levelComparison l E b q T n).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          ((SpTowerCalculus.realization l E b S (q.abelian S)).functor ⋙
            SpTowerShriek.F l E b o c)
          (SpTowerCalculus.realization l E b T (q.abelian T)).counitIso ≪≫
            Functor.rightUnitor _) (SpTowerShriek.Ev l E T n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (SpTowerCalculus.levelComparison l E b q S n) _, ?_⟩
    intro M
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Category.id_comp]
    erw [Category.comp_id]
  exact ⟨
    { evaluation := eval
      finite_origin := by
        intro T _ _ _ _ K n
        let A := SpTowerShriek.R l E n
        let R := sfIntrinsicDerivedEquivalence T A
        let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        obtain ⟨J, ⟨eJ⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1 _).mpr
          ⟨(K.property.1 n).2.1, (K.property.1 n).1⟩
        let ec : R.functor.obj (ν.mapDerivedCategory.obj J.obj) ≅
            (spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K.obj :=
          ((Functor.mapDerivedCategoryCompIso ν
            (ProEtale.finiteCoefficientIntrinsicRealization T A)).app J.obj).symm ≪≫ eJ
        let e : ν.mapDerivedCategory.obj J.obj ≅ R.inverse.obj
            ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K.obj) :=
          R.unitIso.app _ ≪≫ R.inverse.mapIso ec
        obtain ⟨a, c, _, hz⟩ := J.property.2
        exact ⟨J.obj, ⟨a, (DerivedCategory.isGE_iff J.obj a).mpr
          (fun i hi ↦ hz i (.inl hi))⟩, ⟨e⟩⟩ }⟩

/-- Proper/open composition and exact etale sum-extension, normalized together.
Source: Stacks 0F7J and 03DI--03DJ, 03S5; blueprint Local pairs, steps 1--6.
Proof: build the finite evaluation isomorphisms by whiskering the target level
comparison, the realization counit, Fcomparison and the source level comparison;
expanding the composite gives the prescribed normalization word. For each finite
level of K in C the finite-ring constructible-derived origin theorem gives a bounded
etale origin, transported back through the intrinsic realization equivalence; its
lower bound gives the plus origin. This is finiteData, chosen before preservation.
The geometric coherent-operations theorem then gives the compositor and an open
comparison family v, with coherence and the open normalization for every h. For a
given h the independent etale-calculus theorem gives et0; replace its comparison for
an open immersion j by v followed by the inverse of the unique open adjunction
comparison, and keep all other fields. The displayed equation is the open
normalization of the geometric theorem after cancelling that inverse.
This construction does not assert coefficient-reduction compatibility.
(blueprint: lem-route-geometric-calculus). -/
theorem geometric_calculus
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E) :
    ∃ finiteData : FiniteNormalization l E k b o q z,
    ∃ ops : CompositionOperations l E k b o q z,
    ∀ h : Preservation l E k b o q,
    ∃ et : EtaleCalculus l E k b o q z,
      Nonempty (CompositionCoherence l E k b o q z h finiteData ops) ∧
      (∀ {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a : Compactification j) (c : Compactification f) (K : C l E b q U),
    (ops.composition j f (j ≫ f) rfl a c (c.precomp j)).hom.app K =
      (F l E b o q c).map
        ((et.etale_shriek j a).hom.app K ≫
          (openEtaleCoordinates l E b o q z j (et.etale j)).hom.app K.obj) ≫
        (openComposition l E b o q j c).hom.app K.obj) := by
  classical
  obtain ⟨finiteData⟩ := finite_normalization_exists_aux l E k b o q z
  obtain ⟨ops, v, hc⟩ :=
    geometric_coherent_operations l E pchar hp hne k b o x laws q z finiteData
  refine ⟨finiteData, ops, fun h ↦ ?_⟩
  obtain ⟨et₀⟩ := etale_calculus_exists l E pchar hp hne k b o x laws q z h
  let et : EtaleCalculus l E k b o q z :=
    { et₀ with
      etale_shriek := fun {U T} _ _ _ _ _ _ _ _ e _ _ _ _ _ c ↦ by
        by_cases he : IsOpenImmersion e
        · letI := he
          exact v e c ≪≫ Functor.isoWhiskerLeft (inclusion l E b q U)
            (openEtaleCoordinates l E b o q z e (et₀.etale e)).symm
        · exact et₀.etale_shriek e c }
  refine ⟨et, (hc h).1, ?_⟩
  intro U X Y _ _ _ _ _ _ _ _ _ _ _ _ j _ _ _ f _ _ _ _ a c K
  rw [(hc h).2 j f a c K]
  congr 2
  simp only [et, dif_pos (inferInstance : IsOpenImmersion j),
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  change (v j a).hom.app K = (v j a).hom.app K ≫
    (openEtaleCoordinates l E b o q z j (et₀.etale j)).inv.app K.obj ≫
      (openEtaleCoordinates l E b o q z j (et₀.etale j)).hom.app K.obj
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]


end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
