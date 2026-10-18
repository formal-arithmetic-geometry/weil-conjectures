module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Agreement with bounded derived global sections

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-rgamma-unbounded-bounded.md (blueprint: lem-kun-rgamma-unbounded-bounded).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem exists_Q_map_of_kInjective
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {C I : CochainComplex A ℤ} [I.IsKInjective]
    (f : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj I) :
    ∃ u : C ⟶ I, DerivedCategory.Q.map u = f := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj C) I).2
    (e.hom.app C ≫ f ≫ e.inv.app I)
  refine ⟨g.out, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (K := C) (L := I) g.out
  rw [HomotopyCategory.quotient_map_out, hg] at h
  apply (cancel_epi (e.hom.app C)).1
  simpa only [e, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h.symm

private theorem homotopy_of_Q_map_eq
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {C I : CochainComplex A ℤ} [I.IsKInjective] (f g : C ⟶ I)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj C) I).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app I)).1
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

private theorem Q_map_sections_eq_of_homotopy
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    {C I : CochainComplex A ℤ} {f g : C ⟶ I} (h : Homotopy f g) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) :=
  DerivedCategory.Q_map_eq_of_homotopy B (F.mapHomotopy h)

-- The nested `eC'` binder belongs to the unchanged statement, but is not used in its result.
set_option linter.unusedVariables false in
/-- Agreement of bounded-below and unbounded derived global sections, including the
augmentation-compatible comparison, its uniqueness up to homotopy and its naturality.
Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-rgamma-unbounded-bounded; Stacks Project, Tags 079P and 070I
(blueprint: lem-kun-rgamma-unbounded-bounded).

Proof: choose the two K-injective resolutions using
`prop-weil-pbc-kinjective-resolutions-exist`. Their augmentations become invertible under
localization. Apply `lem-weil-pbc-kinjective-hom-derived` with target `J` to lift
`Q(b) ∘ Q(a)⁻¹` uniquely to a homotopy class `u`. The same argument with target `I`
lifts the inverse; injectivity implies the two inverse homotopy equations and `a ≫ u ~ b`.
Global sections is additive and preserves the homotopy equations termwise, so its image
of `u` is invertible in `D(Λ)`. The K-injective computation of derived global sections
identifies the source and target with the two recipes. A second compatible comparison
has the same image under localization, hence is homotopic and has the same image after
sections. For any derived morphism `f`, lift its conjugates by the augmentations into
`I'` and `J'`. The two composites into `J'` have equal localizations; injectivity makes
them homotopic, proving the displayed naturality square after sections and localization.
Identity and composition of the lifts follow by the same injectivity argument. -/
theorem rGamma_unbounded_bounded (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (C I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ DerivedCategory.Plus.ι.obj K)
    (a : C ⟶ I) (b : C ⟶ J)
    (ha : CochainComplex.IsKInjectiveResolution T Λ a)
    (hb : CochainComplex.IsKInjectiveResolution T Λ b) :
    ∃ u : I ⟶ J,
      Nonempty (Homotopy (a ≫ u) b) ∧
      (∀ u' : I ⟶ J, Nonempty (Homotopy (a ≫ u') b) → Nonempty (Homotopy u u')) ∧
      IsIso (DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u)) ∧
      (∃ eI :
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
          (DerivedCategory.Plus.ι.obj K) ≅ DerivedCategory.Q.obj
          (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I),
        ∃ eJ :
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
            (DerivedCategory.Plus.ι.obj K) ≅ DerivedCategory.Q.obj
          (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J),
          eI.hom ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) = eJ.hom) ∧
      (∀ (C' I' J' : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
        (K' : DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (eC' : DerivedCategory.Q.obj C' ≅ DerivedCategory.Plus.ι.obj K')
        (a' : C' ⟶ I') (b' : C' ⟶ J'),
        CochainComplex.IsKInjectiveResolution T Λ a' →
        CochainComplex.IsKInjectiveResolution T Λ b' →
        ∀ (u' : I' ⟶ J'), Nonempty (Homotopy (a' ≫ u') b') →
        ∀ f : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj C',
          (∃ p : I ⟶ I',
            DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p =
              f ≫ DerivedCategory.Q.map a') ∧
          (∃ q : J ⟶ J',
            DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q =
              f ≫ DerivedCategory.Q.map b') ∧
          (∀ (p : I ⟶ I') (q : J ⟶ J'),
            DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p =
              f ≫ DerivedCategory.Q.map a' →
            DerivedCategory.Q.map b ≫ DerivedCategory.Q.map q =
              f ≫ DerivedCategory.Q.map b' →
            DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u) ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map q) = DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p) ≫ DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map u'))) := by
  classical
  let A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let F := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let G := F.mapHomologicalComplex (.up ℤ)
  let Q := DerivedCategory.Q (C := A)
  let QΛ := DerivedCategory.Q (C := ModuleCat.{u + 1} Λ)
  have : QuasiIso a := ha.1
  have : QuasiIso b := hb.1
  have : I.IsKInjective := ha.2
  have : J.IsKInjective := hb.2
  obtain ⟨u, hu⟩ := exists_Q_map_of_kInjective (inv (Q.map a) ≫ Q.map b)
  have hau : Q.map a ≫ Q.map u = Q.map b := by
    rw [hu, IsIso.hom_inv_id_assoc]
  have hab : Nonempty (Homotopy (a ≫ u) b) :=
    homotopy_of_Q_map_eq _ _ (by simpa only [Functor.map_comp] using hau)
  have unique (u' : I ⟶ J) (h : Nonempty (Homotopy (a ≫ u') b)) :
      Nonempty (Homotopy u u') := by
    apply homotopy_of_Q_map_eq
    apply (cancel_epi (Q.map a)).1
    rw [hau]
    have h' : Q.map a ≫ Q.map u' = Q.map b := by
      simpa only [Functor.map_comp] using DerivedCategory.Q_map_eq_of_homotopy A h.some
    exact h'.symm
  have : IsIso (Q.map u) := by rw [hu]; infer_instance
  obtain ⟨v, hv⟩ := exists_Q_map_of_kInjective (inv (Q.map u))
  have huv : Nonempty (Homotopy (u ≫ v) (𝟙 I)) :=
    homotopy_of_Q_map_eq _ _ (by
      change Q.map (u ≫ v) = Q.map (𝟙 I)
      rw [Q.map_comp, hv, IsIso.hom_inv_id, Q.map_id])
  have hvu : Nonempty (Homotopy (v ≫ u) (𝟙 J)) :=
    homotopy_of_Q_map_eq _ _ (by
      change Q.map (v ≫ u) = Q.map (𝟙 J)
      rw [Q.map_comp, hv, IsIso.inv_hom_id, Q.map_id])
  have hiso : IsIso (DerivedCategory.Q.map (G.map u)) := by
    refine ⟨⟨DerivedCategory.Q.map (G.map v), ?_, ?_⟩⟩
    · have h := Q_map_sections_eq_of_homotopy F huv.some
      change DerivedCategory.Q.map (G.map (u ≫ v)) =
        DerivedCategory.Q.map (G.map (𝟙 I)) at h
      rw [G.map_comp, G.map_id, QΛ.map_comp, QΛ.map_id] at h
      exact h
    · have h := Q_map_sections_eq_of_homotopy F hvu.some
      change DerivedCategory.Q.map (G.map (v ≫ u)) =
        DerivedCategory.Q.map (G.map (𝟙 J)) at h
      rw [G.map_comp, G.map_id, QΛ.map_comp, QΛ.map_id] at h
      exact h
  refine ⟨u, hab, unique, hiso, ?_, ?_⟩
  · let eI := F.rightDerivedFunctor.mapIso
      (eC.symm ≪≫ asIso (Q.map a)) ≪≫ F.rightDerivedFunctorObjQIso I
    exact ⟨eI, eI ≪≫ asIso (DerivedCategory.Q.map (G.map u)), rfl⟩
  · intro C' I' J' K' _eC' a' b' ha' hb' u' hu' f
    have : I'.IsKInjective := ha'.2
    have : J'.IsKInjective := hb'.2
    obtain ⟨p, hp⟩ := exists_Q_map_of_kInjective (inv (Q.map a) ≫ f ≫ Q.map a')
    obtain ⟨q, hq⟩ := exists_Q_map_of_kInjective (inv (Q.map b) ≫ f ≫ Q.map b')
    refine ⟨⟨p, ?_⟩, ⟨q, ?_⟩, ?_⟩
    · rw [hp, IsIso.hom_inv_id_assoc]
    · rw [hq, IsIso.hom_inv_id_assoc]
    · intro p q hp hq
      have hau' : Q.map a' ≫ Q.map u' = Q.map b' := by
        simpa only [Functor.map_comp] using
          DerivedCategory.Q_map_eq_of_homotopy A hu'.some
      have hcomm : Nonempty (Homotopy (u ≫ q) (p ≫ u')) := by
        apply homotopy_of_Q_map_eq
        simp only [Functor.map_comp]
        apply (cancel_epi (Q.map a)).1
        calc
          Q.map a ≫ Q.map u ≫ Q.map q = Q.map b ≫ Q.map q := by
            rw [← Category.assoc, hau]
          _ = f ≫ Q.map b' := hq
          _ = Q.map a ≫ Q.map p ≫ Q.map u' := by
            rw [← Category.assoc, hp, Category.assoc, hau']
      simpa only [Functor.map_comp] using Q_map_sections_eq_of_homotopy F hcomm.some

end AlgebraicGeometry.Etale
