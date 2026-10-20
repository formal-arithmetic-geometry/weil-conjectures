/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Subobject.Limits
import all WeilConjectures.CategoryTheory.FiniteFiltrationRefinement
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!
# Devissage of a constructible etale module sheaf

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-constructible-devissage.md`
(blueprint: lem-fin-constructible-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem open_closed_factor_iso
    (Λ : Type (u + 1)) [CommRing Λ] {T C Z : Scheme.{u}}
    (a : T ⟶ C) (q : C ⟶ Z) (j : T ⟶ Z)
    [IsOpenImmersion a] [IsClosedImmersion q] [IsOpenImmersion j]
    (h : a ≫ q = j) (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj L ≅
      (lowerStar (ModuleCat.{u + 1} Λ) q).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) a).obj L)) := by
  let A := ModuleCat.{u + 1} Λ
  let M := (openImmersionLowerShriek A j).obj L
  let w := q.openComplement.ι
  have hwq : Disjoint (Set.range w.base) (Set.range q.base) :=
    disjoint_range_of_range_eq_compl w q q.range_eq_compl_range_openComplement_ι
  have hjw : Disjoint (Set.range j.base) (Set.range w.base) := by
    apply hwq.symm.mono_left
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  have hz : IsZero ((upperStar A w).obj M) :=
    isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j w hjw L
  let η := (upperStarLowerStarAdjunction A q).unit.app M
  have hη : IsIso η := by
    apply isIso_of_isIso_upperStar_map A w q
      q.range_eq_compl_range_openComplement_ι η
    · have hz' := isZero_upperStar_lowerStar_of_disjoint_range A w q hwq
        ((upperStar A q).obj M)
      exact ⟨⟨0, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
    · exact inferInstanceAs (IsIso ((upperStar A q).map
        ((upperStarLowerStarAdjunction A q).unit.app M)))
  have hp : IsPullback a (𝟙 T) q j :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using h⟩
  have hbc := isIso_openImmersionLowerShriekBaseChange A a q j h hp
  let e := (asIso (openImmersionLowerShriekBaseChange A a q j h)).app L
  exact ⟨asIso η ≪≫ (lowerStar A q).mapIso e.symm⟩

private theorem closed_open_generator_iso
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (V : Z.Opens)
    (L : Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (_ : IsOpenImmersion (V.ι ≫ i).toImage),
      Nonempty ((lowerStar (ModuleCat.{u + 1} Λ) i).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).obj L) ≅
        (lowerStar (ModuleCat.{u + 1} Λ) (V.ι ≫ i).imageι).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (V.ι ≫ i).toImage).obj L)) := by
  let A := ModuleCat.{u + 1} Λ
  let c := V.ι ≫ i
  have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c :=
    ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let q : c.image ⟶ Z := IsClosedImmersion.lift i c.imageι (by
    simpa [Scheme.Hom.imageι] using (V.ι.le_ker_comp i))
  have hq : q ≫ i = c.imageι := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (q ≫ i) := hq.symm ▸ inferInstance
  have : IsClosedImmersion q := IsClosedImmersion.of_comp_isClosedImmersion q i
  have ha : c.toImage ≫ q = V.ι := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hq, Scheme.Hom.toImage_imageι]
  obtain ⟨e⟩ := open_closed_factor_iso Λ c.toImage q V.ι ha L
  exact ⟨inferInstance, ⟨(lowerStar A i).mapIso e ≪≫
    (lowerStarComp A q i c.imageι hq.symm).app _⟩⟩

/-- A constructible sheaf has a finite filtration with factors extended from lisse sheaves
on locally closed constructible subschemes. The locally closed extension uses the canonical
scheme-theoretic closure `j.image`, cut out by `j.ker`, its closed immersion `j.imageι`,
and the open immersion `j.toImage`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-constructible-devissage.md`
(blueprint: lem-fin-constructible-devissage).

Proof:
1. Finite type over a field makes X Noetherian. Let P be the property of being an
   extension from a lisse sheaf using the canonical scheme-theoretic closure. Induct
   on closed supports in X to show that the closed direct image of any constructible
   sheaf belongs to P.filtrationClosure. The empty support gives a zero object.
2. Generic constancy provides a dense lisse open in the closed subscheme. Its closed
   complement has strictly smaller image in X. Pullback preserves constructibility,
   so induction applies to the closed restriction.
3. Push the open-closed short exact sequence into X using exact closed direct image.
   Its closed term belongs to the filtration closure by induction and composition
   of direct images. For its open term, factor the canonical scheme-theoretic image
   through the closed subscheme using the kernel inequality. Base change and the
   closed-adjunction unit identify the two extension-by-zero descriptions; the unit
   is invertible by restricting to the closed part and its complementary open.
4. Extension closure combines the two terms. Apply this to the identity closed
   immersion of X and use the proved subobject_filtration_of_closure helper from
   FiniteFiltrationRefinement to obtain the required finite subobject chain.
   This helper constructs inverse-image filtrations under quotient epimorphisms;
   no splitting of the extension is asserted. -/
theorem exists_constructible_sheaf_devissage
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : IsSmoothBaseChangeCoefficients N Λ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Subobject F),
      IsZero (S 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ∧
      S (Fin.last m) = ⊤ ∧
      ∃ hS : ∀ r : Fin m, S r.castSucc ≤ S r.succ,
        ∀ r : Fin m, ∃ (T : Scheme.{u}) (j : T ⟶ X),
          IsImmersion j ∧ Topology.IsConstructible (Set.range j) ∧
          ∃ (_ : IsOpenImmersion j.toImage)
            (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
            Scheme.IsFiniteLocallyConstantSheaf L ∧
            Nonempty (cokernel (Subobject.ofLE (S r.castSucc) (S r.succ) (hS r)) ≅
              (lowerStar (ModuleCat.{u + 1} Λ) j.imageι).obj
                ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j.toImage).obj L)) := by
  classical
  -- Noetherian induction replaces the dimension induction in the original plan.
  have _ := hΛ
  let A := ModuleCat.{u + 1} Λ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let P : ObjectProperty (Sheaf X.smallEtaleTopology A) := fun G ↦
    ∃ (T : Scheme.{u}) (j : T ⟶ X),
      IsImmersion j ∧ Topology.IsConstructible (Set.range j) ∧
      ∃ (_ : IsOpenImmersion j.toImage)
        (L : Sheaf T.smallEtaleTopology A),
        Scheme.IsFiniteLocallyConstantSheaf L ∧
        Nonempty (G ≅ (lowerStar A j.imageι).obj
          ((openImmersionLowerShriek A j.toImage).obj L))
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    obtain ⟨T, j, hj, hc, ho, L, hL, ⟨eL⟩⟩ := h
    exact ⟨T, j, hj, hc, ho, L, hL, ⟨e.symm ≪≫ eL⟩⟩⟩
  have hclosed : ∀ (D : TopologicalSpace.Closeds X) {Z : Scheme.{u}}
      (i : Z ⟶ X) [IsClosedImmersion i], Set.range i.base = D →
      ∀ (G : Sheaf Z.smallEtaleTopology A) [Scheme.IsConstructibleSheaf G],
        P.filtrationClosure ((lowerStar A i).obj G) := by
    intro D
    induction D using WellFoundedLT.induction with
    | ind D ih =>
      intro Z i hi hD G hG
      by_cases hZ : IsEmpty Z
      · exact .of_isZero ((lowerStar A i).map_isZero
          (Scheme.Etale.isZero_sheaf_of_isEmpty G))
      have : Nonempty Z := not_isEmpty_iff.mp hZ
      obtain ⟨V, hVd, hV⟩ := Scheme.IsConstructibleSheaf.exists_dense_open G
      have hS := (shortExact_openClosedShortComplex A V.ι V.closedComplement G
        (by simp)).map_of_exact (lowerStar A i)
      apply P.filtrationClosure.prop_X₂_of_shortExact hS
      · apply ObjectProperty.le_filtrationClosure (P := P)
        obtain ⟨ho, e⟩ := closed_open_generator_iso Λ i V ((upperStar A V.ι).obj G)
        exact ⟨V.toScheme, V.ι ≫ i, inferInstance,
          (V.ι ≫ i).isLocallyClosed_range.isConstructible_of_noetherianSpace,
          ho, (upperStar A V.ι).obj G, hV, e⟩
      · have hlt : (⟨Set.range (V.closedComplement ≫ i).base,
            (V.closedComplement ≫ i).isClosedEmbedding.isClosed_range⟩ :
              TopologicalSpace.Closeds X) < D := by
          rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hD,
            Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
          refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
          obtain ⟨z, hz⟩ := hVd.nonempty
          obtain ⟨y, hy, hyz⟩ : i.base z ∈ i.base '' Set.range V.closedComplement.base :=
            h ▸ ⟨z, rfl⟩
          rw [i.isClosedEmbedding.injective hyz, V.range_closedComplement] at hy
          exact hy hz
        have : Scheme.IsConstructibleSheaf ((upperStar A V.closedComplement).obj G) :=
          Scheme.IsConstructibleSheaf.upperStar _ _
        exact P.filtrationClosure.prop_of_iso
          ((lowerStarComp A V.closedComplement i).app _).symm
          (ih _ hlt (V.closedComplement ≫ i) rfl _)
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  have hcl : P.filtrationClosure F :=
    P.filtrationClosure.prop_of_iso ((lowerStarId A X).app F)
      (hclosed ⊤ (𝟙 X) (by simp) F)
  obtain ⟨m, S, hS, hbot, htop, hquot⟩ :=
    CategoryTheory.subobject_filtration_of_closure P hcl
  refine ⟨m, S, ?_, htop, fun r ↦ hS r.castSucc_le_succ, hquot⟩
  rw [hbot]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

end AlgebraicGeometry.Etale
