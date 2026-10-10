/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Compactly supported and ordinary cohomology of a proper scheme

For a proper `k₀`-scheme `a : X ⟶ Spec k₀` the direct image with compact support
`Ra_! = Rg_* ∘ i_!`, for the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`, is the derived
direct image `Ra_*`: the open immersion `i` is then also closed, so that `i_! ≅ i_*`, and
`Rg_* ∘ i_* ≅ R(i ≫ g)_*`. Hence the compactly supported cohomology of a Weil complex on `X`
is its ordinary cohomology, Frobenius-equivariantly.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range`:
  `j_! ⟶ j_*` is an isomorphism of `ℓ`-adic sheaves for an open immersion `j` with closed range.
- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`: `Ra_! K ≅ Ra_* K` for `X`
  proper.
- `AlgebraicGeometry.WeilSheaf.globalSectionsEquivOfIso`: isomorphic Weil sheaves have
  isomorphic global sections, compatibly with Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The comparison `j_! ⟶ j_*` of `ℓ`-adic sheaves is an isomorphism for an open immersion `j`
with closed range.** The open immersion `j` and the inclusion of the open complement `W` of its
range form a Zariski cover of `X`; the comparison restricts to an isomorphism along `j`, and
both sides vanish along `W`. -/
theorem isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range
    (hj : IsClosed (Set.range j.base)) :
    IsIso (adicOpenImmersionLowerShriekToLowerStar l j) := by
  let W : X.Opens := ⟨(Set.range j.base)ᶜ, hj.isOpen_compl⟩
  let g : ∀ i, ![U, (W : Scheme.{u})] i ⟶ X := Fin.cons j (Fin.cons W.ι fun i ↦ i.elim0)
  have : ∀ i, IsOpenImmersion (g i) :=
    Fin.cases (inferInstanceAs (IsOpenImmersion j))
      (Fin.cases (inferInstanceAs (IsOpenImmersion W.ι)) fun i ↦ i.elim0)
  have hW : Set.range W.ι.base = (Set.range j.base)ᶜ := W.range_ι
  have hsurj : ∀ x, ∃ i, x ∈ Set.range (g i).base := fun x ↦ by
    by_cases hx : x ∈ Set.range j.base
    · exact ⟨0, hx⟩
    · exact ⟨1, hW.ge hx⟩
  have hcover : Presieve.ofArrows _ g ∈ Scheme.proetalePrecoverage X :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun i ↦ this i⟩)
  have hjk : Set.range j.base ∩ Set.range W.ι.base = ∅ := by
    rw [hW, Set.inter_compl_self]
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  refine isIso_of_isIso_adicUpperStar l g hcover _ (Fin.cases ?_ (Fin.cases ?_ fun i ↦ i.elim0))
  · change IsIso ((j)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l j).app M))
    let c := (adicOpenImmersionLowerShriekToLowerStar l j).app M
    have : IsIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M ≫ (j)^*ᵃ[l].map c) := by
      rw [adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M) _
  · change IsIso ((W.ι)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l j).app M))
    have h₁ : IsZero ((W.ι)^*ᵃ[l].obj ((j)_!ᵃ[l].obj M)) :=
      isZero_adicUpperStar_adicOpenImmersionLowerShriek j W.ι hjk M
    have h₂ : IsZero ((W.ι)^*ᵃ[l].obj ((j)_*ᵃ[l].obj M)) :=
      AdicSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _ j W.ι hjk
        M.X).of_iso ((upperStarIsoOpenImmersionRestriction _ W.ι).app _))
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

end ProEtale

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The base change `ī` of a universally closed open immersion `i` has clopen range. -/
lemma isClosed_range_geometricFiberMap (i : U ⟶ X) [IsOpenImmersion i] [UniversallyClosed i]
    [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsClosed (Set.range (Scheme.Hom.geometricFiberMap i (comp_over i
      (Spec (CommRingCat.of k₀)))).base) :=
  have : UniversallyClosed (Scheme.Hom.geometricFiberMap i
      (comp_over i (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @UniversallyClosed) i
      (comp_over i (Spec (CommRingCat.of k₀))) inferInstance
  (Scheme.Hom.isClopen_range _).isClosed

/-- For a universally closed open immersion `i`, the comparison `i_! ⟶ i_*` of pro-étale Weil
sheaves is an isomorphism. -/
instance ProEtaleWeilSheaf.isIso_extensionByZeroToLowerStar (i : U ⟶ X) [IsOpenImmersion i]
    [UniversallyClosed i] [i.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i) := by
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l _
    (isClosed_range_geometricFiberMap (k₀ := k₀) i)
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have : IsIso ((IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l i).app K)) :=
    inferInstanceAs (IsIso ((adicOpenImmersionLowerShriekToLowerStar l
      (Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k₀))))).app K.carrier))
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)


namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- An isomorphism of Weil sheaves induces an isomorphism of their global sections, compatible
with the Frobenius. -/
noncomputable def globalSectionsEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G) :
    F.globalSections.Equiv G.globalSections where
  toLinearEquiv := WeilCoefficients.linearEquivOfIso
    ((ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso e)
  map_frobenius x := by
    have h : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
        e.hom.hom.hom.f.hom ≫ G.obj.str.hom.hom = F.obj.str.hom.hom ≫ e.hom.hom.hom.f.hom :=
      congrArg (fun φ ↦ φ.hom) e.hom.hom.hom.h
    have n := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality
        e.hom.hom.hom.f.hom
    have key : ((globalSectionsLowerStarIso (WeilCoefficients.{u} l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app F.obj.carrier.X ≫
        (Sheaf.Γ _ _).map F.obj.str.hom.hom) ≫ (Sheaf.Γ _ _).map e.hom.hom.hom.f.hom =
        (Sheaf.Γ _ _).map e.hom.hom.hom.f.hom ≫
          ((globalSectionsLowerStarIso (WeilCoefficients.{u} l)
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app
              G.obj.carrier.X ≫ (Sheaf.Γ _ _).map G.obj.str.hom.hom) := by
      rw [Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp, ← Category.assoc,
        ← Category.assoc]
      congr 1
      exact n.symm
    exact congrArg (fun m ↦ ((WeilCoefficients.toModuleCat l).map m).hom x) key

end WeilSheaf

/-- A functor isomorphic to one preserving K-injective complexes preserves them. -/
lemma _root_.CategoryTheory.Functor.preservesKInjectiveComplexes_of_iso {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D] {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    (e : F ≅ F') [F'.PreservesKInjectiveComplexes] : F.PreservesKInjectiveComplexes where
  isKInjective_map K _ := CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).symm.app K)

attribute [local instance] Compactification.over

variable (k₀ l) in
/-- Pushforwards of pro-étale Weil sheaves along equal morphisms are isomorphic. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCongr {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ≅ ProEtaleWeilSheaf.lowerStar k₀ l φ' := by
  subst h
  exact Iso.refl _

variable [Fact (ringChar k₀ ≠ l)]

instance (i : U ⟶ X) [IsOpenImmersion i] [UniversallyClosed i]
    [i.IsOver (Spec (CommRingCat.of k₀))] :
    (Scheme.Hom.geometricFiberMap i
      (comp_over i (Spec (CommRingCat.of k₀))))_!ᵃ[l].PreservesKInjectiveComplexes :=
  have := isIso_adicOpenImmersionLowerShriekToLowerStar_of_isClosed_range l _
    (isClosed_range_geometricFiberMap (k₀ := k₀) i)
  Functor.preservesKInjectiveComplexes_of_iso
    (asIso (adicOpenImmersionLowerShriekToLowerStar l _))

/-- **For a proper `k₀`-scheme, compactly supported direct image is direct image**: for the
chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀` of the proper structure morphism `a`, the open
immersion `i` is universally closed, so that `Ra_! K = Rg_*(i_! K) ≅ Rg_*(i_* K) ≅ Ra_* K`. -/
noncomputable def WeilComplex.derivedLowerShriekObjIsoOfIsProper
    [IsProper (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ≅
      (WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj K := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

end AlgebraicGeometry
