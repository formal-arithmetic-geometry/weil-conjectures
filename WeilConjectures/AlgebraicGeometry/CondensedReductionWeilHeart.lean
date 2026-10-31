/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedReductionTransportData
import WeilConjectures.AlgebraicGeometry.CondensedReductionTopologicalTransport
import WeilConjectures.AlgebraicGeometry.CondensedReductionNumericalTransport
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField

/-! # Reduction on the actual condensed constructible Weil heart

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6 and final paragraph.
(blueprint: lem-zl-condensed-reduction-weil-heart)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedReduction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem geometric_reduction :
    ∃ e : (D.geometricFiber (model X₀)).left ≅
        (D.geometricFiber X₀).left.nilradical.subscheme,
      e.hom ≫ (D.geometricFiber X₀).left.nilradical.subschemeι =
        geometricImmersion D X₀ := by
  let := Fintype.ofFinite D.k₀
  let : IsReduced (model X₀).left :=
    inferInstanceAs (IsReduced X₀.left.nilradical.subscheme)
  let : (model X₀).left.Over (Spec (.of D.k₀)) := ⟨(model X₀).hom⟩
  let : LocallyOfFiniteType ((model X₀).left ↘ Spec (.of D.k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (model X₀).hom)
  let : QuasiCompact ((model X₀).left ↘ Spec (.of D.k₀)) :=
    inferInstanceAs (QuasiCompact (model X₀).hom)
  have : IsReduced (D.geometricFiber (model X₀)).left :=
    (geometricallyReduced_finiteType_of_perfectField D.k₀ (model X₀).left).1 D.k
  have hclosed : IsClosedImmersion (geometricImmersion D X₀) :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) (immersion X₀)
      (inferInstanceAs (IsClosedImmersion X₀.left.nilradical.subschemeι))
  have hsurj : Surjective (geometricImmersion D X₀) :=
    MorphismProperty.overPullbackMap (P := @Surjective)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) (immersion X₀)
      (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
        X₀.left).2.2.1
  let f := (geometricImmersion D X₀).liftNilradical
  have hf : f ≫ (D.geometricFiber X₀).left.nilradical.subschemeι =
      geometricImmersion D X₀ := by
    simp [f]
  have : IsClosedImmersion (f ≫ (D.geometricFiber X₀).left.nilradical.subschemeι) :=
    hf.symm ▸ hclosed
  have : IsClosedImmersion f :=
    IsClosedImmersion.of_comp_isClosedImmersion f
      (D.geometricFiber X₀).left.nilradical.subschemeι
  have : Surjective f := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := (geometricImmersion D X₀).surjective
      ((D.geometricFiber X₀).left.nilradical.subschemeι y)
    refine ⟨x, (D.geometricFiber X₀).left.nilradical.subschemeι.isEmbedding.injective ?_⟩
    change (f ≫ (D.geometricFiber X₀).left.nilradical.subschemeι) x = _
    simpa [hf] using hx
  have : IsIso f := isIso_of_isClosedImmersion_of_surjective f
  exact ⟨asIso f, hf⟩

private theorem geometric_commutes : Commutes D X₀ := by
  let := Fintype.ofFinite D.k₀
  unfold Commutes
  change geometricImmersion D X₀ ≫ D.galoisMap X₀.hom _ =
    D.galoisMap (model X₀).hom _ ≫ geometricImmersion D X₀
  apply pullback.hom_ext
  · simp only [Category.assoc, (D.galoisMap_projections X₀.hom _).1]
    simp only [geometricImmersion, Over.pullback_map_left, pullback.lift_fst,
      ← Category.assoc, (D.galoisMap_projections (model X₀).hom _).1]
  · simp only [Category.assoc, (D.galoisMap_projections X₀.hom _).2]
    simp [geometricImmersion, Over.pullback_map_left, ← Category.assoc,
      (D.galoisMap_projections (model X₀).hom _).2]

private theorem mixed_of_iso {M N : CondensedWeil.WeilModule D l X₀}
    (e : M ≅ N) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hM : CondensedWeil.Mixed D l X₀ M iota w) :
    CondensedWeil.Mixed D l X₀ N iota w := by
  obtain ⟨n, G, φ, hc, hz, ⟨last⟩, hm, hp⟩ := hM
  exact ⟨n, G, φ, hc, hz, ⟨last ≪≫ e⟩, hm, hp⟩

private theorem unitFiltrations_of_imageFiltrations {h : Commutes D X₀}
    (E : WeilEquivalence D l X₀ h) (iota : PadicAlgCl l →+* ℂ)
    (himage : ImageFiltrations D l (model X₀) X₀ E.directImage iota) :
    UnitFiltrations D l X₀ E iota := by
  intro M n G last weights w hz hm hp
  obtain ⟨hz', hm', hp', hmix⟩ := himage n G weights w hz hm hp
  let := E.unit_iso M
  let finish : (G ⋙ E.directImage).obj (Fin.last n) ≅ M :=
    E.directImage.mapIso last ≪≫ (asIso (E.adjunction.unit.app M)).symm
  refine ⟨G ⋙ E.directImage, Iso.refl _, finish, ?_, hz', hm', hp', ?_⟩
  · simp [finish]
  · exact mixed_of_iso D l X₀ ((ObjectProperty.ι _).mapIso finish) iota w hmix

/-- Reduction is an exact equivalence for pulled-back condensed coefficients, including
its actual module adjunction, its geometric Frobenius mate, local Frobenius and every
prescribed finite mixed filtration.

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6 and final paragraph
(blueprint: lem-zl-condensed-reduction-weil-heart).

Proof:
1. Perfect-field geometric reducedness makes the geometric reduction model reduced.
   Its base-changed immersion is a surjective closed immersion. Factor it through the
   nilradical of the target. The factor is again a surjective closed immersion, and its
   target is reduced, so it is an isomorphism. Its composite is the specified immersion.
2. Compare the two projections of the geometric pullback to prove the commuting square:
   Frobenius fixes the model projection and applies the same closure automorphism.
3. Apply lem-zl-condensed-reduction-topological-transport to that square for the actual
   ordinary and Weil equivalences and their normalized local scalar-fibre comparisons.
4. Apply lem-zl-condensed-reduction-numerical-transport to the supplied equivalence and
   local comparison for numerical invariance and both image-filtration assertions.
5. Given a filtration G of inverseImage M with endpoint isomorphism last, set
   P = G composed with directImage and use the identity comparison c. The direct-image
   image-filtration assertion gives zero, monomorphisms, pure quotients and a mixed
   endpoint. Take finish to be directImage.mapIso last followed by the inverse of the
   actual unit at M. The unit is invertible, and cancellation proves the endpoint square.
   Compose the endpoint isomorphism of the Mixed witness with the underlying Weil
   isomorphism finish. This gives Mixed for M and all the required UnitFiltrations data,
   including repeated terms and length zero. -/
theorem reduction_weil_heart (hl : l ≠ D.p) [IsSeparated X₀.hom]
    (iota : PadicAlgCl l ≃+* ℂ) :
    (∃ e : (D.geometricFiber (model X₀)).left ≅ (D.geometricFiber X₀).left.nilradical.subscheme,
      e.hom ≫ (D.geometricFiber X₀).left.nilradical.subschemeι = geometricImmersion D X₀) ∧
    Nonempty (ModuleEquivalence D l X₀) ∧
    ∃ (h : Commutes D X₀) (E : WeilEquivalence D l X₀ h),
      LocalCompatibility D l X₀ E ∧ NumericalCompatibility D l X₀ E iota ∧
        ImageFiltrations D l X₀ (model X₀) E.inverseImage iota.toRingHom ∧
        ImageFiltrations D l (model X₀) X₀ E.directImage iota.toRingHom ∧
        UnitFiltrations D l X₀ E iota.toRingHom := by
  have hgeom := geometric_reduction D X₀
  have h := geometric_commutes D X₀
  obtain ⟨hmodule, E, hlocal⟩ := reduction_topological_transport D l X₀ hl h
  obtain ⟨hnumerical, hinverse, hdirect⟩ :=
    reduction_numerical_transport D l X₀ hl E hlocal iota
  exact ⟨hgeom, hmodule, h, E, hlocal, hnumerical, hinverse, hdirect,
    unitFiltrations_of_imageFiltrations D l X₀ E iota.toRingHom hdirect⟩

end WeilConjectures.CondensedReduction
