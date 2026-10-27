module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion
import WeilConjectures.RingTheory.OpenFlatLocus
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Relative source flat loci and parameter base change

Source: Stacks Project, Tag 05VK, `more-morphisms-lemma-base-change-flatness-fibres`,
and Tag 05VJ, `more-morphisms-lemma-base-change-criterion-flatness-fibre`.
(blueprint: lem-sfb-relative-flat-locus-base-change)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem pointwise_flatness_isPullback
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (x : P) :
    ((f.stalkMap (a x)).hom.Flat → (b.stalkMap x).hom.Flat) ∧
    ((g.stalkMap (b x)).hom.Flat → (b.stalkMap x).hom.Flat →
      (f.stalkMap (a x)).hom.Flat) := by
  have ha : pullback.fst f g (sq.isoPullback.hom x) = a x := by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_fst]
  have hb : pullback.snd f g (sq.isoPullback.hom x) = b x := by
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_snd]
  have hc : ((pullback.snd f g).stalkMap (sq.isoPullback.hom x)).hom.Flat ↔
      (b.stalkMap x).hom.Flat := by
    conv_rhs => rw [← sq.isoPullback_hom_snd]
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
  have hfa := RingHom.Flat.respectsIso.arrow_mk_iso_iff (f.arrowStalkMapIsoOfEq ha)
  have hgb := RingHom.Flat.respectsIso.arrow_mk_iso_iff (g.arrowStalkMapIsoOfEq hb)
  simpa only [hfa, hgb, hc] using
    pointwise_flatness_base_change f g (sq.isoPullback.hom x)

private noncomputable abbrev familyMap {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p) (h : T ⟶ S) :=
  pullback.map p h q h f (𝟙 T) (𝟙 S)
    (by simpa only [Category.comp_id] using hf.symm) (by simp)

private theorem familyMap_isPullback {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p) (h : T ⟶ S) :
    IsPullback (pullback.fst p h) (familyMap p q f hf h) f (pullback.fst q h) := by
  refine .of_bot ?_ ?_ (.of_hasPullback q h)
  · simpa only [familyMap, pullback.lift_snd, Category.comp_id, hf] using
      IsPullback.of_hasPullback p h
  · simp only [familyMap, pullback.lift_fst]

private theorem flatAt_iff_fiber_flatAt {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] [LocallyOfFiniteType q] (s : S)
    (z : p.fiber s) :
    (f.stalkMap (p.fiberι s z)).hom.Flat ↔
      ((familyMap p q f hf (S.fromSpecResidueField s)).stalkMap z).hom.Flat := by
  constructor
  · exact (pointwise_flatness_isPullback
      (familyMap_isPullback p q f hf (S.fromSpecResidueField s)) z).1
  · intro hz
    have hs : p (p.fiberι s z) = s := by
      rw [← Scheme.Hom.comp_apply, p.fiber_fac]
      simp
    generalize hx : p.fiberι s z = x at hs ⊢
    subst s
    have hz' : p.asFiber x = z := by
      apply (p.fiberι _).isEmbedding.injective
      simpa using hx.symm
    subst z
    exact (p.flatAt_and_base_flatAt_of_fiber_flatAt q f hf x
      (Flat.stalkMap p x) hz).1

private theorem lfp_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [h : LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFiniteType q] :
    LocallyOfFinitePresentation f := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _
      (q.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))]
    intro U
    have hcomp := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at hcomp
    have inst := hcomp
    exact this (f ∣_ q ⁻¹ᵁ U.1) (q ∣_ U.1) U.2
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have hcomp := HasRingHomProperty.comp_of_isOpenImmersion
      (P := @LocallyOfFinitePresentation) (f ⁻¹ᵁ U.1).ι (f ≫ q) h
    rw [← morphismRestrict_ι_assoc] at hcomp
    have inst := hcomp
    have hftι : LocallyOfFiniteType U.1.ι := locallyOfFiniteType_of_isOpenImmersion _
    have hftcomp : LocallyOfFiniteType (U.1.ι ≫ q) := locallyOfFiniteType_comp U.1.ι q
    exact this (f ∣_ U.1) (U.1.ι ≫ q) U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top X)]
    intro U
    have hcomp := HasRingHomProperty.comp_of_isOpenImmersion
      (P := @LocallyOfFinitePresentation) U.1.ι (f ≫ q) h
    rw [← Category.assoc] at hcomp
    have inst := hcomp
    exact this (U.1.ι ≫ f) U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  have hq := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) q inferInstance
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hq

private theorem isOpen_flat_stalks_spec
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    [LocallyOfFinitePresentation (Spec.map f)] :
    IsOpen {z : Spec S | ((Spec.map f).stalkMap z).hom.Flat} := by
  have hf : f.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance
  algebraize [f.hom]
  have : Algebra.FinitePresentation R S := hf
  have heq (z : PrimeSpectrum S) :
      ((Spec.map f).stalkMap z).hom.Flat ↔ Module.Flat R (Localization.AtPrime z.asIdeal) := by
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso f z)]
    algebraize [Localization.localRingHom (z.comap f.hom).asIdeal z.asIdeal f.hom rfl]
    have : IsScalarTower R (Localization.AtPrime (z.comap f.hom).asIdeal)
        (Localization.AtPrime z.asIdeal) :=
      .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
    change Module.Flat (Localization.AtPrime (z.comap f.hom).asIdeal)
      (Localization.AtPrime z.asIdeal) ↔ _
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime (z.comap f.hom).asIdeal) (z.comap f.hom).asIdeal.primeCompl
      (Localization.AtPrime z.asIdeal)
  have hflat (z : PrimeSpectrum S) :
      Module.Flat R (Localization.AtPrime z.asIdeal) ↔
        Module.Flat R (LocalizedModule z.asIdeal.primeCompl S) := by
    let e := (IsLocalizedModule.iso z.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime z.asIdeal))).restrictScalars R
    exact ⟨fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e, fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e.symm⟩
  change IsOpen {z : PrimeSpectrum S | ((Spec.map f).stalkMap z).hom.Flat}
  simpa only [heq, hflat] using
    (Module.isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := S))

private theorem isOpen_flat_stalks_affine
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffine E] [IsAffine L]
    [LocallyOfFinitePresentation p] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  let p' := E.isoSpec.inv ≫ p ≫ L.isoSpec.hom
  have h' : IsOpen {z : Spec Γ(E, ⊤) | (p'.stalkMap z).hom.Flat} := by
    have : LocallyOfFinitePresentation (Spec.map (Spec.preimage p')) := by
      rw [Spec.map_preimage]
      dsimp [p']
      infer_instance
    rw [← Spec.map_preimage p']
    exact isOpen_flat_stalks_spec _
  convert h'.preimage E.isoSpec.hom.continuous using 1
  ext z
  change (p.stalkMap z).hom.Flat ↔
    ((E.isoSpec.inv ≫ p ≫ L.isoSpec.hom).stalkMap (E.isoSpec.hom z)).hom.Flat
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso]
  have he : E.isoSpec.inv (E.isoSpec.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [he]


/-- The source flat locus of a morphism between the specified families is open, and its
formation commutes with every parameter base change.

Source: Stacks Project, Tag 05VK, `more-morphisms-lemma-base-change-flatness-fibres`;
its proof specializes Tag 05VJ to the structure sheaf.
(blueprint: lem-sfb-relative-flat-locus-base-change)

Proof:
1. Around x choose affine charts Spec A in S, Spec B in Y, and Spec C in X,
   compatible with f. Local finite presentation of p and local finite type of q
   give C finitely presented over A and B finite type over A. Shrinking the X-chart
   by a basic open preserves finite presentation: adjoining v with relation av - 1
   constructs localization at a. Apply
   lem-weil-pbc-finite-presentation-over-finite-type-algebra to A -> B -> C.
   Thus f is locally of finite presentation.
2. On such a chart apply lem-weil-pbc-openness-of-flatness to B -> C and M = C,
   a free rank-one C-module. The flat locus in Spec C is open. The identifications
   of lem-weil-pbc-affine-open-stalk-localization identify the stalk map with
   B_b -> C_c, where b is the inverse image of c. By
   lem-weil-pbc-flat-over-localization, flatness over B_b equals flatness over B.
   Thus these open chart loci are precisely the intersections with the locus U
   defined by def-weil-flat-morphism, and their union is U.
3. For s = p(x), the fibre square of f over s is cartesian by the fibre-product
   universal property. By lem-sfb-pointwise-flatness-base-change, flatness of f at x
   implies flatness of f_s at its corresponding fibre point. Conversely, p is flat
   at x, so lem-sfb-fibrewise-flatness-criterion gives the reverse implication.
   Hence U is also the fibrewise flat locus.
4. For any h : T -> S, base-change stability of flatness, local finite presentation
   and local finite type (lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-lft-base-change) keeps all
   hypotheses in force. Repeat Step 3 for f_T to describe its flat locus fibrewise.
5. For x' in X_T put t = p_T(x'), x = pi_X(x') and s = h(t). By
   lem-weil-pbc-fibre-of-base-change, the fibres over t are the fibres over s after
   extension of residue fields kappa(s) -> kappa(t). These identifications commute
   with the induced maps f_s and (f_T)_t: both composites with each projection agree,
   so the fibre-product universal property gives the required cartesian square.
6. By lem-weil-pbc-field-extension-base-change-faithfully-flat with D = kappa(s),
   the residue-field extension is flat. Its spectral map and its base change to
   Y_s are flat by def-weil-flat-morphism and
   lem-weil-pbc-flat-morphism-base-change. The two implications of
   lem-sfb-pointwise-flatness-base-change in the square of Step 5 identify flatness
   of (f_T)_t at x' with flatness of f_s at x. Combining Steps 3 and 4 proves
   that the flat locus of f_T equals the inverse image of U under pi_X.
-/
theorem isOpen_flatLocus_and_baseChange {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] [LocallyOfFiniteType q] :
    IsOpen {x : X | (f.stalkMap x).hom.Flat} ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ S),
        {x : ↥(pullback p h) |
          ((pullback.map p h q h f (𝟙 T) (𝟙 S)
            (by simpa only [Category.comp_id] using hf.symm) (by simp)).stalkMap x).hom.Flat} =
          (pullback.fst p h) ⁻¹' {x : X | (f.stalkMap x).hom.Flat} := by
  have hfp : LocallyOfFinitePresentation f := by
    have : LocallyOfFinitePresentation (f ≫ q) := hf.symm ▸ inferInstance
    exact lfp_of_comp f q
  constructor
  · rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨V, hV, hfx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨U, hU, hxU, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ V from hfx)
    let U' : X.Opens := U
    let V' : Y.Opens := V
    have : IsAffine U'.toScheme := hU
    have : IsAffine V'.toScheme := hV
    have hopen := isOpen_flat_stalks_affine (f.resLE V' U' e)
    refine ⟨U'.ι '' {z | ((f.resLE V' U' e).stalkMap z).hom.Flat}, ?_,
      U'.ι.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (Scheme.Hom.resLEStalkMap f e z)).mp hz
    · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (Scheme.Hom.resLEStalkMap f e ⟨x, hxU⟩)).mpr hx
  · intro T h
    let pT := pullback.snd p h
    let qT := pullback.snd q h
    let fT := familyMap p q f hf h
    have hfT : fT ≫ qT = pT := by simp [fT, qT, pT, familyMap, pullback.map]
    ext x'
    change (fT.stalkMap x').hom.Flat ↔
      (f.stalkMap (pullback.fst p h x')).hom.Flat
    let t := pT x'
    let s := h t
    let r := Spec.map (h.residueFieldMap t)
    let a : pT.fiber t ⟶ p.fiber s :=
      pullback.map pT (T.fromSpecResidueField t) p (S.fromSpecResidueField s)
        (pullback.fst p h) r h pullback.condition.symm (by simp [r, s])
    let b : qT.fiber t ⟶ q.fiber s :=
      pullback.map qT (T.fromSpecResidueField t) q (S.fromSpecResidueField s)
        (pullback.fst q h) r h pullback.condition.symm (by simp [r, s])
    let fs := familyMap p q f hf (S.fromSpecResidueField s)
    let ft := familyMap pT qT fT hfT (T.fromSpecResidueField t)
    have sqX : IsPullback a (pT.fiberToSpecResidueField t)
        (p.fiberToSpecResidueField s) r :=
      isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback p h) t
    have sqY : IsPullback b (qT.fiberToSpecResidueField t)
        (q.fiberToSpecResidueField s) r :=
      isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback q h) t
    have hcomm : a ≫ fs = ft ≫ b := by
      apply pullback.hom_ext <;>
        simp [a, b, fs, ft, fT, familyMap, pullback.map, Category.assoc]
    have sq : IsPullback a ft fs b := by
      apply IsPullback.of_bot (t := sqY) _ hcomm
      simpa [fs, ft, familyMap, Scheme.Hom.fiberToSpecResidueField,
        pullback.map] using sqX
    have hr : Flat r := by
      apply Flat.SpecMap_iff.mpr
      algebraize [(h.residueFieldMap t).hom]
      exact inferInstanceAs (Module.Flat (S.residueField s) (T.residueField t))
    have hb : Flat b := MorphismProperty.of_isPullback sqY.flip hr
    have hpoint : p.fiberι s (a (pT.asFiber x')) = pullback.fst p h x' := by
      change (a ≫ p.fiberι s) (pT.asFiber x') = _
      have ha : a ≫ p.fiberι s = pT.fiberι t ≫ pullback.fst p h := by
        simp [a, Scheme.Hom.fiberι, pullback.map]
      rw [ha, Scheme.Hom.comp_apply, pT.fiberι_asFiber]
    have hsflat := flatAt_iff_fiber_flatAt p q f hf s (a (pT.asFiber x'))
    have htflat := flatAt_iff_fiber_flatAt pT qT fT hfT t (pT.asFiber x')
    have hreflection := pointwise_flatness_isPullback sq (pT.asFiber x')
    have heq := RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (f.arrowStalkMapIsoOfEq hpoint)
    have hbase : (fs.stalkMap (a (pT.asFiber x'))).hom.Flat ↔
        (ft.stalkMap (pT.asFiber x')).hom.Flat :=
      ⟨hreflection.1, hreflection.2 (Flat.stalkMap b _)⟩
    have htpoint : pT.fiberι t (pT.asFiber x') = x' := pT.fiberι_asFiber x'
    have het := RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (fT.arrowStalkMapIsoOfEq htpoint)
    exact het.symm.trans (htflat.trans (hbase.symm.trans (hsflat.symm.trans heq)))

end AlgebraicGeometry
