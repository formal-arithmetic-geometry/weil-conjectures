/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.Paper.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
import Sheaf.Paper.StrictHenselizationPointEvaluationProperties
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale

/-! # Ind-etale affine strict-local base change

Source: Stacks Project, Tag 0GIP, case (2), and Tag 0GJS, the displayed strict-local
ring comparison (blueprint: lem-weil-pbc-ind-etale-affine-strict-local-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem pointedMap_existsUnique
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ S) (hs : s = x ≫ f) :
    ∃! h : strictHenselizationScheme x ⟶ strictHenselizationScheme s,
      h ≫ strictHenselizationStructuralMap s = strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s)) := by
  subst s
  exact strictHenselizationMap_existsUnique f x

private theorem evaluation_isLocal
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) [IsLocalRing (strictHenselizationRing s)] :
    IsLocalHom (strictHenselizationPointEvaluation s) := by
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo s)).hom.toAlgebra
  let ψ := strictHenselizationPointEvaluationToSep s rfl
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    (strictHenselizationPointEvaluationToSep_surjective s rfl)
  let ι := (IntermediateField.val
    (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom
  have : IsLocalHom ι := inferInstance
  exact (inferInstance : IsLocalHom (ι.comp ψ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem structural_proAffineEtale
    {S : Scheme.{u}} [IsAffine S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : proAffineEtale (strictHenselizationStructuralMap s) := by
  let a := Spec.preimage (strictHenselizationStructuralMap s ≫ S.isoSpec.hom)
  have ha : Spec.map a ≫ S.isoSpec.inv = strictHenselizationStructuralMap s := by
    simp only [a, Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hR := smallStrictHenselization_indEtale_of_affine_chart s Γ(S, ⊤) S.isoSpec.inv
    ⟨S.isoSpec.hom (s (IsLocalRing.closedPoint Ω)), by simp⟩
    (Iso.refl _) a.hom (by
      change Spec.map a ≫ S.isoSpec.inv = 𝟙 _ ≫ strictHenselizationStructuralMap s
      simpa only [Category.id_comp] using ha)
  have hi : proAffineEtale (strictHenselizationStructuralMap s ≫ S.isoSpec.hom) := by
    rw [← Spec.map_preimage (strictHenselizationStructuralMap s ≫ S.isoSpec.hom)]
    exact proAffineEtale_Spec_iff.mpr hR
  exact (proAffineEtale.cancel_right_of_respectsIso _ _).mp hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointedMap_isIso
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ S)
    (h : strictHenselizationScheme x ⟶ strictHenselizationScheme s)
    (hf : proAffineEtale f)
    (hb : h ≫ strictHenselizationStructuralMap s = strictHenselizationStructuralMap x ≫ f)
    (hp : Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s))) : IsIso h := by
  obtain ⟨hsLocal, hsStrict⟩ := strictHenselizationLocalStructure s
  have := hsLocal
  have := hsStrict
  obtain ⟨hxLocal, _⟩ := strictHenselizationLocalStructure x
  have := hxLocal
  have hsPro := structural_proAffineEtale s
  have hxPro := structural_proAffineEtale x
  have hPro : proAffineEtale h := proAffineEtale.of_postcomp h
    (strictHenselizationStructuralMap s) hsPro
    (hb ▸ proAffineEtale.comp_mem _ _ hxPro hf)
  let a := Spec.preimage h
  have ha : Spec.map a = h := Spec.map_preimage h
  have haInd : a.hom.IndEtale := proAffineEtale_Spec_iff.mp (ha.symm ▸ hPro)
  have heval : (strictHenselizationPointEvaluation x).comp a.hom =
      strictHenselizationPointEvaluation s := by
    have heq : a ≫ CommRingCat.ofHom (strictHenselizationPointEvaluation x) =
        CommRingCat.ofHom (strictHenselizationPointEvaluation s) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ha]
      exact hp
    exact congrArg CommRingCat.Hom.hom heq
  have : IsLocalHom (strictHenselizationPointEvaluation s) := evaluation_isLocal s
  have : IsLocalHom ((strictHenselizationPointEvaluation x).comp a.hom) := heval ▸ ‹_›
  have : IsLocalHom a.hom := isLocalHom_of_comp a.hom (strictHenselizationPointEvaluation x)
  let : Algebra (strictHenselizationRing s) (strictHenselizationRing x) := a.hom.toAlgebra
  have : Algebra.WeaklyEtale (strictHenselizationRing s) (strictHenselizationRing x) :=
    haInd.weaklyEtale
  have hbij : Function.Bijective a.hom :=
    Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing
  have : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr hbij
  rw [← ha]
  change IsIso (Scheme.Spec.map a.op)
  infer_instance

/-- The canonical comparison of strict localizations is an isomorphism for an ind-etale
map on one side of an affine fibre product. The four functorial maps are specified by
commuting with the structural maps and with the canonical geometric-point evaluations.
These are the pointed maps of `strictHenselizationFunctoriality`; their existence is part
of the conclusion, so no choices of residue identifications or local-ring instances are
extra hypotheses. The isomorphism is uniquely characterized by its two projections.

Source: Stacks Project, Tag 0GIP, case (2), and Tag 0GJS
(blueprint: lem-weil-pbc-ind-etale-affine-strict-local-base-change).

Proof:
1. Identify the original affine fibre product with Spec of B tensor_A C, using
   lem-weil-pbc-fibre-product-affine-spectra. Strict-henselization functoriality supplies
   the four pointed local maps, and its uniqueness makes their square commute.
2. By lem-weil-pbc-strict-henselization-affine-chart-ind-etale, the maps from A, B, C,
   and B tensor_A C to their strict-local rings are ind-etale. Composition, base change,
   and the relative-map clause of lem-weil-pbc-ind-etale-stability imply that the maps
   from the strict-local A ring to the strict-local B ring and from the strict-local C
   ring to the strict-local tensor ring are ind-etale, hence weakly etale.
3. Functoriality makes these local maps of strictly henselian local rings. Apply
   thm-weil-pbc-weak-etale-strict-local (Olivier's theorem) to both. Thus u and m below
   are isomorphisms.
4. The second projection of pullback u v is an isomorphism since u is. Its inverse is
   the pair (v followed by u inverse, identity). Compose this inverse with m to obtain
   the comparison isomorphism. The commuting square gives its first projection l;
   its second projection is m. The pullback universal property gives uniqueness and,
   using the structural equations for l and m, compatibility with the map to Y.
No finiteness of A to C or algebraicity of the geometric-point field is used. -/
theorem indEtale_affine_strictLocal_baseChange
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : A ⟶ C)
    (hf : f.hom.IndEtale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ pullback (Spec.map f) (Spec.map g))
    (barB : Spec (.of Ω) ⟶ Spec B) (barC : Spec (.of Ω) ⟶ Spec C)
    (barA : Spec (.of Ω) ⟶ Spec A)
    (hbarB : barB = barY ≫ pullback.fst (Spec.map f) (Spec.map g))
    (hbarC : barC = barY ≫ pullback.snd (Spec.map f) (Spec.map g))
    (hbarA : barA = barB ≫ Spec.map f) :
    ∃ (u : strictHenselizationScheme barB ⟶ strictHenselizationScheme barA)
      (v : strictHenselizationScheme barC ⟶ strictHenselizationScheme barA)
      (hu : u ≫ strictHenselizationStructuralMap barA =
        strictHenselizationStructuralMap barB ≫ Spec.map f)
      (hv : v ≫ strictHenselizationStructuralMap barA =
        strictHenselizationStructuralMap barC ≫ Spec.map g),
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barB)) ≫ u =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barA)) ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barC)) ≫ v =
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barA)) ∧
      ∃ (l : strictHenselizationScheme barY ⟶ strictHenselizationScheme barB)
        (m : strictHenselizationScheme barY ⟶ strictHenselizationScheme barC),
        l ≫ strictHenselizationStructuralMap barB =
          strictHenselizationStructuralMap barY ≫
            pullback.fst (Spec.map f) (Spec.map g) ∧
        m ≫ strictHenselizationStructuralMap barC =
          strictHenselizationStructuralMap barY ≫
            pullback.snd (Spec.map f) (Spec.map g) ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫ l =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barB)) ∧
        Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barY)) ≫ m =
          Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation barC)) ∧
        ∃! e : strictHenselizationScheme barY ≅ pullback u v,
          e.hom ≫ pullback.fst u v = l ∧
          e.hom ≫ pullback.snd u v = m ∧
          e.hom ≫ pullback.map u v (Spec.map f) (Spec.map g)
            (strictHenselizationStructuralMap barB)
            (strictHenselizationStructuralMap barC)
            (strictHenselizationStructuralMap barA) hu hv =
              strictHenselizationStructuralMap barY := by
  classical
  have hbarA' : barA = barC ≫ Spec.map g := by
    rw [hbarA, hbarB, hbarC, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨u, ⟨hu, hpu⟩, _⟩ := pointedMap_existsUnique (Spec.map f) barB barA hbarA
  obtain ⟨v, ⟨hv, hpv⟩, _⟩ := pointedMap_existsUnique (Spec.map g) barC barA hbarA'
  obtain ⟨l, ⟨hl, hpl⟩, _⟩ :=
    pointedMap_existsUnique (pullback.fst (Spec.map f) (Spec.map g)) barY barB hbarB
  obtain ⟨m, ⟨hm, hpm⟩, _⟩ :=
    pointedMap_existsUnique (pullback.snd (Spec.map f) (Spec.map g)) barY barC hbarC
  have hsquare : l ≫ u = m ≫ v := by
    obtain ⟨w, _, hwuniq⟩ := pointedMap_existsUnique
      (pullback.fst (Spec.map f) (Spec.map g) ≫ Spec.map f) barY barA
      (by rw [hbarA, hbarB, Category.assoc])
    have h₁ : l ≫ u = w := hwuniq _ ⟨by
      rw [Category.assoc, hu, ← Category.assoc, hl, Category.assoc],
      by rw [← Category.assoc, hpl, hpu]⟩
    have h₂ : m ≫ v = w := hwuniq _ ⟨by
      rw [Category.assoc, hv, ← Category.assoc, hm, Category.assoc, pullback.condition],
      by rw [← Category.assoc, hpm, hpv]⟩
    exact h₁.trans h₂.symm
  have hfu : proAffineEtale (Spec.map f) := proAffineEtale_Spec_iff.mpr hf
  have huIso : IsIso u := pointedMap_isIso (Spec.map f) barB barA u hfu hu hpu
  have hmIso : IsIso m := pointedMap_isIso
    (pullback.snd (Spec.map f) (Spec.map g)) barY barC m
    (proAffineEtale.pullback_snd _ _ hfu) hm hpm
  let c := pullback.lift l m hsquare
  have hc : c ≫ pullback.snd u v = m := pullback.lift_snd _ _ _
  have : IsIso (c ≫ pullback.snd u v) := by rw [hc]; infer_instance
  have : IsIso c := IsIso.of_isIso_comp_right c (pullback.snd u v)
  refine ⟨u, v, hu, hv, hpu, hpv, l, m, hl, hm, hpl, hpm, asIso c, ?_, ?_⟩
  · refine ⟨pullback.lift_fst _ _ _, hc, ?_⟩
    apply pullback.hom_ext
    · change c ≫ _ ≫ _ = _
      simp only [pullback.map, pullback.lift_fst, c, pullback.lift_fst_assoc]
      exact hl
    · change c ≫ _ ≫ _ = _
      simp only [pullback.map, pullback.lift_snd, c, pullback.lift_snd_assoc]
      exact hm
  · intro e he
    apply Iso.ext
    apply pullback.hom_ext
    · exact he.1.trans (pullback.lift_fst _ _ _).symm
    · exact he.2.1.trans hc.symm

end AlgebraicGeometry.Scheme
