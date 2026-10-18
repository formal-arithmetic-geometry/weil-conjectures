/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Stabilization of a closed inverse system with locally finitely presented limit

Source: Stacks Project, Limits, Tag 081B, Lemma `lemma-finite-type-eventually-closed`,
clause (3), applied to the identity of the limit
(blueprint: lem-weil-pbc-closed-limit-lfp-stabilization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem exists_isIso_projection_of_qcqs
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (S : Scheme.{u}) (D : J ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ j, LocallyOfFiniteType (t.app j)]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j} (f : i ⟶ j), Mono (D.map f)]
    (c : Cone D) (hc : IsLimit c) (q : c.pt ⟶ S)
    (hq : ∀ j, c.π.app j ≫ t.app j = q)
    [LocallyOfFinitePresentation q] :
    ∃ k : J, ∀ (j : J) (_f : j ⟶ k), IsIso (c.π.app j) := by
  -- Descend the identity of the limit, then descend its inverse equation.
  have ht : c.π ≫ t = (Functor.const J).map ((𝟙 c.pt) ≫ q) := by
    ext j
    simpa using hq j
  obtain ⟨i, g, hg, hgt⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t q c hc (𝟙 _) ht
  obtain ⟨k, hki, heq⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D t (t.app i) c hc
      (g ≫ c.π.app i) (𝟙 _) (by simp [hq, hgt]) (by simp)
      (by simp [← Category.assoc, hg])
  refine ⟨k, fun j f ↦ ?_⟩
  let hji := f ≫ hki
  let v : D.obj j ⟶ c.pt := D.map hji ≫ g
  have hv : c.π.app j ≫ v = 𝟙 _ := by
    simpa [v, ← Category.assoc] using hg
  have hv' : v ≫ c.π.app j = 𝟙 _ := by
    apply (cancel_mono (D.map hji)).mp
    simp only [Category.assoc, Category.id_comp, c.w]
    change D.map hji ≫ g ≫ c.π.app i = D.map hji
    simpa [hji, D.map_comp, Category.assoc] using congrArg (D.map f ≫ ·) heq
  exact ⟨⟨v, hv, hv'⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_isIso_projection_on_affine
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (S : Scheme.{u}) (D : J ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const J).obj S)
    [∀ j, LocallyOfFiniteType (t.app j)]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j} (f : i ⟶ j), Mono (D.map f)]
    (c : Cone D) (hc : IsLimit c) (q : c.pt ⟶ S)
    (hq : ∀ j, c.π.app j ≫ t.app j = q)
    [LocallyOfFinitePresentation q] (a : J) (U : (D.obj a).Opens)
    (hU : IsAffineOpen U) :
    ∃ k : Over a, ∀ (j : Over a) (_f : j ⟶ k),
      IsIso ((opensCone D c a U).π.app j) := by
  let E := opensDiagram D a U
  let d := opensCone D c a U
  let v : E ⟶ (Functor.const (Over a)).obj S :=
    opensDiagramι D a U ≫ Functor.whiskerLeft (Over.forget a) t
  have (j : Over a) : IsAffine (E.obj j) := hU.preimage (D.map j.hom)
  have (j : Over a) : LocallyOfFiniteType (v.app j) := by
    dsimp [v, E, opensDiagramι]
    infer_instance
  have {i j : Over a} (f : i ⟶ j) : Mono (E.map f) := by
    apply mono_of_mono_fac (Scheme.Hom.resLE_comp_ι (D.map f.left) _)
  let q' : d.pt ⟶ S := (c.π.app a ⁻¹ᵁ U).ι ≫ q
  have : LocallyOfFinitePresentation q' := by dsimp [q', d, opensCone]; infer_instance
  exact exists_isIso_projection_of_qcqs S E v d (isLimitOpensCone D c hc a U) q'
    (fun j ↦ by simp [v, d, E, opensCone, opensDiagramι, q', hq])

/-- A directed inverse system of quasi-compact schemes locally of finite type over a base,
with closed immersion transitions and locally finitely presented limit over that base,
has isomorphic limit projections at every sufficiently large stage.

Source: Stacks Project, Limits, Tag 081B, clause (3)
(blueprint: lem-weil-pbc-closed-limit-lfp-stabilization).

Proof plan:
1. Fix a stage `a`. Local finite type and quasi-compactness give a finite affine cover of
   that stage by charts mapping into affine opens of the base. Closed immersion transitions
   give quotient rings on all later inverse-image charts, with surjective transition maps.
2. By `exists_limit_affine_transition`, its open-restriction and affine clauses identify
   the limit charts with spectra of the filtered colimits of these rings. Every colimit
   element has a representative, so the map from the chart ring at `a` is surjective.
   Local finite presentation makes each limit chart ring finitely presented over its base
   chart ring, by `LocallyOfFinitePresentation.finitePresentation_appLE`.
3. Present the stage chart ring by finitely many polynomial generators. The composite
   polynomial-ring surjection to the limit has finitely generated kernel by
   `Algebra.FinitePresentation.ker_fg_of_mvPolynomial`. Its images generate the kernel of
   the stage-to-limit map, so the limit chart ring is a quotient by finitely many elements.
4. Eventual equality of representatives in a filtered colimit kills these finitely many
   elements at one common later stage. Surjectivity and equality of kernels identify every
   subsequent chart ring with the limit chart ring. An empty generator list needs no delay.
5. Take a common upper bound for the finitely many chart bounds. Each limit projection is
   an isomorphism on this affine open cover. Its local inverses agree on overlaps by inverse
   uniqueness and glue by `Scheme.Cover.glueMorphisms`. Both composites are identities by
   `Scheme.Cover.hom_ext`. An empty cover means the stage and every later scheme are empty,
   and their projections are isomorphisms as well. -/
theorem exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) (D : Iᵒᵖ ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (t.app i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    (c : Cone D) (hc : IsLimit c) (q : c.pt ⟶ S)
    (hq : ∀ i : Iᵒᵖ, c.π.app i ≫ t.app i = q)
    [LocallyOfFinitePresentation q] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsIso (c.π.app (op i)) := by
  -- A finite affine cover lets us work without quasi-separatedness of the stages.
  classical
  let a : I := Classical.choice inferInstance
  obtain ⟨s, hs⟩ := (D.obj (op a)).isBasis_affineOpens.isOpenCover.exists_finite_of_compactSpace
  let U (j : s) : (D.obj (op a)).Opens := j.val.val
  choose k hk using fun j : s ↦
    exists_isIso_projection_on_affine S D t c hc q hq (op a) (U j) j.val.property
  have hb : ∃ b : I, ∀ j : s, (k j).left.unop ≤ b := by
    obtain ⟨b, hb⟩ :=
      (Finset.univ.image (fun j : s ↦ (k j).left.unop)).exists_le
    exact ⟨b, fun j ↦ hb _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩
  obtain ⟨b, hb⟩ := hb
  obtain ⟨b', hab', hbb'⟩ := exists_ge_ge a b
  refine ⟨b', fun i hi ↦ ?_⟩
  let f : op i ⟶ op a := (homOfLE (hab'.trans hi)).op
  have hcover : ⨆ j, D.map f ⁻¹ᵁ U j = ⊤ :=
    (hs.comap (D.map f).base.hom).iSup_eq_top
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun j ↦ D.map f ⁻¹ᵁ U j) hcover
  intro j
  let z : Over (op a) := Over.mk f
  let e : z ⟶ k j := Over.homMk ((homOfLE ((hb j).trans (hbb'.trans hi))).op)
  have he := hk j z e
  have hpre : c.π.app (op i) ⁻¹ᵁ (D.map f ⁻¹ᵁ U j) = c.π.app (op a) ⁻¹ᵁ U j := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hπ : (opensCone D c (op a) (U j)).π.app z =
      Scheme.homOfLE _ hpre.ge ≫ (c.π.app (op i) ∣_ D.map f ⁻¹ᵁ U j) := by
    rfl
  have : IsIso (Scheme.homOfLE _ hpre.ge) :=
    ⟨⟨Scheme.homOfLE _ hpre.le, by simp, by simp⟩⟩
  rw [hπ] at he
  exact IsIso.of_isIso_comp_left (Scheme.homOfLE _ hpre.ge) _

end AlgebraicGeometry
