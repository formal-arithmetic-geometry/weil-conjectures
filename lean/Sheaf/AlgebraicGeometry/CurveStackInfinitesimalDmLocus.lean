/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.NodalCurveStackSmooth
import Sheaf.AlgebraicGeometry.AlgebraicStackOpenDmLocus
import Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas
import Sheaf.AlgebraicGeometry.GroupSchemeIdentityDualUnramified
import Sheaf.AlgebraicGeometry.DmPointStabilizer
import Sheaf.AlgebraicGeometry.OpenModuliDiagonalRestriction
import Sheaf.AlgebraicGeometry.OpenModuliSubstackAlgebraicity
import Sheaf.AlgebraicGeometry.ProperCurveGeometricContainment
import Sheaf.AlgebraicGeometry.ProperCurveSchemeRealization
import Sheaf.AlgebraicGeometry.ProperCurveStabilizerComparison

/-! # The Deligne--Mumford locus in the stack of proper curves

Source: Stacks Project, moduli-curves.tex, Tags 0DSW and 0E6G, first proof paragraph;
stacks-morphisms.tex, Tags 0DSM, 0DSN and 06N3
(blueprint: lem-sfb-curve-stack-infinitesimal-dm-locus).

The moduli category has algebraic-space families. The point characterization includes
all proper schemes of dimension at most one, and the final maximality assertion tests
all geometric algebraic-space objects. The empty family and empty open are allowed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace ProperCurveModuli

/-- Membership of the point represented by a scheme in a full open substack: its
representable presheaf is isomorphic, over the given field, to an object of that open.
This is independent of presentation because a full open is closed under isomorphism.
Source: Stacks, moduli-curves.tex, Tag 0DSW(3)(a)
(blueprint: lem-sfb-curve-stack-infinitesimal-dm-locus). -/
def SchemePointIn {k : Type u} [Field k]
    (U : OpenModuliSubstack (category (Spec (.of k))))
    (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))
    (C : Scheme.{u}) (f : C ⟶ Spec (.of Ω)) : Prop :=
  ∃ X : ProperCurveFamily (Over.mk a),
    ∃ e : X.space.obj.obj ≅ yoneda.obj (Over.mk (f ≫ a)),
      e.hom ≫ yoneda.map (Over.homMk (U := Over.mk (f ≫ a)) (V := Over.mk a) f rfl) =
        X.projection ∧ U.property ⟨Over.mk a, X⟩

end ProperCurveModuli

set_option backward.isDefEq.respectTransparency false in
private theorem infinitesimalAutomorphisms_transport {S : Scheme.{u}}
    (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ S)
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ yoneda.obj (Over.mk a))
    (g : G ⟶ yoneda.obj (Over.mk a)) (e : F ≅ G) (he : e.hom ≫ g = f)
    (hf : ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a f) :
    ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a g := by
  let d := yoneda.map (ProperCurveFamily.dualProjection Ω a)
  let q : pullback f d ≅ pullback g d :=
    asIso (pullback.map f d g d e.hom (𝟙 _) (𝟙 _) (by simpa using he.symm)
      (by simp))
  have hq : q.hom ≫ pullback.snd g d = pullback.snd f d := by
    simp [q]
  have hqi : q.inv ≫ pullback.snd f d = pullback.snd g d := by
    rw [← hq, Iso.inv_hom_id_assoc]
  have hr : ProperCurveFamily.infinitesimalReduction Ω a f ≫ q.hom =
      e.hom ≫ ProperCurveFamily.infinitesimalReduction Ω a g := by
    dsimp only [q, d]
    apply pullback.hom_ext
    · simp only [pullback.map, ProperCurveFamily.infinitesimalReduction,
        asIso_hom, Category.assoc, limit.lift_π, PullbackCone.mk_π_app]
      change (ProperCurveFamily.infinitesimalReduction Ω a f ≫
        pullback.fst f (yoneda.map (ProperCurveFamily.dualProjection Ω a))) ≫
          e.hom = _
      simp [ProperCurveFamily.infinitesimalReduction]
    · simp only [pullback.map, ProperCurveFamily.infinitesimalReduction,
        asIso_hom, Category.assoc, limit.lift_π, PullbackCone.mk_π_app, Category.comp_id]
      rw [← Category.assoc, he]
  intro β hβ hbase
  let α : Aut (pullback f d) := q ≪≫ β ≪≫ q.symm
  have hα : α = Iso.refl _ := by
    apply hf α
    · change ProperCurveFamily.infinitesimalReduction Ω a f ≫
        (q.hom ≫ β.hom ≫ q.inv) = _
      calc
        _ = (e.hom ≫ ProperCurveFamily.infinitesimalReduction Ω a g) ≫
            β.hom ≫ q.inv := by rw [← Category.assoc, ← Category.assoc, hr, Category.assoc]
        _ = (e.hom ≫ ProperCurveFamily.infinitesimalReduction Ω a g) ≫ q.inv := by
          rw [← Category.assoc, Category.assoc e.hom, hβ]
        _ = _ := by rw [← hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change q.hom ≫ β.hom ≫ q.inv ≫ pullback.snd f d = _
      rw [hqi, hbase, hq]
  apply Iso.ext
  calc
    β.hom = q.inv ≫ α.hom ≫ q.hom := by simp [α]
    _ = (Iso.refl _).hom := by rw [hα]; simp

private theorem infinitesimalAutomorphisms_iso_iff {S : Scheme.{u}}
    (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ S)
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ yoneda.obj (Over.mk a))
    (g : G ⟶ yoneda.obj (Over.mk a)) (e : F ≅ G) (he : e.hom ≫ g = f) :
    ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a f ↔
      ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a g := by
  refine ⟨infinitesimalAutomorphisms_transport Ω a f g e he,
    infinitesimalAutomorphisms_transport Ω a g f e.symm ?_⟩
  simp only [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]


private theorem dm_of_algebraic_unramified {S : Scheme.{u}}
    (F : BasedCategory (Over S)) (hF : IsAlgebraicModuliStack F)
    (h : HasUnramifiedModuliDiagonal F) : IsDeligneMumfordModuliStack F := by
  obtain ⟨hs, hd, P, atlas, ha⟩ := hF
  apply (unramifiedModuliDiagonal_iff_etaleAtlas F hs hd ?_).2.mp h
  refine ⟨P, atlas, ?_⟩
  intro T t
  obtain ⟨Z, p, he, hsm, hsurj⟩ := ha T t
  exact ⟨Z, p, he, hsurj, hsm⟩

/-- There is a largest open of the stack of proper curves with unramified relative
diagonal, it admits a surjective etale scheme atlas, and its geometric scheme points
are exactly those with no nonidentity infinitesimal automorphism. Any open satisfying
the same geometric condition is contained in it and is Deligne--Mumford.
Source: Stacks, moduli-curves.tex, Tags 0DSW and 0E6G, first proof paragraph;
stacks-morphisms.tex, Tags 0DSM, 0DSN and 06N3
(blueprint: lem-sfb-curve-stack-infinitesimal-dm-locus).

Proof: (1) The curve-stack algebraicity theorem
`lem-sfb-nodal-curve-stack-smooth` supplies algebraicity of this precise category.
Apply `lem-sfb-algebraic-stack-open-dm-locus` to obtain the largest open with
unramified diagonal. (2) Apply `lem-sfb-unramified-diagonal-etale-atlas` to obtain
the required scheme atlas, so the conclusion uses the recorded DM convention.
(3) For a geometric curve, `lem-sfb-proper-curve-automorphism-scheme` represents
its automorphisms by a separated finite-type group scheme. Naturality for reduction
Spec Omega -> Spec (DualNumber Omega) identifies identity-reducing automorphisms
with dual-number points of that group above the identity; naturality for the
projection identifies the constant identity point with the identity automorphism.
(4) `lem-sfb-group-scheme-identity-dual-unramified` equates triviality of those
points with unramifiedness of the automorphism group, and
`lem-sfb-algebraic-stack-dm-point-stabilizer` equates that with membership in the
largest open. The argument applies equally to algebraic-space geometric objects.
(5) For an open V satisfying the geometric condition, pull back the largest open to
any scheme mapping to V. Every point of that scheme has a geometric lift in the
pulled-back open, so the open is the whole scheme. Thus V is contained in the
largest open. (6) Pull back its scheme atlas to V; the resulting open subscheme of
the atlas is a representable surjective etale atlas of V. This includes the empty
open, whose pulled-back atlas is empty. No reducedness, smoothness of automorphism
groups, connectedness, purity or restriction on characteristic is used. -/
theorem exists_curveStack_infinitesimal_dm_locus (k : Type u) [Field k] :
    ∃ U : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
      HasUnramifiedModuliDiagonal U.category ∧
      IsDeligneMumfordModuliStack U.category ∧
      (∀ V : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
        HasUnramifiedModuliDiagonal V.category → V.IsContainedIn U) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))
          (C : Scheme.{u}) (f : C ⟶ Spec (.of Ω)),
        IsProper f → topologicalKrullDim C ≤ 1 →
          (ProperCurveModuli.SchemePointIn U Ω a C f ↔
            ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a
              (yoneda.map (Over.homMk (U := Over.mk (f ≫ a)) (V := Over.mk a) f rfl)))) ∧
      (∀ V : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Spec (.of k))
            (X : ProperCurveFamily (Over.mk a)),
          V.property ⟨Over.mk a, X⟩ →
            ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a X.projection) →
        V.IsContainedIn U ∧ IsDeligneMumfordModuliStack V.category) := by
  have hF := (nodal_curve_stack_smooth k).1
  have hDM : ∀ W : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))),
      HasUnramifiedModuliDiagonal W.category → IsDeligneMumfordModuliStack W.category :=
    fun W h ↦ dm_of_algebraic_unramified _ (W.isAlgebraic hF) h
  obtain ⟨hstack, hdiag, P, atlas, hatlas⟩ := hF
  have ha : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (ProperCurveModuli.category (Spec (.of k)))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange atlas T t Z p ∧ SpaceMapIsSurjective Z T p ∧
          SpaceMapIsSmooth Z T p := by
    intro T t
    obtain ⟨Z, p, he, hsm, hsurj⟩ := hatlas T t
    exact ⟨Z, p, he, hsurj, hsm⟩
  obtain ⟨U, hU, hmax⟩ := exists_largest_open_unramified_moduli_diagonal
    (ProperCurveModuli.category (Spec (.of k))) hstack hdiag ⟨P, atlas, ha⟩
  have hpoint : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (.of Ω) ⟶ Spec (.of k)) (X : ProperCurveFamily (Over.mk a)),
      U.property ⟨Over.mk a, X⟩ ↔
        ProperCurveFamily.HasTrivialInfinitesimalAutomorphisms Ω a X.projection := by
    intro Ω _ _ a X
    obtain ⟨x, G, Z, p, hlft, hqc, hG, hmem, hspace, hdual⟩ :=
      ProperCurveModuli.exists_stabilizer_comparison Ω a X
    have := hlft
    have := hqc
    exact (hmem U).trans
      ((fieldPoint_factors_dmOpen_iff_unramified_automorphismSpace
        _ hstack hdiag ⟨P, atlas, ha⟩ U hU hmax Ω a x Z p hG).trans
          (hspace.trans ((isUnramified_iff_identityDualNumberPoints G.X).trans hdual)))
  refine ⟨U, hU, hDM U hU, hmax, ?_, ?_⟩
  · intro Ω _ _ a C f hp hd
    constructor
    · rintro ⟨X, e, he, hX⟩
      exact (infinitesimalAutomorphisms_iso_iff Ω a X.projection _ e he).mp
        ((hpoint Ω a X).mp hX)
    · intro h
      obtain ⟨X, e, he⟩ := ProperCurveModuli.exists_scheme_family a C f hp hd
      exact ⟨X, e, he, (hpoint Ω a X).mpr
        ((infinitesimalAutomorphisms_iso_iff Ω a X.projection _ e he).mpr h)⟩
  · intro V hV
    have hVU : V.IsContainedIn U :=
      ProperCurveModuli.open_containment_of_geometric_points U V
        (fun Ω _ _ a X hX ↦ (hpoint Ω a X).mpr (hV Ω a X hX))
    exact ⟨hVU, hDM V (V.hasUnramifiedDiagonal_of_contained U hVU hU)⟩

end AlgebraicGeometry
