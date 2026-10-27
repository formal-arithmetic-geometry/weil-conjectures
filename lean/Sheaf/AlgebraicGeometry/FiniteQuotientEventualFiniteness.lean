/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Eventual finiteness of algebra quotients along an ideal approximation

Source: Stacks Project, Properties, Tag 086N,
`lemma-finite-algebra-directed-colimit-finite-finitely-presented`, final proof paragraph;
Tag 0817, `lemma-integral-algebra-directed-colimit-finite`, proof of (2)
(blueprint: lem-weil-pbc-finite-quotient-eventual-finiteness).

An ideal subsheaf is represented by an injective module-sheaf map with ideal section
ranges. Quotient finiteness is written using the canonical ring quotients on affine opens.
The recorded generated-ideal lemma identifies these rings with the affine sections of
the sheaf quotients. For the given ideal itself, the hypothesis already supplies
finiteness of the canonical affine ring quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.CommAlgebraSheaf

-- The finite list consists of monic equations evaluated at algebra generators
-- (Stacks 086N, final paragraph). Any ideal containing it gives a finite quotient.
private theorem finite_relations {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.FiniteType) (J : Ideal A)
    (hJ : ((Ideal.Quotient.mk J).comp f).Finite) :
    ∃ t : Finset A, (∀ x ∈ t, x ∈ J) ∧ ∀ I : Ideal A,
      (∀ x ∈ t, x ∈ I) → ((Ideal.Quotient.mk I).comp f).Finite := by
  classical
  let : Algebra R A := f.toAlgebra
  obtain ⟨s, hs⟩ := hf.out
  have hp : ∀ a : s, ∃ p : Polynomial R, p.Monic ∧
      Polynomial.eval₂ f (a : A) p ∈ J := by
    intro a
    obtain ⟨p, hp, hz⟩ := hJ.to_isIntegral (Ideal.Quotient.mk J a)
    refine ⟨p, hp, ?_⟩
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa only [Polynomial.hom_eval₂, RingHom.comp_apply] using hz
  choose p hp hz using hp
  refine ⟨Finset.univ.image (fun a : s ↦ Polynomial.eval₂ f (a : A) (p a)), ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hz a
  · intro I hI
    let q : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
    have htop : Algebra.adjoin R (q '' (s : Set A)) = ⊤ := by
      rw [Algebra.adjoin_image, hs, Algebra.map_top, AlgHom.range_eq_top]
      exact Ideal.Quotient.mk_surjective
    have hint : ∀ x ∈ q '' (s : Set A), _root_.IsIntegral R x := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨p ⟨a, ha⟩, hp ⟨a, ha⟩, ?_⟩
      have hm := hI _ (Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩)
      have he := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      change Polynomial.eval₂ ((Ideal.Quotient.mk I).comp f)
        (Ideal.Quotient.mk I a) (p ⟨a, ha⟩) = 0
      simpa only [Polynomial.hom_eval₂] using he
    have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral
      (s.finite_toSet.image q) hint
    rw [htop] at hfin
    have : Module.Finite R (A ⧸ I) :=
      Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv)
    exact this

-- The first isomorphism theorem transports module finiteness without choosing
-- algebra structures on the sheaf sections.
private theorem quotient_finite_iff {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (h : R →+* B)
    (hcomm : g.comp f = h) (hg : Function.Surjective g) (I : Ideal A)
    (hI : RingHom.ker g = I) :
    ((Ideal.Quotient.mk I).comp f).Finite ↔ h.Finite := by
  subst I
  let e := g.quotientKerEquivOfSurjective hg
  have he : e.toRingHom.comp ((Ideal.Quotient.mk (RingHom.ker g)).comp f) = h := by
    ext r
    change g.quotientKerEquivOfSurjective hg
      (Ideal.Quotient.mk (RingHom.ker g) (f r)) = h r
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    exact RingHom.congr_fun hcomm r
  constructor
  · intro hf
    rw [← he]
    exact e.finite.comp hf
  · intro hf
    have he' : e.symm.toRingHom.comp h =
        (Ideal.Quotient.mk (RingHom.ker g)).comp f := by
      rw [← he, ← RingHom.comp_assoc]
      simp
    rw [← he']
    exact e.symm.finite.comp hf

set_option backward.isDefEq.respectTransparency false in
/-- A finite-type quasi-coherent algebra with finite quotient by an ideal has finite
quotients by the ideals generated at every sufficiently late stage of any directed
quasi-coherent module approximation of that ideal. No injectivity or finite generation
is imposed on the approximating modules or their maps to the ideal.

Here `c.pt` is the ideal module, `i` is its inclusion, and `J U` is its ideal of sections.
On an affine open, the generated ideal at `k` is the span of the range of
`(c.ι.app k ≫ i).app U`. The composed ring homomorphisms below give precisely the
structure maps of the affine quotient algebras; `RingHom.Finite` means module finiteness.

Source: Stacks, Properties, Tag 086N, final proof paragraph, as applied in Tag 0817(2)
(blueprint: lem-weil-pbc-finite-quotient-eventual-finiteness).

Proof:
1. Apply lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal(b) to each composite
   E_k → J → S. The generated ideals and quotients are quasi-coherent, and on affines
   their sections are the displayed spans and ring quotients. The hypothesis directly
   gives finiteness of S(U)/J(U), so constructing that sheaf quotient is unnecessary.
2. Choose a finite affine cover by lem-weil-pbc-qcqs-finite-affine-open-cover. On each
   member choose finitely many algebra generators using the finite-type hypothesis.
3. By lem-weil-pbc-finite-algebra-is-integral, each generator's image in the finite
   quotient satisfies a monic polynomial. Evaluating at the original generator gives
   an element of J(U), since the canonical quotient map has kernel J(U).
4. By lem-weil-pbc-quasi-coherent-module-colimit-affine-sections, lift each of these
   finitely many relation sections to one E_k. Nonemptiness and directedness give a
   common upper bound k₀, also when the list is empty. Cocone compatibility puts every
   relation in the image of E_k for every k ≥ k₀; injectivity is unnecessary.
5. Each quotient on the finite cover is generated by the images of the chosen algebra
   generators, which satisfy those monic relations. Apply
   lem-weil-pbc-finite-of-integral-generators to obtain module finiteness on this cover.
6. The quotient module is quasi-coherent by step 1. Clause (c) of
   lem-weil-pbc-quasi-coherent-finite-type-affine propagates finiteness from the cover
   to every affine open, proving exactly the displayed conclusion. -/
theorem finite_quotient_eventually_finite
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (S : X.CommAlgebraSheaf) (hS : S.toModule.IsQuasicoherent)
    (hSft : ∀ U : X.Opens, IsAffineOpen U → (S.hom.hom.app (op U)).hom.FiniteType)
    (K : Type u) [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    (E : K ⥤ X.Modules) (c : Cocone E) (hc : IsColimit c)
    (hE : ∀ k : K, (E.obj k).IsQuasicoherent) (hJ : c.pt.IsQuasicoherent)
    (i : c.pt ⟶ S.toModule) (J : ∀ U : X.Opens, Ideal (S.right.obj.obj (op U)))
    (hi : ∀ U : X.Opens, Function.Injective (i.app U) ∧
      Set.range (i.app U) = (J U : Set (S.right.obj.obj (op U))))
    (hfinite : ∀ U : X.Opens, IsAffineOpen U →
      ((Ideal.Quotient.mk (J U)).comp (S.hom.hom.app (op U)).hom).Finite) :
    ∃ k₀ : K, ∀ k : K, k₀ ≤ k → ∀ U : X.Opens, IsAffineOpen U →
      ((Ideal.Quotient.mk
        (Ideal.span (Set.range ((c.ι.app k ≫ i).app U) :
          Set (S.right.obj.obj (op U))))).comp (S.hom.hom.app (op U)).hom).Finite := by
  classical
  let : c.pt.IsQuasicoherent := hJ
  have hcol := (Modules.quasiCoherentModuleColimitAffineSections X K E c hc hE).2
  have hlocal : ∀ U : X.Opens, IsAffineOpen U → ∃ k₀ : K,
      ∀ k : K, k₀ ≤ k →
        ((Ideal.Quotient.mk
          (Ideal.span (Set.range ((c.ι.app k ≫ i).app U) :
            Set (S.right.obj.obj (op U))))).comp (S.hom.hom.app (op U)).hom).Finite := by
    intro U hU
    obtain ⟨t, ht, htf⟩ := finite_relations (S.hom.hom.app (op U)).hom
      (hSft U hU) (J U) (hfinite U hU)
    have hlift : ∀ r : t, ∃ k : K, ∃ e : Γ(E.obj k, U),
        (c.ι.app k ≫ i).app U e = (r : S.right.obj.obj (op U)) := by
      intro r
      have hr : (r : S.right.obj.obj (op U)) ∈ Set.range (i.app U) := by
        rw [(hi U).2]
        exact ht r r.property
      obtain ⟨v, hv⟩ := hr
      obtain ⟨k, e, he⟩ := (hcol U hU).1 v
      refine ⟨k, e, ?_⟩
      change i.app U (((c.ι.app k).val.app (op U)) e) = _
      exact (congrArg (i.app U) he).trans hv
    choose idx e he using hlift
    obtain ⟨k₀, hk₀⟩ := (Set.finite_range idx).bddAbove
    refine ⟨k₀, fun k hk ↦ htf _ ?_⟩
    intro r hr
    let a : t := ⟨r, hr⟩
    have ha : idx a ≤ k := (hk₀ (Set.mem_range_self a)).trans hk
    apply Ideal.subset_span
    refine ⟨(E.map (homOfLE ha)).app U (e a), ?_⟩
    have hw := congrArg (fun f ↦ f.app U (e a)) (c.w (homOfLE ha))
    change (c.ι.app k).app U ((E.map (homOfLE ha)).app U (e a)) =
      (c.ι.app (idx a)).app U (e a) at hw
    change i.app U ((c.ι.app k).app U ((E.map (homOfLE ha)).app U (e a))) = r
    rw [hw]
    exact he a
  obtain ⟨T, hT, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  let U : T → X.Opens := fun j ↦ j.val.val
  have : Finite T := hT
  have hU : ∀ j : T, IsAffineOpen (U j) := fun j ↦ j.val.property
  have hUc : (⨆ j : T, U j) = ⊤ := by
    simpa only [U, iSup_subtype] using hcover.symm
  choose idx hidx using fun j : T ↦ hlocal (U j) (hU j)
  obtain ⟨k₀, hk₀⟩ := (Set.finite_range idx).bddAbove
  refine ⟨k₀, ?_⟩
  intro k hk
  obtain ⟨N, n, I, _, _, _, _, hI, _, Q, q, P, p, a,
    _, _, hQ, _, hq, _⟩ :=
    generated_ideal_quotient_quasiCoherent S hS (E.obj k) (hE k) (c.ι.app k ≫ i)
  have hbridge : ∀ V : X.Opens, IsAffineOpen V →
      (((Ideal.Quotient.mk
          (Ideal.span (Set.range ((c.ι.app k ≫ i).app V) :
            Set (S.right.obj.obj (op V))))).comp (S.hom.hom.app (op V)).hom).Finite ↔
        Module.Finite Γ(X, V) Γ(Q.toModule, V)) := by
    intro V hV
    rw [← hI V hV]
    exact quotient_finite_iff (S.hom.hom.app (op V)).hom
      (q.right.hom.app (op V)).hom (Q.hom.hom.app (op V)).hom
      (by exact congrArg (fun f ↦ (f.hom.app (op V)).hom) q.w)
      (hq V hV).1 (I V) (hq V hV).2
  have hfin : ∀ j : T, Module.Finite Γ(X, U j) Γ(Q.toModule, U j) := by
    intro j
    apply (hbridge (U j) (hU j)).mp
    exact hidx j k ((hk₀ (Set.mem_range_self j)).trans hk)
  have hall := ((Modules.quasicoherent_finite_type_affine X).2 Q.toModule hQ).2.1
    T U hUc hU hfin
  intro V hV
  exact (hbridge V hV).mpr (hall.2 V hV)

end AlgebraicGeometry.Scheme.CommAlgebraSheaf
