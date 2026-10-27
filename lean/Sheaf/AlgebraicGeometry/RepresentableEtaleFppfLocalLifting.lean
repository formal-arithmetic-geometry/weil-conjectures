/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local lifting for representable surjective étale maps to fppf sheaves

Source: Stacks Project, Spaces, Tag 0262, proof of (3); Topologies, Tag 021M;
Sites, Tags 00WM and 00WN (blueprint: lem-a1-representable-etale-fppf-local-lifting).

The target is an arbitrary fppf sheaf, without an algebraic-space hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable surjective étale map from a scheme has local lifts on its scheme
pullbacks, hence is locally surjective and epimorphic as a map of fppf sheaves.
Source: Stacks Project, Spaces, Tag 0262, proof of (3); Topologies, Tag 021M;
Sites, Tags 00WM and 00WN (blueprint: lem-a1-representable-etale-fppf-local-lifting).

Proof:
1. For `T` and `ξ`, Yoneda gives the natural transformation whose value on `b : W → T`
   is `F(b)(ξ)`. Apply the scheme tests of def-trf-algebraic-space to represent its
   pullback with `p` by `V`. The resulting projections `v : V → T` and `a : V → U`
   give the displayed pullback square. Commutativity evaluated at the identity of `V`
   gives `p(a) = F(v)(ξ)`. Étaleness and surjectivity hold for this same projection:
   the representing squares from the two tests are uniquely isomorphic over `T`.
2. By def-weil-etale-morphism, `v` is flat and locally of finite presentation.
   Together with surjectivity this makes its singleton an fppf covering by
   def-pc-fppf-site, including the empty target. The generated sieve covers on the
   slice site by its definition.
3. The displayed equality is a lift of the restriction of `ξ` on this covering.
   For arbitrary `T` and `ξ`, this proves local surjectivity in the sense of 00WM.
4. Apply lem-weil-pbc-site-sheaf-sets-epi-locally-surjective (00WN), specifically
   `Sheaf.epi_of_isLocallySurjective'`, to obtain the sheaf epimorphism. No diagonal
   representability or global section lift is used. -/
theorem representable_etale_fppf_local_lifting {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (U : Over S)
    (p : (Scheme.fppfTopology.over S).yoneda.obj U ⟶ F)
    (hp : IsEtale p.hom) (hs : IsSurjective p.hom) :
    (∀ (T : Over S) (ξ : F.obj.obj (op T)),
      ∃ (V : Over S) (v : V ⟶ T) (a : V ⟶ U),
        IsPullback (yoneda.map a) (yoneda.map v) p.hom (yonedaEquiv.symm ξ) ∧
        p.hom.app (op V) a = F.obj.map v.op ξ ∧
        Etale v.left ∧ Surjective v.left ∧
        Sieve.generate (Presieve.singleton v) ∈ (Scheme.fppfTopology.over S) T) ∧
    Sheaf.IsLocallySurjective p ∧ Epi p := by
  classical
  have hlift : ∀ (T : Over S) (ξ : F.obj.obj (op T)),
      ∃ (V : Over S) (v : V ⟶ T) (a : V ⟶ U),
        IsPullback (yoneda.map a) (yoneda.map v) p.hom (yonedaEquiv.symm ξ) ∧
        p.hom.app (op V) a = F.obj.map v.op ξ ∧
        Etale v.left ∧ Surjective v.left ∧
        Sieve.generate (Presieve.singleton v) ∈ (Scheme.fppfTopology.over S) T := by
    intro T ξ
    obtain ⟨V, v, a', ha', hv⟩ := hp T (yonedaEquiv.symm ξ)
    obtain ⟨W, w, b, hb, hw⟩ := hs T (yonedaEquiv.symm ξ)
    let e : V ≅ W := yoneda.preimageIso (ha'.isoIsPullback _ _ hb)
    have he : e.hom ≫ w = v := by
      apply yoneda.map_injective
      simpa only [Functor.map_comp, e, Functor.preimageIso_hom,
        Functor.map_preimage] using ha'.isoIsPullback_hom_snd _ _ hb
    have hvSur : Surjective v.left := by
      rw [← he]
      change Surjective (e.hom.left ≫ w.left)
      have := hw
      infer_instance
    let a : V ⟶ U := yoneda.preimage a'
    have ha : yoneda.map a = a' := yoneda.map_preimage a'
    have hsq : IsPullback (yoneda.map a) (yoneda.map v) p.hom
        (yonedaEquiv.symm ξ) := by
      rw [ha]
      exact ha'
    have hξ : p.hom.app (op V) a = F.obj.map v.op ξ := by
      exact congrArg (fun t ↦ t.app (op V) (𝟙 V)) hsq.w
    have hcover : Sieve.generate (Presieve.singleton v) ∈
        (Scheme.fppfTopology.over S) T := by
      have := hv
      have := hvSur
      rw [GrothendieckTopology.mem_over_iff]
      change (Sieve.generate (Presieve.singleton v)).functorPushforward (Over.forget S) ∈ _
      rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
      exact Precoverage.generate_mem_toGrothendieck v.left.singleton_mem_fppfPrecoverage
    exact ⟨V, v, a, hsq, hξ, hv, hvSur, hcover⟩
  have hlocal : Sheaf.IsLocallySurjective p := by
    constructor
    intro T ξ
    obtain ⟨V, v, a, _, hξ, _, _, hcover⟩ := hlift T ξ
    apply (Scheme.fppfTopology.over S).superset_covering ?_ hcover
    rw [Sieve.generate_le_iff]
    rintro Z f ⟨⟩
    exact ⟨a, hξ⟩
  have := hlocal
  exact ⟨hlift, hlocal, Sheaf.epi_of_isLocallySurjective' p⟩

end AlgebraicGeometry.AlgebraicSpace
