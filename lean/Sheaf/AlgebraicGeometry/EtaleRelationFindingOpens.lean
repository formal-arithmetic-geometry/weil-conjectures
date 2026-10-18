module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Restriction of a quotient by an fppf relation is an open subspace

Source: Stacks Project, `literature/stacks-project/spaces.tex`, Tag 02WU
(lemma-finding-opens), using Tag 02VH for restriction of the relation and Tags 023Q/02W2
for fppf descent of opens (blueprint: lem-trf-etale-relation-finding-opens).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restricting a quotient sheaf by an equivalence relation along a flat, locally finitely
presented morphism is representable by an open immersion.
Source: Stacks Project, Spaces, Tag 02WU (lemma-finding-opens)
(blueprint: lem-trf-etale-relation-finding-opens).

Proof:
1. A pair `(u₁, u₂)` of `U'`-points lies in `R'` exactly when `(g u₁, g u₂)` lies in `R`, by
   the fibre-product universal property; the pullback of an equivalence relation along a
   function is one, so both presheaf quotients are pointwise quotients (Tag 02V8).
2. `F' → F` is injective: two local representatives `u', v'` with the same image in `F`
   lift locally to `R` by lem-trf-etale-relation-kernel-pair, hence to `R'`
   (lem-weil-pbc-site-sheafification-sections-local; Tag 045Z).
3. Put `E = U' ×_{g,U,s} R` and `p = t ∘ pr_R : E → U`. The projection `E → R` is a base
   change of `g`, so `p` is flat and locally of finite presentation by base change
   and composition; its image `W ⊂ U` is open (lem-weil-pbc-flat-lfp-open).
4. For `v : V → U`, the base change `D = E ×_W v⁻¹(W) → v⁻¹(W)` is a one-member fppf
   covering. On `D` the point `(u', r)` of `E` has `s r = g u'` and `t r = v`, so the
   images of `g u'` and `v` in `F` agree; hence `v⁻¹(W) → F` factors through `F'`.
5. Conversely, if `v ∘ z` lifts to `F'`, then locally `(b_k, r_k)` gives a map to `E`
   over `v ∘ z`, so `z` factors through `v⁻¹(W)`. Steps 4 and 5 identify
   `h_V ×_F F'` with `h_{v⁻¹(W)}`.
6. For arbitrary `a : h_T → F`, choose an fppf cover `T_i → T` with representatives
   `a_i : T_i → U`; the opens `W_i = a_i⁻¹(W)` agree on the overlaps `T_i ×_T T_j`.
7. Every fppf covering is an fpqc covering: flatness is given, and images of affine opens
   are open and cover each affine of `T` by quasi-compactness (Tag 022C).
8. By lem-weil-pbc-open-subscheme-fpqc-descent the `W_i` descend to an open `W_T ⊂ T`;
   representables are fppf sheaves (lem-weil-pbc-fpqc-representable-descent), so `W_T`
   represents `h_T ×_F F'` and `W_T → T` is an open immersion (Tags 02WU, 03N0). -/
theorem etale_relation_finding_opens
    {S : Scheme.{u}} {R U U' : Over S} (s t : R ⟶ U)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Surjective s.left] [Flat s.left] [LocallyOfFinitePresentation s.left]
    [Surjective t.left] [Flat t.left] [LocallyOfFinitePresentation t.left]
    (g : U' ⟶ U) [Flat g.left] [LocallyOfFinitePresentation g.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k))
    (F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η' : coequalizer
      (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
      (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g)) ⟶ F'.obj)
    (hη' : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F'.obj ⟶ G.obj ↦ η' ≫ k)) :
    ∃ α : F'.obj ⟶ F.obj,
      (coequalizer.π (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
          (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g)) ≫ η') ≫ α =
        yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ p ↦ IsOpenImmersion p.left) α := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
