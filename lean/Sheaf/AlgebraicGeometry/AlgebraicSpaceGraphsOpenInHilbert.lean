module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceHilbertFamily
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalIsomorphismOpen

/-! # Graphs form an open subfunctor of the Hilbert functor for algebraic spaces

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-space-graphs-open-in-hilbert).

The two presheaves are specified by their exact values and transition maps. This avoids
choosing a representative of an isomorphism class of closed immersions to define data.
The open pullback square is stated in presheaves using the universe-lifted Yoneda functor;
its representable presheaves have exactly the usual scheme-test morphisms as sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The graph transformation is natural, injective, and representable by open immersions.
Hilbert transitions are inverse images of closed subspaces, specified by cartesian squares.
The morphism transitions are precomposition with the canonical base-change map.
The criterion on every scheme test and the formula recovering the unique morphism are
included. There is no finite-presentation hypothesis on the separated target.

Source: Stacks, quot.tex, Tags 0D1A--0D1B
(blueprint: lem-sfb-space-graphs-open-in-hilbert).

Proof:
1. Use lem-sfb-space-flat-proper-fp-locality to base change the three hypotheses on Z.
   Separatedness of W is preserved by base change, by
   lem-sfb-space-separated-fp-composition. The same permanence holds for each D.
2. The graph is the pullback of the closed relative diagonal of W_T. Closed immersions
   are stable under base change by their scheme-test definition. Its source is Z_T,
   which has all three Hilbert properties by step 1. This also gives Hilbert transitions.
3. By lem-trf-space-fibre-products-etale-covers, graph formation commutes with base change:
   the two projections of the pulled-back graph are the identity and the pulled-back f.
   The same universal property proves identity and composition for both presheaves.
4. If k and l are the projections of D, an inverse of k identifies D with the graph of
   k inverse followed by l. Conversely a graph has invertible first projection. This
   proves the image criterion, unique recovery, and injectivity, after every base change.
5. Apply lem-sfb-space-universal-isomorphism-open to D → Z_T over T. The source is flat,
   locally finitely presented and universally closed; the target is locally of finite
   type, closed and separated, by properness and def-sfb-space-morphism-properties.
   Its open subspace is represented by an open subscheme V of T. No condition on the
   finite presentation of W enters this application.
6. A point of h_T ×_H Mor is a pair (h,f) with graph(f) = h*D. By steps 4--5 this is
   exactly a factorization of h through V, unique since the open inclusion is mono.
   Send a factorization to the inverse-first-projection recovery formula of step 4.
   Base change preserves both inverse equations, so these mutually inverse bijections
   are natural. They give the stated presheaf pullback square. -/
theorem space_graphs_open_in_hilbert {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B)
    (hz_proper : MapIsProper z) (hz_flat : MapIsFlat z)
    (hz_lfp : MapIsLocallyOfFinitePresentation z)
    (hz_qc : MapIsQuasiCompact z.hom.hom)
    (hz_qs : MapIsQuasiCompact (pullback.diagonal z.hom.hom))
    (hw_separated : MapIsSeparated w) :
    ∃ (M H : (SchemeTests B.obj.obj)ᵒᵖ ⥤ Type (u + 1))
      (eM : ∀ T : SchemeTests B.obj.obj, M.obj (op T) ≃ RelativeMorphism z w T)
      (eH : ∀ T : SchemeTests B.obj.obj,
        H.obj (op T) ≃ SpaceHilbertFamily (relativeProductMap z w) T)
      (γ : M ⟶ H),
      (∀ (T' T : SchemeTests B.obj.obj) (h : T' ⟶ T) (f : M.obj (op T)),
        (eM T' (M.map h.op f)).val = relativeSpaceMap z h ≫ (eM T f).val) ∧
      (∀ (T' T : SchemeTests B.obj.obj) (h : T' ⟶ T) (D : H.obj (op T)),
        ∃ d : (eH T' (H.map h.op D)).space ⟶ (eH T D).space,
          IsPullback d (eH T' (H.map h.op D)).inclusion (eH T D).inclusion
            (relativeSpaceMap (relativeProductMap z w) h)) ∧
      (∀ (T : SchemeTests B.obj.obj) (f : M.obj (op T)),
        ∃ e : (eH T (γ.app (op T) f)).space ≅ relativeSpace z T,
          e.hom ≫ relativeSpaceGraph z w T (eM T f) =
            (eH T (γ.app (op T) f)).inclusion) ∧
      (∀ T : SchemeTests B.obj.obj, Function.Injective (γ.app (op T))) ∧
      (∀ (T : SchemeTests B.obj.obj) (D : H.obj (op T)),
        (∃ f : M.obj (op T), γ.app (op T) f = D) ↔ IsIso (eH T D).first) ∧
      (∀ (T : SchemeTests B.obj.obj) (D : H.obj (op T))
          (e : (eH T D).space ≅ relativeSpace z T), e.hom = (eH T D).first →
        ∃! f : M.obj (op T),
          γ.app (op T) f = D ∧ (eM T f).val = e.inv ≫ (eH T D).second) ∧
      (∀ (T : SchemeTests B.obj.obj) (D : H.obj (op T)),
        ∃ (V : SchemeTests B.obj.obj) (j : V ⟶ T), IsOpenImmersion j.left.left ∧
          (∀ (T' : SchemeTests B.obj.obj) (h : T' ⟶ T),
            IsIso (eH T' (H.map h.op D)).first ↔ ∃ a : T' ⟶ V, a ≫ j = h) ∧
          ∃ β : uliftYoneda.{u + 1}.obj V ⟶ M,
            IsPullback β (uliftYoneda.{u + 1}.map j) γ
              (uliftYonedaEquiv.{u + 1}.symm D)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
