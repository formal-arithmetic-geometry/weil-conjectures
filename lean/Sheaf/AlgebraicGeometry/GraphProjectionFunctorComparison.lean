module

public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
import WeilConjectures.Mathlib.CategoryTheory.Yoneda

/-!
# Graph recovery, open functor comparison, and universal evaluation

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B, lemma-Mor-into-Hilb and
lemma-Mor-into-Hilb-open (blueprint: lem-sfb-graph-projection-functor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.RelativeGraphComparison

/-- The first projection restricted to a closed family, using the existing graph ambient.
Source: Stacks Project, quot.tex, Tag 0D1B
(blueprint: lem-sfb-graph-projection-functor-comparison). -/
noncomputable def first {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S) (T : Over S)
    (D : (pullback (pullback.fst z x ≫ z) T.hom).IdealSheafData) :
    D.subscheme ⟶ pullback T.hom z :=
  D.subschemeι ≫ graphFirstProjection z x T

/-- The second projection of a closed family, composed with `X_T ⟶ X`.
Together with the structure map to `T`, this determines the second projection to `X_T`.
Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-graph-projection-functor-comparison). -/
noncomputable def second {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S) (T : Over S)
    (D : (pullback (pullback.fst z x ≫ z) T.hom).IdealSheafData) : D.subscheme ⟶ X :=
  D.subschemeι ≫ graphSecondProjection z x T

end AlgebraicGeometry.RelativeGraphComparison

namespace AlgebraicGeometry

open RelativeGraphComparison

/-- Graph recovery and its functorial, open-representability and evaluation consequences.
The injective maps `I T` express that `F(T)` is a collection of closed subschemes, rather
than closed subschemes with additional labels. `hI` specifies pullback of those subschemes.

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-graph-projection-functor-comparison).

Proof plan, following the eight DAG steps:
1. On an actual graph the first projection is identity and the second is the given map.
Equal graph subschemes therefore give equal morphisms (def-sfb-relative-morphisms-presheaf,
def-pc-fibre-product).
2. For an invertible first projection `k`, the map `k⁻¹ ≫ l` has graph the original closed
subscheme: the inclusions have equal projections, hence agree by the pullback universal
property (def-pc-fibre-product, def-weil-closed-immersion). This also gives uniqueness.
3. Yoneda identifies the fibre product with pairs `(h,f)` satisfying `γ(f) = h*D`.
Forgetting `f` identifies it naturally with the subfunctor where the first projection is
invertible (lem-pc-yoneda, def-pc-representable-functor).
4. An open immersion is a monomorphism, so its functor of points is exactly the maps
factoring through it. The assumed universal open criterion identifies this with the fibre
product, over `h_T` (def-weil-open-immersion, def-pc-open-subfunctor).
5. At a representing universal family, the fibre product with `h_H` is the original
morphism presheaf; consequently its open represents that presheaf, and inclusion represents
`γ` (lem-pc-yoneda, def-pc-representable-functor).
6. The identity point of this representing open is recovered by the inverse first
projection. Naturality identifies its pullback along every test map with the classified
morphism (def-sfb-relative-morphisms-presheaf, def-pc-fibre-product).
7. Pull back the two inverse equations. Pullback uniqueness shows that the inverse and
its composition with the second projection commute with arbitrary base change
(def-pc-fibre-product).
8. Both the pulled-back open and the new universal open represent maps whose composite
factors through the old open. Their two factorization maps are inverse since open
inclusions are monomorphisms (def-pc-fibre-product, def-weil-open-immersion). -/
theorem graph_projection_functor_comparison {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    (F : (Over S)ᵒᵖ ⥤ Type u)
    (I : ∀ T : Over S, F.obj (op T) →
      (pullback (pullback.fst z x ≫ z) T.hom).IdealSheafData)
    (hinj : ∀ T : Over S, Function.Injective (I T))
    (hI : ∀ (T T' : Over S) (h : T' ⟶ T) (D : F.obj (op T)),
      I T' (F.map h.op D) = (I T D).comap (baseChangeMap (pullback.fst z x ≫ z) h))
    (γ : relativeMorphismsPresheaf z x ⟶ F)
    (hγ : ∀ (T : Over S) (f : (relativeMorphismsPresheaf z x).obj (op T)),
      IsClosedImmersion (relativeMorphismGraph z x T f) ∧
        I T (γ.app (op T) f) = (relativeMorphismGraph z x T f).ker) :
    (∀ T : Over S, Function.Injective (γ.app (op T))) ∧
    (∀ (T : Over S) (D : F.obj (op T)),
      (∃ f, γ.app (op T) f = D) ↔ IsIso (first z x T (I T D))) ∧
    (∀ (T : Over S) (D : F.obj (op T)) (e : (I T D).subscheme ≅ pullback T.hom z),
      e.hom = first z x T (I T D) →
        ∃! f : (relativeMorphismsPresheaf z x).obj (op T),
          γ.app (op T) f = D ∧ f.left = e.inv ≫ second z x T (I T D)) ∧
    (∀ (T : Over S) (D : F.obj (op T)),
      ∃ L : Subfunctor (yoneda.obj T),
        (∀ (T' : Over S) (h : T' ⟶ T),
          h ∈ L.obj (op T') ↔ IsIso (first z x T' (I T' (F.map h.op D)))) ∧
        ∃ e : pullback (yonedaEquiv.symm D) γ ≅ L.toFunctor,
          e.hom ≫ L.ι = pullback.fst (yonedaEquiv.symm D) γ) ∧
    (∀ (T : Over S) (D : F.obj (op T)) (e : (I T D).subscheme ≅ pullback T.hom z),
      e.hom = first z x T (I T D) → ∀ (T₀ : Over S) (h : T₀ ⟶ T),
        ∃ (e₀ : (I T₀ (F.map h.op D)).subscheme ≅ pullback T₀.hom z)
          (d : (I T₀ (F.map h.op D)).subscheme ⟶ (I T D).subscheme),
          e₀.hom = first z x T₀ (I T₀ (F.map h.op D)) ∧
          d ≫ (I T D).subschemeι = (I T₀ (F.map h.op D)).subschemeι ≫
            baseChangeMap (pullback.fst z x ≫ z) h ∧
          e₀.inv ≫ d = ((Over.pullback z).map h).left ≫ e.inv ∧
          e₀.inv ≫ second z x T₀ (I T₀ (F.map h.op D)) =
            ((Over.pullback z).map h).left ≫ e.inv ≫ second z x T (I T D)) ∧
    (∀ U : ∀ T : Over S, F.obj (op T) → T.left.Opens,
      (∀ (T : Over S) (D : F.obj (op T)) (T' : Over S) (h : T' ⟶ T),
        IsIso (first z x T' (I T' (F.map h.op D))) ↔
          ∃ a : T'.left ⟶ (U T D).toScheme, a ≫ (U T D).ι = h.left) →
      (∀ (T : Over S) (D : F.obj (op T)),
        ∃ e : pullback (yonedaEquiv.symm D) γ ≅
            yoneda.obj (Over.mk ((U T D).ι ≫ T.hom)),
          e.hom ≫ yoneda.map (Over.homMk (U T D).ι rfl) =
            pullback.fst (yonedaEquiv.symm D) γ) ∧
      ((@IsOpenImmersion : MorphismProperty Scheme.{u}).over (X := S)).presheaf γ ∧
      (∀ (H : Over S) (eH : F.RepresentableBy H),
        ∃ (M : Over S) (i : M ⟶ H)
          (eM : (relativeMorphismsPresheaf z x).RepresentableBy M),
          IsOpenImmersion i.left ∧
          Set.range i.left = (U H (eH.homEquiv (𝟙 H)) : Set H.left) ∧
          (∀ (T : Over S) (a : T ⟶ M),
            eH.homEquiv (a ≫ i) = γ.app (op T) (eM.homEquiv a)) ∧
          ∃ e : (I M (F.map i.op (eH.homEquiv (𝟙 H)))).subscheme ≅ pullback M.hom z,
            e.hom = first z x M (I M (F.map i.op (eH.homEquiv (𝟙 H)))) ∧
            (eM.homEquiv (𝟙 M)).left =
              e.inv ≫ second z x M (I M (F.map i.op (eH.homEquiv (𝟙 H)))) ∧
            (∀ (T : Over S) (a : T ⟶ M),
              (eM.homEquiv a).left =
                ((Over.pullback z).map a).left ≫ (eM.homEquiv (𝟙 M)).left)) ∧
      (∀ (T T₀ : Over S) (h : T₀ ⟶ T) (D : F.obj (op T)),
        U T₀ (F.map h.op D) = h.left ⁻¹ᵁ U T D)) := by
  sorry

end AlgebraicGeometry
