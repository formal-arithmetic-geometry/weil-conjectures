module

public import Sheaf.AlgebraicGeometry.ProperHilbertPresheaf
public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Graphs form an open subfunctor of the Hilbert functor

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-graphs-open-in-hilbert).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The canonical graph transformation is injective and representable by open immersions.
Its components are specified by the kernel ideals of the actual graph maps. The universal
open locus, recovery by inverse first projection, and the representing-scheme consequence
with universal evaluation are included explicitly.

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: lem-sfb-graphs-open-in-hilbert).

Proof plan: (1) Properness, flatness and finite presentation of `Z_T` follow from
lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-flat-morphism-base-change and
lem-weil-pbc-qcqs-morphism-permanence. Separatedness of `X_T` follows by base change
of its diagonal. The graph is the pullback of this closed diagonal, hence closed,
and its domain has the three required properties. (2) Pullback preserves the families
by those same permanence results. Uniqueness in def-pc-fibre-product identifies the
pullback graph with the graph of the pulled back morphism, proving naturality.
(3) A closed family is a graph exactly when its first projection is invertible:
the inverse followed by its second projection recovers the unique morphism.
(4) Apply lem-sfb-universal-isomorphism-open to `D → Z_T` over `T`: the source is
flat, locally finitely presented and universally closed; the target is separated,
locally of finite type and closed over `T`, by properness. This gives the universal
open locus, without any finiteness hypothesis on `X`. (5) The fibre product of the
morphism functor with `h_T` over Hilbert is `h_U`, by (3) and (4), naturally by (2).
(6) Apply this to the universal family of a representing Hilbert scheme. The inverse
first projection followed by the second is universal evaluation. Pullback preserves
inverse equations and hence evaluation, and the universal test-map criterion shows
that the open locus itself commutes with every base change. -/
theorem graphs_open_in_hilbert {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    [IsProper z] [Flat z] [LocallyOfFinitePresentation z] [IsSeparated x] :
    ∃ γ : relativeMorphismsPresheaf z x ⟶ properHilbertPresheaf (pullback.fst z x ≫ z),
      (∀ (T : Over S) (f : (relativeMorphismsPresheaf z x).obj (op T)),
        IsClosedImmersion (relativeMorphismGraph z x T f) ∧
          (γ.app (op T) f).1 = (relativeMorphismGraph z x T f).ker) ∧
      (∀ T : Over S, Function.Injective (γ.app (op T))) ∧
      ((@IsOpenImmersion : MorphismProperty Scheme.{u}).over (X := S)).presheaf γ ∧
      (∀ (T : Over S)
          (D : (properHilbertPresheaf (pullback.fst z x ≫ z)).obj (op T)),
        ∃ U : T.left.Opens, ∀ (T' : Over S) (h : T' ⟶ T),
          IsIso (((properHilbertPresheaf (pullback.fst z x ≫ z)).map h.op D).1.subschemeι ≫
            graphFirstProjection z x T') ↔
              ∃ a : T'.left ⟶ U.toScheme, a ≫ U.ι = h.left) ∧
      (∀ (T : Over S)
          (D : (properHilbertPresheaf (pullback.fst z x ≫ z)).obj (op T))
          (e : D.1.subscheme ≅ pullback T.hom z),
        e.hom = D.1.subschemeι ≫ graphFirstProjection z x T →
          ∃ f : (relativeMorphismsPresheaf z x).obj (op T),
            γ.app (op T) f = D ∧
              f.left = e.inv ≫ D.1.subschemeι ≫ graphSecondProjection z x T) ∧
      (∀ (H : Over S)
          (eH : (properHilbertPresheaf (pullback.fst z x ≫ z)).RepresentableBy H),
        ∃ (M : Over S) (i : M ⟶ H)
          (eM : (relativeMorphismsPresheaf z x).RepresentableBy M),
          IsOpenImmersion i.left ∧
          (∀ (T : Over S) (a : T ⟶ M),
            eH.homEquiv (a ≫ i) = γ.app (op T) (eM.homEquiv a)) ∧
          ∃ ev : pullback M.hom z ⟶ X,
            ev = (eM.homEquiv (𝟙 M)).left ∧
            (∀ (T : Over S) (a : T ⟶ M),
              (eM.homEquiv a).left = ((Over.pullback z).map a).left ≫ ev)) := by
  sorry

end AlgebraicGeometry
