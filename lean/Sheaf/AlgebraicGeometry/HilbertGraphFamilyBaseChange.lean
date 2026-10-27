module

public import Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf
public import Sheaf.AlgebraicGeometry.ProperHilbertPresheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage

/-!
# Graph families and arbitrary base change

Source: Stacks Project, quot.tex, Tag 0D1A, lemma-Mor-into-Hilb, graph construction
before the injectivity argument; Tag 0CZY, situation-hilb, base-change paragraph
(blueprint: lem-sfb-hilbert-graph-family-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A proper, flat, finitely presented source and a separated target give closed graph
families and a natural transformation to the proper Hilbert presheaf. Ideal equalities
express equality of closed subschemes under the canonical fibre-product identifications,
including compatibility with identity and composite base changes.

Source: Stacks Project, quot.tex, Tag 0D1A, lemma-Mor-into-Hilb, and Tag 0CZY,
situation-hilb (blueprint: lem-sfb-hilbert-graph-family-base-change).

Proof plan:
1. Base change preserves properness by lem-weil-pbc-proper-fp-permanence, flatness by
   lem-weil-pbc-flat-morphism-base-change, and finite presentation by
   lem-weil-pbc-qcqs-morphism-permanence. The fibre-product universal property identifies
   the graph ambient space with the base change of the product.
2. The diagonal of the base-changed target is the pullback of the original diagonal.
   By lem-weil-pbc-closed-immersion-base-change it is closed, giving separatedness.
3. The actual graph is the pullback of that diagonal, so it is a closed immersion.
   Its first projection is the identity, so its structure map has the properties in
   step 1 and its kernel ideal defines a proper Hilbert family.
4. For an arbitrary family, its pullback is its fibre product over the test scheme.
   The permanence results of step 1 preserve its properties. By
   lem-pc-closed-subscheme-base-change-ideal-image its ideal is the pulled-back ideal,
   without a flatness assumption on the base change.
5. Projection equalities identify the pulled-back graph with the graph of the pulled-back
   morphism. Their kernel ideals agree by def-sbc-closed-immersion-ideal-sheaf, so this is
   equality of closed subschemes, rather than just equality of supports.
6. Uniqueness in def-pc-fibre-product makes identity and iterated comparisons agree.
   Ideal pullback therefore respects identities and composites. The equality of step 5
   is precisely naturality of the transformation with the specified graph components. -/
theorem hilbert_graph_family_base_change {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    [IsProper z] [Flat z] [LocallyOfFinitePresentation z] [IsSeparated x] :
    (∀ T : Over S,
      IsProper (pullback.fst T.hom z) ∧ Flat (pullback.fst T.hom z) ∧
        LocallyOfFinitePresentation (pullback.fst T.hom z) ∧
          IsSeparated (pullback.fst T.hom x)) ∧
    (∀ (T T' : Over S) (h : T' ⟶ T)
        (D : (properHilbertPresheaf (pullback.fst z x ≫ z)).obj (op T)),
      IsProperHilbertFamily (pullback.fst z x ≫ z) T'
        (D.1.comap (baseChangeMap (pullback.fst z x ≫ z) h))) ∧
    ∃ γ : relativeMorphismsPresheaf z x ⟶ properHilbertPresheaf (pullback.fst z x ≫ z),
      (∀ (T : Over S) (f : (relativeMorphismsPresheaf z x).obj (op T)),
        IsClosedImmersion (relativeMorphismGraph z x T f) ∧
          (γ.app (op T) f).1 = (relativeMorphismGraph z x T f).ker) ∧
      (∀ (T T' : Over S) (h : T' ⟶ T)
          (f : (relativeMorphismsPresheaf z x).obj (op T)),
        (relativeMorphismGraph z x T f).ker.comap
            (baseChangeMap (pullback.fst z x ≫ z) h) =
          (relativeMorphismGraph z x T' ((relativeMorphismsPresheaf z x).map h.op f)).ker) ∧
      (∀ (T : Over S)
          (D : (properHilbertPresheaf (pullback.fst z x ≫ z)).obj (op T)),
        D.1.comap (baseChangeMap (pullback.fst z x ≫ z) (𝟙 T)) = D.1) ∧
      (∀ (T T' T'' : Over S) (h : T' ⟶ T) (k : T'' ⟶ T')
          (D : (properHilbertPresheaf (pullback.fst z x ≫ z)).obj (op T)),
        (D.1.comap (baseChangeMap (pullback.fst z x ≫ z) h)).comap
            (baseChangeMap (pullback.fst z x ≫ z) k) =
          D.1.comap (baseChangeMap (pullback.fst z x ≫ z) (k ≫ h))) := by
  sorry

end AlgebraicGeometry
