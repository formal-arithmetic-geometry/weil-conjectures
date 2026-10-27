module

public import Sheaf.AlgebraicGeometry.RelativeIsomGraphClassification
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import Mathlib.CategoryTheory.Yoneda

/-!
# Zariski gluing of isomorphism graph representatives

Source: Stacks Project, schemes.tex, Tags 01JB, 01JC, 01JJ, 01JP, 01KT and 01KU;
morphisms.tex, Tag 01TQ; moduli-curves.tex, Tag 0DSQ
(blueprint: lem-sfb-isom-graph-representatives-zariski-gluing).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Separated finitely presented local graph representatives of relative isomorphisms
glue over an arbitrary Zariski cover, preserving graphs and inverse projections.

Source: Stacks, Tags 01JB, 01JC, 01JJ, 01JP, 01KT, 01KU and 01TQ; Tag 0DSQ
(blueprint: lem-sfb-isom-graph-representatives-zariski-gluing).

Proof:
1. Pull the cover of T back to X_T and Y_T. Glue the forward maps and inverse maps
   by lem-weil-pbc-scheme-morphism-gluing. Their composites and structure maps agree
   on the covers, so morphism uniqueness gives the inverse identities and uniqueness.
2. Maps to J_i factor uniquely over U_i because its inclusion is monic. The pullback
   of this subfunctor at a point of F(T) is represented by T ×_S U_i. Its projection
   is open by lem-weil-pbc-open-immersion-base-change, and these opens cover T.
3. The given bijections identify both overlap representatives with F on the overlap.
   Yoneda full faithfulness (lem-galois-yoneda-fully-faithful) produces the transition
   isomorphisms. They preserve the classified isomorphism. Yoneda faithfulness proves
   the identity and triple-overlap cocycle equations.
4. Apply lem-galois-glue to obtain J over S and its base-open charts. Their inclusions
   are base changes of the U_i inclusions and cover J.
5. The local universal elements agree by step 3 and glue by step 1. Pulling the global
   element back defines the global bijection. Conversely local classifying maps glue
   uniquely by morphism gluing. This gives naturality and the prescribed local maps.
6. Apply lem-sfb-separated-lfp-target-open-locality and
   lem-pc-quasi-compact-local-on-target to the charts. Separatedness gives
   quasi-separatedness (lem-pc-separated-quasi-separated), hence finite presentation.
7. The graph (1,f) is a section of the separated projection, so it is closed by
   lem-weil-pbc-separated-base-change and lem-weil-pbc-section-separated-closed-immersion.
   For a closed j with invertible projections, j composed with inverse(p_X) equals
   (1,inverse(p_X) followed by p_Y), by the pullback universal property. Thus the
   graph ideals agree. Steps 3 and 5 preserve this isomorphism and its graph both ways.
8. For every B to S, the map/pullback adjunction gives the representing bijection on B.
   Reassociate the family pullbacks by their projections. Pullback of (1,f) is
   (1,pullback(f)); closed immersions survive pullback by
   lem-weil-pbc-closed-immersion-base-change. The inverse identities pull back, so
   uniqueness of inverses gives the same inverse-projection formula. No test scheme,
   base change, or cover is required to be Noetherian, quasi-compact, or finite. -/
theorem exists_isom_graph_representatives_zariski_gluing
    {S X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) [IsSeparated x] [IsSeparated y]
    (I : Type v) (U : I → Scheme.{u}) (b : ∀ i : I, U i ⟶ S)
    [∀ i : I, IsOpenImmersion (b i)]
    (hcover : ∀ s : S, ∃ (i : I) (t : U i), b i t = s)
    (Jᵢ : ∀ i : I, Over (U i))
    [∀ i : I, IsSeparated (Jᵢ i).hom]
    [∀ i : I, LocallyOfFinitePresentation (Jᵢ i).hom]
    [∀ i : I, QuasiCompact (Jᵢ i).hom] [∀ i : I, QuasiSeparated (Jᵢ i).hom]
    (eᵢ : ∀ (i : I) (T : Over (U i)),
      (T ⟶ Jᵢ i) ≃ relativeIsomorphisms x y ((Over.map (b i)).obj T))
    (hnatural : ∀ (i : I) (T' T : Over (U i)) (h : T' ⟶ T) (a : T ⟶ Jᵢ i),
      RelativeIsomorphisms.Restricts ((Over.map (b i)).map h)
        (eᵢ i T' (h ≫ a)) (eᵢ i T a))
    (hgraphs : ∀ (i : I) (T : Over (U i)),
      IsRelativeIsomGraphClassification (eᵢ i T)) :
    IsRelativeIsomZariskiSheaf.{u, w} x y ∧
      ∃ (J : Over S) (E : RelativeIsomGraphRepresentation x y J),
        IsSeparated J.hom ∧ LocallyOfFinitePresentation J.hom ∧
        QuasiCompact J.hom ∧ QuasiSeparated J.hom ∧
        ∃ j : ∀ i : I, (Over.map (b i)).obj (Jᵢ i) ⟶ J,
          (∀ i : I, IsOpenImmersion (j i).left ∧
            IsPullback (j i).left (Jᵢ i).hom J.hom (b i)) ∧
          (∃ χ : ∀ i : I, (Over.pullback (b i)).obj J ≅ Jᵢ i,
            ∀ i : I, (χ i).hom.left ≫ (j i).left = pullback.fst J.hom (b i)) ∧
          (∀ (i : I) (T : Over (U i)) (a : T ⟶ Jᵢ i),
            E.equiv ((Over.map (b i)).obj T) ((Over.map (b i)).map a ≫ j i) =
              eᵢ i T a) ∧
          (∀ (i : I) (T : Over S) (ξ : relativeIsomorphisms x y T),
            IsOpenImmersion (pullback.snd (j i).left ((E.equiv T).symm ξ).left) ∧
            ∃ c : pullback (j i).left ((E.equiv T).symm ξ).left ≅
                pullback T.hom (b i),
              c.hom ≫ pullback.fst T.hom (b i) =
                pullback.snd (j i).left ((E.equiv T).symm ξ).left ∧
              c.hom ≫ pullback.snd T.hom (b i) =
                pullback.fst (j i).left ((E.equiv T).symm ξ).left ≫ (Jᵢ i).hom) ∧
          (∀ (B : Scheme.{u}) (b' : B ⟶ S),
            ∃ EB : RelativeIsomGraphRepresentation (pullback.snd x b') (pullback.snd y b')
                ((Over.pullback b').obj J),
              ∀ (T : Over B) (a : T ⟶ (Over.pullback b').obj J),
                (relativeIsomBaseChangeIso x b' T).hom ≫
                    (E.equiv ((Over.map b').obj T)
                      (((Over.mapPullbackAdj b').homEquiv T J).symm a)).hom.left =
                  (EB.equiv T a).hom.left ≫ (relativeIsomBaseChangeIso y b' T).hom ∧
                (relativeIsomBaseChangeIso y b' T).hom ≫
                    (E.equiv ((Over.map b').obj T)
                      (((Over.mapPullbackAdj b').homEquiv T J).symm a)).inv.left =
                  (EB.equiv T a).inv.left ≫ (relativeIsomBaseChangeIso x b' T).hom ∧
                relativeIsomGraph (EB.equiv T a) ≫
                    relativeIsomGraphBaseChangeMap x y b' T =
                  (relativeIsomBaseChangeIso x b' T).hom ≫
                    relativeIsomGraph (E.equiv ((Over.map b').obj T)
                      (((Over.mapPullbackAdj b').homEquiv T J).symm a))) := by
  sorry

end AlgebraicGeometry
