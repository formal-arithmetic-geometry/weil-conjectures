module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.CategoryTheory.Extensive

/-!
# Local finite-set normal forms for finite diagrams of finite étale schemes

Source: Stacks Project, Fundamental Groups, Tag 0BN9,
`lemma-finite-etale-covers-limits-colimits`, finite-colimits proof; finite-diagram
extension of simultaneous splitting and open refinement
(blueprint: lem-sc-finite-etale-diagram-local-normal-form).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite diagram of finite étale schemes becomes a diagram of finite sets of copies
of the base on an étale covering. The last equality says that each conjugated arrow
is the identity from a source copy to its designated target copy. The sets can vary
between cover members. Source: Stacks Project, Tag 0BN9, finite-colimits proof,
finite-diagram extension (blueprint: lem-sc-finite-etale-diagram-local-normal-form).

Proof:
1. If `Y` is empty, take the empty cover. Otherwise induct on the finitely many objects
   of `I`, starting with the identity cover. Finite étale morphisms remain such after
   base change, as in def-weil-pbc-finite-etale-category.
2. At each step use `finite_etale_etale_local_split` (Stacks 04HN) at every point of
   each current cover member. Replace its finitely many pieces, each isomorphic over
   the new base to that base, by copies of the base. Construct the coproduct isomorphism
   and its inverse summandwise; uniqueness proves they are inverse. Pull back earlier
   trivializations, using lem-sc-etale-fibre-product-base-change-coproduct and the
   universal property of iterated pullbacks (def-pc-fibre-product). Étale composition
   preserves the covering, and every point remains covered.
3. For each arrow and each source sheet, apply `coproductCopiesMorphismsClopen` (a)
   to the conjugated map. This partitions the base into clopen pieces, one for each
   target sheet, and identifies the map on each piece with that sheet's inclusion.
   There are finitely many arrow/source-sheet pairs.
4. Around each point intersect the pieces containing that point for all these pairs.
   This is an open neighbourhood, and the resulting neighbourhoods cover. Open
   immersions are étale and compose with the preceding étale cover. Restricting the
   trivializations gives the required sheet maps. Identity and composition laws follow
   from those of `D`: evaluate the conjugation identities at the chosen point in each
   source copy, and use disjointness of the target copies to identify their labels.
   Empty source sets give vacuous equations; a nonempty source cannot map to an empty
   target over this nonempty neighbourhood.
5. Index by the cover members and their points. Finite induction and set-indexed unions
   give a set of indices, and the covering and restriction equalities give the result.
   An empty diagram requires no object or arrow data. No degree is identified between
   different cover members. -/
theorem finiteEtaleDiagramLocalNormalForm (Y : Scheme.{u})
    {I : Type v} [SmallCategory I] [FinCategory I]
    (D : I ⥤ (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y) :
    ∃ (Λ : Type u) (U : Λ → Scheme.{u}) (a : ∀ l, U l ⟶ Y),
      (∀ l, Etale (a l)) ∧
      (∀ y : Y, ∃ (l : Λ) (x : U l), (a l) x = y) ∧
      ∀ l : Λ, ∃ S : I ⥤ Type u,
        (∀ i : I, Finite (S.obj i)) ∧
        ∃ e : ∀ i : I,
            pullback (D.obj i).hom (a l) ≅ ∐ (fun _ : S.obj i ↦ U l),
          (∀ i : I,
            (e i).hom ≫ Sigma.desc (fun _ : S.obj i ↦ 𝟙 (U l)) =
              pullback.snd (D.obj i).hom (a l)) ∧
          ∀ (i j : I) (f : i ⟶ j) (s : S.obj i),
            Sigma.ι (fun _ : S.obj i ↦ U l) s ≫ (e i).inv ≫
                ((MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ (a l)).map
                  (D.map f)).left ≫ (e j).hom =
              Sigma.ι (fun _ : S.obj j ↦ U l) (S.map f s) := by
  sorry

end AlgebraicGeometry
