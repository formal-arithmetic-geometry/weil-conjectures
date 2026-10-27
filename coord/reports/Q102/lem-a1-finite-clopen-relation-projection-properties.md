## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClopenRelationProjectionProperties`
states `AlgebraicGeometry.finite_clopen_relation_projection_properties` with one
`sorry`. The node's statement, dependencies and proof are unchanged. There are no
new nodes, dependency repairs, statement corrections or disputed statements.

The module also supplies six canonical abbreviations in
`AlgebraicGeometry.FiniteClopenRelation`, belonging to this node:

- `baseChangeEndpoint`: Mathlib's `pullback.map` on the endpoint and identity maps
  on the new base and the original base. This is the induced endpoint `s_B` or `t_B`.
- `restriction`: first form `A = pullback V.ι s_B`, then
  `pullback (pullback.snd V.ι s_B ≫ t_B) V.ι`. This is precisely
  `C = V ×_{U_B,s_B} R_B ×_{t_B,U_B} V`, with its full scheme structure.
- `source`: the first projection to `A`, followed by the first projection `A → V`.
- `target`: the second projection of the last pullback, to `V`.
- `toRelation`: the first projection to `A`, followed by its second projection to `R_B`.
- `toSquare`: `pullback.lift source target` into `V ×_B V`. Its compatibility is
  proved directly by the two pullback conditions and the fact that each
  `baseChangeEndpoint` preserves the projection to `B`. No auxiliary theorem is
  postponed, and no chosen arbitrary map or existence witness is used.

All variables and universes are explicitly bound, with `autoImplicit false` and
`Scheme.{u}` throughout. No file-local notation, private definition or statement
`let` is used. All data are real constructions. Every declaration has its own
source/blueprint docstring; the theorem docstring contains the five proof steps.

Clause-by-clause rendering of the hypotheses and conclusion:

| Node text | Lean rendering |
| --- | --- |
| Schemes `T,U,R,B` | `(T U R B : Scheme.{u})` |
| The three structure morphisms to `T` | `(fU : U ⟶ T) (fR : R ⟶ T) (fB : B ⟶ T)` |
| `s,t` are `T`-morphisms | `(s t : R ⟶ U)` with `hs : s ≫ fU = fR` and `ht : t ≫ fU = fR` |
| Both endpoints are étale | `[Etale s] [Etale t]` |
| The canonical pair `j=(s,t)` is closed | `[IsClosedImmersion (pullback.lift s t (hs.trans ht.symm))]` |
| `U_B=U×_T B`, `R_B=R×_T B` | Mathlib `pullback fU fB`, `pullback fR fB` |
| Induced endpoint maps | `baseChangeEndpoint fU fR fB s hs` and the corresponding expression for `t` |
| `V` is open and closed with induced scheme structure | `V : (pullback fU fB).Opens`, `_hV : IsClosed (V : Set (pullback fU fB : Scheme.{u}))`; its scheme is `V.toScheme`, inclusion `V.ι` |
| `V→B` is finite | `[IsFinite (V.ι ≫ pullback.snd fU fB)]` |
| `C` and its canonical endpoint maps | `restriction`, `source`, `target` as described above |
| `C→V×_B V` is a closed immersion | `IsClosedImmersion (toSquare fU fR fB s t hs ht V)` |
| That same map is finite | `IsFinite (toSquare fU fR fB s t hs ht V)` |
| `V×_B V` is finite over `B` | `IsFinite (pullback.fst (V.ι ≫ pullback.snd fU fB) (V.ι ≫ pullback.snd fU fB) ≫ V.ι ≫ pullback.snd fU fB)` |
| `C→B` is finite | `IsFinite (toRelation fU fR fB s t hs ht V ≫ pullback.snd fR fB)` |
| The canonical `C→R_B` is an open immersion | `IsOpenImmersion (toRelation fU fR fB s t hs ht V)` |
| Its image is the stated intersection | Equality of `Set.range toRelation` with `s_B ⁻¹' V ∩ t_B ⁻¹' V`, written out with both induced endpoints |
| This image is open and closed | `IsClopen (Set.range (toRelation fU fR fB s t hs ht V))` |
| Both restricted endpoints are étale | Final conjuncts `Etale (source ...) ∧ Etale (target ...)` |
| No equivalence-relation hypothesis | No reflexivity, symmetry, transitivity or groupoid data are bound |

Dependency declarations used, with the recorded signatures and docstrings read
in the pinned source:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; `Scheme` extends a locally ringed space with
  local affine charts, and its morphisms are locally ringed space morphisms.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; affine-locally étale ring maps.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; closed embedding with
  surjective stalk maps.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `.lift`, `.map` and `.condition`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies the scheme pullback instances.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`. The actual induced open subscheme
  and inclusion are Mathlib's `Scheme.Opens.toScheme` and `Scheme.Opens.ι`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; affine with finite ring maps on
  affine opens. The node's integral notion is not needed in this statement.

The proof dependencies are all Mathlib leaves: closed-immersion base change,
closed immersion implies finite, finite base change and composition,
open-immersion base change, and étale base change and composition. Their modules
are already imported publicly because they also provide the statement's notions.
No extra project module is needed for these proof leaves.

Source read: `literature/stacks-project/more-groupoids.tex`,
`lemma-quasi-finite-over-base-j-proper` (Tag 03X5), including the inverse image
of `U' ×_{S'} U'` and the explanation that this object square is finite over `S'`.
The five accepted DAG proof steps supply the closed-immersion specialization and
étale permanence. The nearby blueprint lineage is `lem-a1-affine-hc0`; the current
blueprint is consulted under `literature/blueprint/latest/`, not an old snapshot.
The original example CompactObject module is now withdrawn; its node points to
`WeilConjectures.CategoryTheory.CompactObject`, whose active module/header and
record were read as well.

Edge cases checked mathematically before writing:

- `V=∅`: its induced scheme, both pullbacks and their images are empty; all finite,
  immersion and étale conclusions retain their usual meanings.
- `R=∅`: the same empty restricted arrow scheme is covered with arbitrary `V`.
- Empty base or empty ambient schemes are not excluded by nonemptiness assumptions.
- Nonreduced finite `V` and a diagonal relation retain their nilpotents because
  `C` and the square use scheme pullbacks, not products of underlying sets.
- `V=U_B` is covered whenever its structure map is finite.
- No separation, noetherian, flatness-of-the-base-change or relation axioms have
  been added. A pair of unrelated étale arrows satisfying the closed-pair
  hypothesis is included.

Searches run for existing statements and constructions:

- `msearch.py leansearch`, query `Finite clopen restriction of an etale closed scheme relation`:
  eight hits, including `Scheme.Opens.toScheme`, `IsClopen`, `Scheme.Opens.stalkIso`
  and `IsFinite.instMorphismRestrict`; no whole-statement match.
- `msearch.py leanfinder`, query `A closed scheme relation restricted to a finite clopen open subscheme is finite over the base and has etale endpoint projections`:
  eight hits, including `Scheme.Etale`, `IsFinite` and étale permanence interfaces;
  no whole-statement match. Some search-service names use deprecated `IsEtale`;
  the pinned source and compiler confirm that the recorded current class is `Etale`.
- `msearch.py loogle`, query `"IsClosedImmersion", "IsFinite"`:
  three hits (`IsFinite.instOfIsClosedImmersion`,
  `IsClosedImmersion.iff_isFinite_and_mono`, `.eq_isFinite_inf_mono`), which give an
  ingredient, not this conjunction concerning the restricted relation.
- `msearch.py grep`, query
  `[Rr]elation.*[Ii]sFinite|[Rr]estrict.*[Ii]sEtale|[Ii]sEtale.*[Rr]estrict`
  in `AlgebraicGeometry`: no hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, with patterns including
  `finite-clopen`, `clopen-relation`, `IsClosedImmersion.*IsFinite`,
  `IsFinite.*IsEtale`: nearby permanence and other clopen constructions only;
  no existing statement matching all the node's clauses.
- Exact identifier/node searches in both source trees and
  `dag/lean_names_upstream.json` for
  `lem-a1-finite-clopen-relation-projection-properties`, `FiniteClopenRelation`
  and `finite_clopen_relation_projection_properties`: no hits.
- Read Mathlib's actual `pullback`, projections, lift, map, finite and étale
  permanence declarations; reuse those constructions rather than redefine them.

Validation: `scompile.py Q102 lem-a1-finite-clopen-relation-projection-properties`
compiled the entire final module in sandbox and library mode against the live
published server build, with no errors or non-sorry warnings. The final theorem
is the only postponed proof. The canonical-square compatibility proof is real
and the definitions have no `sorry` dependency.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
