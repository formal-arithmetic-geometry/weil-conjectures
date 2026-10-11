## Worker report

The module states `AlgebraicGeometry.proper_flat_rightAdjoint_restriction_open`. It binds a cartesian square `g : Y' ⟶ Y`, a proper, flat, locally finitely presented morphism `f`, derived categories, and right adjunctions `adjf` and `adjf'`. For every quasi-compact open `V` (respectively `V'`) and every right adjoint `aV` (respectively `aV'`) to the corresponding restricted direct-image functor, it states existence of a natural transformation from the restricted right adjoint to the right adjoint after restriction, whose component is an isomorphism for every derived object. The first conjunct uses `f ⁻¹ᵁ V`; the second uses `(pullback.snd f g) ⁻¹ᵁ V'`, matching the two open restrictions in the node. The final `IsIso` clauses render the two restriction-isomorphism conclusions and the existential natural transformations render the canonical comparison maps represented at this abstraction level.

Hypotheses render as follows: `g` and `f` are explicit morphisms; `[CompactSpace]` and `[QuasiSeparatedSpace]` bind the qcqs scheme hypotheses; `[IsProper f]`, `[Flat f]`, and `[LocallyOfFinitePresentation f]` bind properness, flatness, and finite presentation; `schemeDerivedCategory` supplies the quasi-coherent derived-category ambient used by the recorded project declarations; `adjf` and `adjf'` state that `a` and `a'` are right adjoints to the derived direct images. Each open clause binds `IsCompact (V : Set Y)` or `IsCompact (V' : Set Y')`, a restricted direct-image functor `F_V`/`F_V'`, and its right adjoint. The transformations have types `a ⋙ restriction_X ⟶ restriction_Y ⋙ aV` and `a' ⋙ restriction_X' ⟶ restriction_Y' ⋙ aV'`, and each component is required to be `IsIso`.

Dependencies used: `Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint` (scheme derived direct image and derived-category declarations), `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` (`schemeOpenRestriction`), and Mathlib proper, flat, and finite-presentation morphism classes. Fibre products use Mathlib `CategoryTheory.Limits.pullback` as recorded by `def-pc-fibre-product`; derived categories and direct images use the recorded declarations for `def-pc-derived-category` and `def-pc-derived-direct-image`.

Edge cases checked: the quantification over all quasi-compact opens includes the empty open and the whole base; no nonemptiness or positivity assumptions are imposed; the square permits identity and empty fibre products; all universes are explicit and the same universe is used for schemes and derived categories.

Searches: `msearch.py ... leanfinder "proper flat pushforward right adjoint commutes with restriction to quasi compact opens"` found only generic module restriction adjunctions and no derived quasi-coherent theorem; `msearch.py ... loogle "CategoryTheory.mateEquiv, AlgebraicGeometry.schemeDerivedDirectImage"` returned no hits (unknown identifier); `msearch.py ... grep "rightAdjoint.*[Rr]estrict|[Rr]estrict.*rightAdjoint"` found no project theorem; repository `rg` found no declaration for this node. The Stacks source was checked at Tag 0E4J, Lemma 48.12.2, lines 23–28.

No `STATEMENT-DISPUTED` flag.

## Earlier second reading (a previous round; superseded)

The statement and module were reread after compilation. The first conjunct matches the open `V` clause and the second matches the base-changed open `V'` clause; the componentwise `IsIso` conditions render the two isomorphism conclusions. The module compiles cleanly with only the expected `sorry` proof warning.

## Second reading by U1

The node introduces: (1) a morphism `g : Y' ⟶ Y` of qcqs schemes; (2) a proper,
flat, finitely presented morphism `f : X ⟶ Y`; (3) the pullback `X' = X ×_Y Y'`,
with its projections; (4) right adjoints `a` and `a'` to the derived direct images
of `f` and the base-changed morphism; (5) for every quasi-compact open `V ⊂ Y`,
the restricted morphism and its right adjoint, together with the isomorphism
`j_X^* a(K) ≅ a_V(Lj^*K)` for every `K`; (6) the analogous clause for every
quasi-compact `V' ⊂ Y'`; and (7) compatibility of the base-change construction
with these restrictions.

The Lean renders (1) as `(g : Y' ⟶ Y)` with `[CompactSpace Y]`,
`[QuasiSeparatedSpace Y]`, and the corresponding instances for `Y'`; (2) as
`(f : X ⟶ Y)` with `[IsProper f] [Flat f] [LocallyOfFinitePresentation f]`;
(4) as `a`/`adjf` and `a'`/`adjf'`; (5) as quantification over
`V : Y.Opens`, `IsCompact (V : Set Y)`, the canonical restricted morphism
`morphismRestrict f V`, and an adjunction
`schemeDerivedDirectImage (morphismRestrict f V) ⊣ aV`; and (6) identically
with `morphismRestrict (pullback.snd f g) V'`. The existential natural
transformations have exactly the restriction functor types, and all components
are required to be `IsIso`. The shared `HasDerivedCategory` binder supplies the
ambient derived categories for schemes and opens. Empty opens and identity maps
are included, and no nonemptiness or characteristic assumption is introduced.

I found two mismatches in the worker module. It imposed `[CompactSpace X] [QuasiSeparatedSpace X]`,
which are not hypotheses of the node (they follow from the proper qcqs setup but
must not be added as statement assumptions), and it quantified arbitrary functors
`F_V` and `F_V'`, so the adjunctions did not identify the restricted derived direct
images required by the source. I removed the two `X` instances and replaced each
arbitrary functor by the canonical `schemeDerivedDirectImage (morphismRestrict …)`.
The module then compiled cleanly with only the expected `sorry` warning. Searches
of Mathlib and the source checkout found no existing declaration for this theorem;
`schemeOpenRestriction`, `schemeDerivedDirectImage`, and `morphismRestrict` are the
recorded project declarations used.

## Stage-2 review fix (R-fro)

The delivered statement took `a`, `a'` as right adjoints of `schemeDerivedDirectImage` on the full
`D(O_X)` and concluded with an untied `∃ τ, ∀ K, IsIso (τ.app K)` over all of `D(O_Y)`. The node
(and Stacks 0E4J) speaks of right adjoints on `D_QCoh` and of the canonical map
`j_U^* a(K) → a_V(Lj^* K)` for `K ∈ D_QCoh(Y)`. Restated: `a`, `a'` in the landed binder form
`(F, hF, a, adj)` of proper_flat_rightAdjoint_open_support / _preservesDirectSums on
`schemeDerivedQCohCategory`; the conclusion is the landed rendering of the canonical open-square
map of rightAdjoint_open_support_criterion (Stacks equation-sheafy: the map is an isomorphism at
K iff `a(K → Rj_* j^* K)|_U` is), with `schemeOpenRestriction` for the restrictions, for every
quasi-compact `V ⊆ Y` (f) and `V' ⊆ Y'` (f' = pullback.snd f g). The free `a_V` binders are gone.
