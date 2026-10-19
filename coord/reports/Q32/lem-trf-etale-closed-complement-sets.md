## Worker report

The module `Sheaf.TraceFormula.EtaleClosedComplementSets` defines the canonical set-valued
small-étale direct image `AlgebraicGeometry.etaleSetDirectImage`, inverse image
`AlgebraicGeometry.etaleSetInverseImage`, and their concrete adjunction
`AlgebraicGeometry.etaleSetAdjunction`.  It states
`AlgebraicGeometry.etaleClosedComplementSets` for a closed immersion `i : Z ⟶ X`.

The Lean statement renders the node clause by clause:

- `(etaleSetDirectImage i).Full` and `(etaleSetDirectImage i).Faithful` state full
  faithfulness of `i_*` on sheaves of sets.
- For every `F : Sheaf X.smallEtaleTopology (Type (u + 1))`,
  `(etaleSetDirectImage i).essImage F ↔ Nonempty (IsTerminal
  ((etaleSetInverseImage (i.openComplement.ι)).obj F))` states exactly the essential-image
  characterization on the canonical open complement `i.openComplement.ι`.
  `Nonempty (IsTerminal ...)` is the proposition that the restriction is a terminal sheaf,
  since `Limits.IsTerminal` itself is a witness structure.
- For every `G : Sheaf Z.smallEtaleTopology (Type (u + 1))`,
  `IsIso ((etaleSetAdjunction i).counit.app G)` states that the counit
  `i^{-1} i_* G → G` is an isomorphism.

The helper definitions use the recorded concrete set-sheaf constructions.  The direct image
is `MorphismProperty.Over.pullback @Etale ⊤ i` followed by
`Functor.sheafPushforwardContinuous`; the inverse image is the corresponding
`Functor.sheafPullbackConstruction.sheafPullback`; and the adjunction is
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`.  The recorded dependency
`lem-weil-pbc-sets-etale-inverse-image-composition-units` supplies the set-valued adjunction,
unit formulas, and composition comparisons.  `def-trf-geometric-morphism` is imported for
the geometric-morphism interpretation.  Schemes, closed immersions, and small étale sites
use the recorded Mathlib declarations `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsOpenImmersion`, and
`AlgebraicGeometry.Scheme.smallEtaleTopology`.

I checked edge cases before writing the statement: `Z = ∅`, `U = ∅`, and `X = ∅`; the
canonical complement remains well typed.  Nilpotent/nonreduced closed subschemes are allowed
by `[IsClosedImmersion i]`.  No reducedness, finiteness, Noetherian, or nonemptiness
hypothesis is introduced.  Empty stalks on `Z` are not identified with terminal singleton
stalks; only the restriction to the open complement is terminal.

Searches made:

- `msearch.py ... leanfinder "closed immersion small etale sheaves of sets pushforward fully faithful essential image terminal complement"` returned étale-site forgetful functors and `smallEtaleTopology`, but no closed-immersion set-sheaf theorem.
- `msearch.py ... loogle "sheafPushforwardContinuous, sheafPullbackConstruction, IsClosedImmersion"` returned zero hits (the service did not expose these names in that query).
- `msearch.py ... grep "openComplement|essImage.*upperStar|lowerStar.*essImage" Mathlib/AlgebraicGeometry` returned zero hits.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf` found only the abelian/coefficient versions and the generic set-valued inverse-image composition theorem; no declaration of this complete statement.
- The source declarations were read through `scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` and the framework files
  `SixFunctors/Etale/UpperLowerStar/Defs.lean` and
  `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.

The source statement is accepted unchanged; there is no `STATEMENT-DISPUTED` flag and no
statement correction.

## Second reading by Q32

I reread the node statement and the module.  The hypotheses are exactly a morphism of schemes
`i : Z ⟶ X` with `[IsClosedImmersion i]`; no extra hypotheses are present.  The object types
are the small étale sheaf categories with coefficients `Type (u + 1)`, so they are sheaves of
sets.  The open complement is the canonical `i.openComplement.ι`, whose range is the
complement of the closed immersion range by `Scheme.Hom.range_eq_compl_range_openComplement_ι`.
The three conjunction clauses correspond respectively to full faithfulness, the exact
terminal-restriction essential image, and the actual counit of the concrete adjunction.
The `Nonempty` wrapper is necessary because `Limits.IsTerminal` is a witness structure rather
than a proposition.  All universes are explicit and the module compiled cleanly with
`scompile.py`.
