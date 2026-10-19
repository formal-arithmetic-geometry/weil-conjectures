## Worker report

Delivered module: `Sheaf.CategoryTheory.SiftedNerveIndexCalculus`.
Main declaration: `SSet.Enhanced.SiftedIndex.sifted_nerve_index_calculus`.
All seven helpers have real definitions. The only postponed proof is the main
named theorem; its docstring reproduces all eleven proof steps of the DAG node.
The natural-language statement, proof and proof dependencies are unchanged.

The module uses the existing coherent nerve of small Kan complexes, the existing
coherent colimit-functor presentation, and the existing definition of preservation
of limiting cones. It does not introduce another definition of siftedness.
The theorem directly states equivalence between the finite-product condition and
the nonempty/final-diagonal condition.

### Hypotheses and clauses

- Universes and infinity categories: `K : SSet.{u}` with `[Quasicategory K]`.
  Spaces are `CategoryTheory.Spaces.infinityCategory.{u}` in universe `u + 1`.
  The containing universe is `max (u + 1) v`; the extra `v` remains arbitrary.
  `SSet.uliftFunctor` transports the small shape into that universe. There is no
  equality imposed between the small and containing universes.
- The colimit functor on spaces is the existing `Spaces.InterchangeColimit`.
  Its functor and its coherent unit are actual data, and its `universal` field
  states that each unit component is the supplied colimiting cocone.
  The theorem concludes `Nonempty` of this presentation for every small `K`.
  Thus the quantifier over colimit presentations in the next clause is not vacuous.
- “Colimit preserves finite products” is `PreservesFiniteProducts L`:
  `∀ n, PreservesLimitsOfShape L.functor` on the constant simplicial set
  `ULift (Fin n)`. This uses the existing `PreservesLimitsOfShape`, which fixes
  the whole image cone, including its apex, projections and higher homotopies.
  Testing all `Fin n` is equivalent to testing all finite sets. `Fin 0` is included.
- Equivalence with nonemptiness and final diagonal is the first `↔`:
  `PreservesFiniteProducts L ↔ Nonempty (K _⦋0⦌) ∧ IsFinal (lift (𝟙 K) (𝟙 K))`.
  `lift` is the existing cartesian pairing into the degreewise binary product.
- Finality is the helper `IsFinal`: for every containing quasicategory `E`, every
  diagram `P` on the target, and every supplied colimiting cocone `p`, its actual
  restriction `gluingCoconeRestrict` is colimiting. There is no assumption of
  cocompleteness or existence of other colimits on `E`.
- Weak contractibility is `IsContractible K`, the recorded definition saying that
  `K → Δ[0]` is a weak homotopy equivalence. By the recorded groupoid-localization
  interface this says exactly that localization at all arrows is the point.
  It is not an assertion that the original category is equivalent to the point.
- For every integer `n ≥ 0`, `∀ n : ℕ, IsFinal (diagonal K n)`.
  The codomain is the already defined `Algebroid.power K n` and the diagonal
  repeats each simplex in all coordinates. For zero coordinates this is the
  terminal simplicial set, so the nullary finality assertion is present explicitly.
- The ordinary nerve case binds `I : Type u` and `[SmallCategory I]` and assumes
  the same nonempty/final-diagonal condition for `nerve I`, already identified
  with the space-colimit condition by the first part of the theorem.
- The ordinary conclusions are `Nonempty I`, `IsConnected I`, and, for every `n`,
  `(Functor.pi' (fun _ : Fin n ↦ 𝟭 I)).Final`. This is the actual diagonal functor
  into the Mathlib dependent product category, including the terminal empty product.
  Mathlib `Functor.Final` is the connected-under-comma criterion, equivalently
  preservation of ordinary colimits by restriction.
- Ordinary comparison: `C : Fin n → Type v` and `E : Type v` have categories with
  independent hom universe `w`, and each admits `u`-small colimits through
  `HasColimitsOfSize.{u,u}`. `F : (∀ a, C a) ⥤ E` is an arbitrary functor.
  The hypothesis `∀ a x, PreservesColimitsOfSize (ordinaryInsertion C x a ⋙ F)`
  states exactly separate colimit preservation, using the actual insertion that
  varies coordinate `a` and fixes every other coordinate. The unused fixed value
  in coordinate `a` causes no restriction: cocompleteness supplies an initial object
  in that category. All the other fixed objects are arbitrary.
- For every family `X : ∀ a, I ⥤ C a`, the conclusion is
  `IsIso (colimit.desc (Functor.pi' X ⋙ F) (ordinaryCocone F X))`.
  `ordinaryCocone` has apex `F.obj (fun a ↦ colimit (X a))` and leg at `i`
  `F.map (fun a ↦ colimit.ι (X a) i)`. Thus `colimit.desc` is precisely the
  displayed canonical map, not an unspecified isomorphism between its endpoints.
- Coherent comparison: `C : Fin n → SSet.{max (u+1) v}` and `E` are arbitrary
  quasicategories. `Presentability.HasSmallColimits.{u,...}` supplies exactly
  their small coherent colimits. `F : ∏ᶜ C ⟶ E` is a simplicial functor.
  `Presentability.PreservesColimitsIn (insertion C x a ≫ F)` with the predicate
  `Presentability.IsSmall.{u,...}` states separate preservation of every small
  colimiting cocone under the actual partial functor.
- The diagrams `X a` have domain the lifted `nerve I`, and `p a` are arbitrary
  colimiting cocones on them, not arbitrarily selected colimit objects.
  `CanonicalComparison F X p` states that there is a product cocone `q` whose
  projection under each actual `Pi.π C a` is the given `p a`, and that its image
  under `F` is colimiting. Projection equality uses heterogeneous equality because
  `Pi.lift X ≫ Pi.π C a` is propositionally, rather than definitionally, `X a`.
  The standard equation `Pi.lift_π` provides exactly this canonical transport.
  Since the product cocone is uniquely pinned by all its projections, this fixes
  its apex and its whole coherent cylinder, not merely its vertex legs.
  Being colimiting is equivalent to the canonical map from any colimit of the
  diagonal diagram to this cocone's apex being an equivalence; existence of those
  colimits is already part of the `E` hypothesis. This cocone formulation retains
  the canonical comparison without choosing composition or universal-arrow fillers.
- At `n = 0`, the product category is terminal, the projection condition is empty,
  and the image cocone is the constant cocone at the object selected by `F`.
  Both the ordinary isomorphism and the coherent colimit assertion therefore say
  that the constant diagram has that object as colimit.
- The final conjunction gives `Nonempty ((nerve SimplexCategoryᵒᵖ) _⦋0⦌)` and
  finality of its binary diagonal. By the first equivalence this is siftedness.
  The earlier assertions therefore apply to its coherent simplicial diagrams;
  their colimit is geometric realization, exactly as in the node.

### Existing declarations used

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.power`.
  The complete-algebroid record and its complete source were read; its spaces
  and universe conventions are inherited through the imported framework.
- Mathlib's recorded `def-weil-pbc-simplicial-set` match: `SSet`, `SimplexCategory`,
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`.
  The latter notions establish the dependency's exact definition; no replacement
  definition is introduced here. The statement needs `SSet` and `SimplexCategory`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `Quasicategory`, `coconeCategory`,
  `IsColimiting`, `IsContractible`, and the degreewise simplicial-product convention.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory` and `CategoryTheory.Spaces.mappedCocone`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `HasSmallColimits`, `PreservesColimitsIn`.
- `Sheaf.CategoryTheory.SpacesKappaLimitFilteredColimit`:
  `CategoryTheory.Spaces.InterchangeColimit`, only the definition of the colimit
  presentation; its filtered-limit theorem is not a hypothesis or an invoked proof.
- `Sheaf.CategoryTheory.InfinityLimitsProductsPullbacks`:
  `SSet.Enhanced.PreservesLimitsOfShape`, `infinityDiscrete`, only their definitions.
- `Sheaf.CategoryTheory.InfinityColimitGluing`: `gluingCoconeRestrict`, only the
  canonical restriction definition, not the gluing theorem.
- Mathlib `CategoryTheory.Pi.Basic`: the product category, `Functor.pi'`,
  `CategoryTheory.Pi.eqToEquivalence`. Mathlib products: `Pi.lift`, `Pi.π`.
  Mathlib limits: `Cocone`, `colimit`, `colimit.ι`, `colimit.desc`, `HasColimitsOfSize`,
  `PreservesColimitsOfSize`; `CategoryTheory.Limits.Final`: `Functor.Final`.
- The recorded proof-dependency modules `EnhancedFunctorConeCalculus`,
  `SimplicialGroupoidLocalization`, `NerveNaturalHomotopyEquivalence`,
  `ParametricUniversalArrows`, `SpaceTransportClassification` and Mathlib
  `CategoryTheory.Limits.Fubini` are imported without `public` as the stage-3 plan.
  `lem-coef-infinity-cofinality-space-test` and
  `lem-coef-spaces-small-colimits-universe` have no recorded declaration and hence
  supply no import yet; the statement does not require their postponed proofs.

Added statement dependencies are the six already landed interfaces for coherent
cones, spaces, presentability, the colimit presentation, limit preservation and
restriction. I read their node statements, records and helper signatures, and
checked reachability: none reaches this item. No new node and no dependency-record
repair is necessary. No statement or proof dependency was removed.

The downstream `InfinitySiftedColimitCalculus` module contains the equivalent
`IsInfinitySifted` predicate and a binary special case. Its node's proof depends
on this item. Importing it or adding its node as a prerequisite would reverse that
edge. This delivery neither imports it nor defines a second siftedness predicate:
it writes the equivalence itself, with the existing nonempty and finality notions.

### Edge cases and verification

- Empty `K`: colimits of spaces still exist, but finite-product preservation is
  false by the empty product and the right side of the equivalence is false.
- A point: all finite diagonals are equivalences, including the map to the point
  at `n = 0`, and the comparisons reduce to the specified functorial cocones.
- A discrete two-point shape: the diagonal is not final; the product-preservation
  condition fails. Weak contractibility was not confused with mere nonemptiness.
- `n = 0`, `n = 1`, and higher arities were inspected in both comparison clauses.
  At zero the family of diagrams has no members; the constant-cocone conclusion
  remains nonvacuous for each object selected by `F`.
- Empty spaces and initial objects are allowed. No nonempty vertex of a space
  or of any arbitrary coherent category is required as an added hypothesis.
- Larger target object and hom universes remain independent; no universe equality
  or accessibility, filteredness, presentability or constructibility hypothesis
  was added. The ordinary categories assume cocompleteness, not presentability.
- `scompile.py` compiled the sandbox file and its library module successfully,
  with no errors or warnings (3.2 seconds and 4.9 seconds in the clean run).
  Every variable and universe is explicitly bound and `autoImplicit` is disabled.
  The data definitions have no `sorry`; only the main theorem has `by sorry`.

### Searches and source reading

- `msearch.py leanfinder`, query “sifted infinity category nerve finite diagonals
  final separately colimit preserving functor”: eight hits, chiefly ordinary
  `CategoryTheory.IsSifted` and ordinary Type-valued colimit results. No exact match.
- `msearch.py loogle`, query `"Sifted"`: twelve hits, all ordinary siftedness.
  `CategoryTheory.IsSifted` is not homotopy siftedness of a nerve; HTT explicitly
  warns that the converse implication is false. Its signature and definition
  in `Mathlib.CategoryTheory.Limits.Sifted` were inspected.
- `msearch.py grep`, query `sifted|Sifted`, subdirectory `CategoryTheory/Limits`:
  five hits in the ordinary siftedness module; no coherent finite-arity calculus.
- `msearch.py leansearch`, query “sifted infinity category colimit spaces preserves
  finite products”: eight hits on ordinary siftedness and filtered-product
  comparisons; no exact homotopy-coherent statement.
- `rg` of upstream `WeilConjectures` for `sifted|Sifted` found ordinary site and
  Kan-extension applications, not this theorem. Searching the exact item id
  there gave no hit.
- `rg` of project `lean/Sheaf` found `InfinitySiftedColimitCalculus` (binary special
  case, genuinely downstream), and downstream usages. Searches for `IsFinal`,
  `IsCofinal`, finite diagonals, and product/colimit definitions located the recorded
  lower-level interfaces used above; no full duplicate of the item exists.
- Read the source HTT PDF, printed pp. 506--508, specifically Definition the project server,
  Warning the project server, Lemma the project server, Propositions the project server--7, and Lemma the project server
  with Remark the project server. The small-index convention is explicit in the proof of
  Proposition the project server. Also checked Kerodon tags 02QD and 02QN online, including
  finite diagonals, the nonempty/binary-diagonal criterion, and the finite-product
  colimit condition. Source: https://www.math.ias.edu/~lurie/papers/HTT.pdf
  and https://kerodon.net/tag/02QD .

No statement dispute or source correction was needed.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
