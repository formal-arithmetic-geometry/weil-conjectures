## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitBruhatAffineStratification`
states `AlgebraicGeometry.exists_split_bruhat_affine_stratification`. Its one theorem
has proof `sorry`. The helper `splitFlagQuotientProjection` is actual data: apply
`yoneda.preimage` to the coequalizer projection followed by the supplied
sheafification map. It introduces no arbitrary quotient projection, no chosen
existence witness, and no postponed construction theorem.

The node statement is unchanged. Its statement dependencies gain the already
landed `def-constructible-stratification`, because the statement uses the exact
recorded `Scheme.FiniteLocallyClosedStratification`. No new nodes or dependency
modules are needed.

Hypothesis and conclusion correspondence:

- The arbitrary field is `{F : Type u} [Field F]`; there is no algebraic-closedness,
  perfection or characteristic restriction. The three group schemes are bundled
  `H T B : Grp (Over (Spec (.of F)))`.
- Reductivity is `hH : ReductiveTorusCentralizer.IsReductive H`. Its recorded
  definition includes affine finite type, smoothness, connectedness after algebraic
  closure and triviality of every smooth connected normal unipotent subgroup
  there. No substitute reductivity assumption is used.
- `iT`, `iB`, `j`, `hj` specify T inside B inside H, with `j ≫ iB = iT`.
  `hT` uses the recorded maximal-torus definition, including closedness;
  `hTs` gives a group-scheme isomorphism with `MultiplicativeType.splitTorus F r`.
  The map j is necessarily a closed subgroup inclusion: iT is closed and factors
  through the closed inclusion iB. This avoids assuming an arbitrary unrelated map.
- `hBclosed` says B is closed; `hBsplit : IsSplitSolvable B` uses precisely the
  finite smooth connected normal series with Ga/Gm fppf quotients, including length
  zero. It supplies smoothness, connectedness and solvability of B. `hBmax`
  tests every smooth connected solvable closed overgroup D using the recorded
  `SolvableGroupStructure.IsSolvable`, and requires the inclusion to factor back.
  Thus it is exactly the stated Borel maximality. The existing
  `IsBorelGroupScheme` requires an algebraically closed field and uses a different
  recorded solvability interface; it is not silently imposed here. No new Borel
  definition is made: the node's explicit condition is expanded in the binders.
- `Q : Over (Spec (.of F))`, `ηQ` and `hηQ` express representation of the fppf
  sheafification of right cosets. The presheaf coequalizer identifies g with gb;
  precomposition with ηQ is bijective into every fppf sheaf of sets. Representable
  presheaves are sheaves by subcanonicity of `Scheme.fppfTopology` and its over
  topology, so no redundant sheaf hypothesis is imposed. Affine tests recover
  the node's commutative-algebra formulation because affines form a basis for the
  big fppf site.
- `Smooth Q.hom ∧ IsProjective Q.hom ∧ GeometricallyIntegral Q.hom` is the first
  conclusion. Mathlib geometric integrality tests integral pullbacks to spectra
  of all extension fields; integral includes nonempty irreducibility and reducedness.
- The witness S is the recorded finite locally closed scheme stratification.
  Its fields give immersions, locally closed images, covering and pairwise
  disjointness. `n : Fin S.n → ℕ` gives nonnegative dimensions. The isomorphisms
  in `Over (Spec (.of F))` identify each actual stratum scheme with
  `AffineSpace (ULift (Fin (n a))) (Spec (.of F))`, as F-schemes.
- `a₀ : Fin S.n` specifies a distinguished index. Its immersion is open and
  `closure (S.stratum a) = Set.univ ↔ a = a₀` says exactly that its closure is
  all Q and no other stratum has this property. This also proves density of the
  specified open stratum without an extra topology predicate.
- For every `L : Type u` with `[Field L] [Algebra F L]`, the theorem states
  smoothness, projectivity and geometric integrality of the actual scalar
  extension `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))`.
  The stratum maps are specifically `pullback.snd (S.immersion a)` along the
  first projection Q_L → Q, hence their domains are the scalar-extended strata.
  Their immersion property and `∀ x, ∃! a, ...` give precisely a disjoint
  partition. The displayed affine-space isomorphisms commute with the map to
  Spec L and have the original dimension `n a`. The same a₀ gives the open cell
  and the closure iff clause gives uniqueness of the dense cell after extension.
- The witness ηL has the right-coset coequalizer for the recorded group scalar
  extensions H_L and B_L as source, and the represented Q_L as target. Its
  universal property states that Q_L represents H_L/B_L. The equation
  `coequalizer.π _ _ ≫ ηL = yoneda.map (Over.pullback ... |>.map
  (splitFlagQuotientProjection ...))` pins this identification to the scalar
  extension of the original quotient projection. Thus the canonical
  identification is included, rather than an arbitrary isomorphism or an
  identification only on rational points. The preceding clauses are for its
  actual scalar-extended subschemes.
- `IsIso iT → S.n = 1 ∧ n a₀ = 0 ∧ Nonempty (Q ≅ Over.mk (𝟙 ...))`
  is the H=T case. Equality of the subgroup T with H means its given inclusion
  is an isomorphism. The last isomorphism is over F, and its target is Spec F.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`; the project group-scheme
  convention and closed-subgroup interface in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus`, `baseChange`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `SolvableGroupStructure.IsSolvable`, `IsAlgebraic`, `IsUnipotent`;
  `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`: `IsSplitSolvable`,
  `SplitSolvableLength`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective`;
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.over`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, the exact recorded declaration
  of `def-constructible-stratification`. It imposes no extra constructibility
  condition and is reused without a second definition.
- The proof imports are the published modules of homogeneous quotient, Borel
  quotient proper geometry, regular connected integrality/smooth regularity,
  proper fpqc descent, proper/smooth base change, closed proper monomorphisms,
  projective-spectrum separation, surjective base change, and fpqc representable
  descent. The proof plan is included step by step in the theorem docstring.
  The Chevalley line stabilizer, rational fixed scheme, weight decomposition,
  projective fixed-weight schemes and rational attracting-cell proof nodes have
  no published Lean record in the read DAG; no nonexistent module is imported.

Source checked directly: Milne, Section 21h, printed pp.446--451, especially
Proposition 21.70 (affine locally closed cells and unique dense open cell),
Theorems 21.73 and 21.80 (scheme decompositions), and Remark 21.82 (dimensions).
The standing assumptions are split reductive over an arbitrary field. These
statements are about schemes, not merely rational-point decompositions.

Edge cases checked before and after writing:

- Rank zero and H=T: j and iB force B=H as subgroups; the right-coset sheaf is
  terminal and the rank-zero affine space is Spec F. The explicit implication
  forces one cell and dimension zero. A nontrivial split torus is also covered.
- There can be zero-dimensional cells: n takes values in ℕ with no positivity
  hypothesis. `ULift (Fin 0)` is empty and the recorded affine-space definition
  gives affine zero-space.
- An empty index set is excluded by the witness a₀, correctly, since a flag
  quotient contains the identity coset. Geometric integrality excludes the empty
  quotient, consistently with that coset, instead of silently admitting an empty
  stratification.
- Finite and imperfect fields, inseparable extensions, positive characteristic
  and characteristic two are all admitted: no auxiliary assumptions occur.
- Identity extension and arbitrary extension maps are included. The extension
  field has the same ambient universe as the schemes, following the recorded
  `MultiplicativeType.baseChange` and Mathlib geometric-integrality convention;
  no universe equality between unrelated sites is introduced.
- The quotient universal property tests all sheaves and all test schemes,
  including nonreduced algebras. No condition is reduced to field-valued points.
- A different presentation of the same subgroup or represented quotient is
  allowed: the group and Over-category isomorphisms account for presentations.

Searches performed:

- msearch leanfinder: `Split reductive group flag variety Bruhat affine space
  stratification over arbitrary fields`: root-system and weight-space results,
  no scheme quotient stratification.
- msearch loogle: `"Bruhat"`: zero hits.
- msearch grep: `Bruhat|Schubert|BorelSubgroup|AffineStratification`: one hit,
  an unrelated Bruhat--Tits tree comment in Mathlib/Algebra/Module/Lattice.
- msearch leansearch: `Split reductive flag variety decomposition into affine
  space cells`: Noetherian decompositions, affine covers and polynomial results;
  no match.
- rg over `lean/WeilConjectures` for `IsBorel|BorelSubgroup|IsHomogeneousQuotient|
  IsFppf.*Quotient|Bruhat|AffineStratification` and the item ID: no exact theorem.
- rg over `lean/Sheaf` found Borel, BorelQuotientAffineCell,
  BorelQuotientAffineSpaceCell, BruhatLongestCellCharts, RhoSectionModules and
  SplitReductiveCharacteristicSequence. Their full relevant signatures were
  read: the first cell/longest-chart statements require algebraic closedness or
  assert a single cell, and characteristic-sequence geometry assumes rather
  than proves the quotient geometry. None is this arbitrary-field statement.
- Searches for `structure Stratification`, `FiniteLocallyClosedStratification`
  and `def-constructible-stratification` found the exact existing finite locally
  closed interface. This removed any need for a new stratification notion.
- DAG searches for right-coset/sheaf and quotient definitions found
  `def-sfb-fppf-group-quotient-presentation`; it requires a group quotient by
  a normal specified kernel, so it does not give H/B when B is not normal.
- `tools/blueprint_refs.py search Bruhat`: zero blueprint-node matches.

No statement correction or STATEMENT-DISPUTED finding is needed.

Validation: scompile compiled the sandbox module and its library-path module
cleanly, with autoImplicit disabled. The deliver2 dry run passed the server preflight and per-file
compilation (dry-run commit f3dfd1869ab); no warnings or errors were reported.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
