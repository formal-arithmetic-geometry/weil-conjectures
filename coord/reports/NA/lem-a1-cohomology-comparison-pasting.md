## Worker report

The delivery states `lem-a1-cohomology-comparison-pasting` in
`Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting`.
The main declaration is
`CategoryTheory.Triangulated.TStructure.cohomology_comparison_pasting`;
`lean.declarations` lists its canonical construction and all the remaining clauses.
Every theorem has exactly `by sorry` as its proof. The natural isomorphism is a real
composite of existing natural isomorphisms, with no postponed data or arbitrary choices.
The node's statement, dependencies and proof are unchanged. No new nodes or dependency
modules are needed. There is no statement dispute.

Source read: the local BBD PDF, PDF pages 30--35, including printed pp. 29--32:
Proposition 1.3.3 gives the truncation adjunctions and uniqueness, Proposition 1.3.5
gives commuting truncations, and Theorem 1.3.6 identifies their heart-valued composite.
As the node says, its coherence equations are the extracted agent calculation, not a
verbatim theorem quoted from BBD. The docstrings carry all eight DAG proof steps:
heart bounds; composite formula/naturality; transformation equation; double-truncation
composition; shift composition and identity; squares; horizontal pasting; vertical
pasting and associators.

Hypotheses and clauses, matched individually:

- C and D, and each subsequently introduced B, C', D', C'', D'', are arbitrary categories
  with separate object and morphism universes. They are represented respectively by
  C, D, B, E, A, Z, with `Category`, `Preadditive`, `HasZeroObject`, `HasShift ... ℤ`,
  additive shifts, `Pretriangulated` and `IsTriangulated`. The named ambient triangulation
  instances are explicitly included in the public theorem signatures, even where Lean
  could elaborate the formula using just the pretriangulated structure.
- A bounded t-structure is `tC : TStructure C` and `_hC : tC.bounded = ⊤`, and similarly
  for every other category introduced in the appropriate clause. No uniform bound on
  all objects is imposed.
- F's exactness with its coherent shift comparisons is `[F.CommShift ℤ]`
  `[F.IsTriangulated]`. Preservation of both halves at every integer cutoff is precisely
  `[F.IsTExact tC tD]`, whose upstream fields quantify over all integers. G, H, U, V, F',
  S, W and F'' have the corresponding hypotheses wherever they occur.
- The canonical alpha-minus is `F.eTruncLTIso tC tD (m + 1 : ℤ)`, while alpha-plus is
  `F.eTruncGEIso tC tD (m : ℤ)`. These are exactly the recorded dependency's canonical
  comparisons, characterized by its counit and unit equations. `truncLE m` unfolds to
  `truncLT (m + 1)`; no alternative truncation is constructed.
- H^j is written directly as `tC.truncGELE j j ⋙ shiftFunctor C j`, where Mathlib's
  `truncGELE j j` is `truncLE j ⋙ truncGE j`. Thus the order is upper truncation,
  lower truncation, shift, exactly as specified. This uses existing functors directly
  rather than defining another cohomology endofunctor.
- `truncationCohomologyComparison tC tD F j` is an actual natural isomorphism
  `(H_C^j ⋙ F) ≅ (F ⋙ H_D^j)`. Its body first uses the specified `F.commShiftIso j`,
  then the lower comparison at the upper-truncated input, and then the lower
  truncation of the upper comparison; associators make every parenthesization explicit.
- The main theorem states membership in the source heart and both target hearts and
  its exact component formula. The latter is `c ≫ shift.map (alphaPlus ≫ tauGE.map
  alphaMinus)`, which is the node's displayed right-to-left formula in Lean's
  left-to-right composition notation. These heart memberships mean the same natural
  isomorphism restricts to the full heart, without adding a new copy of the heart.
- `truncationCohomologyComparison_naturality` takes any `η : F ⟶ G` and
  `[NatTrans.CommShift η ℤ]`; its equation is `η_HK ≫ q_G = q_F ≫ H.map η_K`.
  There is no `IsIso η` hypothesis. This includes zero transformations.
- `truncationCohomologyComparison_comp` introduces the third bounded t-category and H.
  The actual Mathlib composite shift instance is used, giving
  `q_(F ⋙ H) = H.map q_F ≫ q_H`. Its t-exactness proof is supplied by the named
  `cohomologyComparison_compTExact`, which merely states closure of these same
  hypotheses under composition. `truncationCohomologyComparison_id` uses the standard
  identity shift structure and the named identity t-exactness theorem, giving `q_id = id`.
  Both small closure theorems have `sorry` proofs, source and proof-plan docstrings,
  and are listed under this owning node; they introduce no new notion or assumption.
- `truncationCohomologyComparison_square` introduces the two new bounded t-categories
  B and E, the functors U, V, F', and `b : F ⋙ V ≅ U ⋙ F'` with
  `[NatTrans.CommShift b.hom ℤ]`. The three conjuncts are exactly the displayed square
  for `truncLE m`, the displayed square for `truncGE m`, and the displayed cohomology
  square. For example the cohomology equation is
  `b_HK ≫ F'.map q_U ≫ q_F' = V.map q_F ≫ q_V ≫ H.map b_K`.
- `truncationCohomologyComparison_paste` introduces S, W, F'' and the successive square
  `d : F' ⋙ W ≅ S ⋙ F''`, with every boundedness, exactness, t-exactness and shift
  compatibility assumption retained. It gives all three faces for the pasted boundary
  `W.map b_K ≫ d_(UK)`, expanded as successive comparisons. In particular both the
  transformation and the comparison chains are the explicit ones in DAG Step 7.
  This is the binary pasting law, whose iteration gives successive pasting of any
  finite number of squares, including the single-square and identity cases.
- `truncationCohomologyComparison_vertical` gives all three equations for vertical
  composition of shift-compatible transformations η and θ, as in Step 8. The
  transformation theorem applies to any specified shift-compatible associator between
  parenthesized exact t-exact functors; Mathlib's `NatTrans.CommShift.associator`,
  `leftUnitor` and `rightUnitor` supply the usual cases. Their component equations are
  instances of that quantified theorem, not an implicit equality of functors. Vertical
  pasting includes composites of such specified associators. Identity transformations
  specialize the same equations; identity outer functors are removed by the identity
  comparison law and the dependency's truncation identity law.

Dependency declarations read and used:

- `def-weil-triangulated-category` is a Mathlib leaf: `CategoryTheory.Pretriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Triangulated`, and `Functor.IsTriangulated`
  with its shift instance in `Mathlib.CategoryTheory.Triangulated.Functor`. The fields
  and ambient hypotheses were read directly.
- `def-weil-t-structure` is a Mathlib leaf: `CategoryTheory.Triangulated.TStructure`,
  `TStructure.bounded` in `...TStructure.Basic`, `TStructure.heart` in `...TStructure.Heart`,
  `truncLT`, `truncGE` and their canonical arrows in `...TStructure.TruncLTGE`, and
  `truncLE`/`truncGELE` in `...TStructure.TruncLEGT`. These are all used directly.
- `lem-pod-texact-truncation-comparison`:
  `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`, declaration
  `CategoryTheory.Triangulated.TStructure.texact_truncation_comparison`, whose full
  signature and proof docstring were read. The public import exposes its exact
  `Functor.eTruncLTIso` and `eTruncGEIso` from the upstream SpectralObject module.
  Their full signatures, canonical-map equations, the `Functor.IsTExact` fields and
  `eTruncGELTIsoApp` were read; the new q is their required shifted natural composite.
- Proof-only `lem-weil-heart-short-exact-triangles`:
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`, with `homology₀`
  and the referenced `ShortExact` constructions. It is a plain proof import; the heart
  definition is publicly imported from Mathlib because it appears in the statement.

Edge cases checked against the formulas: all j and m are ℤ (including j < 0 and j = 0),
K may be zero, and the t-structure may be the degenerate one on the zero category.
The identity functor uses its prescribed identity shift comparison. η can be zero,
identity or noninvertible; b and d are isomorphisms exactly where the node requires it.
No nonempty indexing set is introduced. The six categories have independent universes.
Each equation was checked from its actual source to its actual target, including the
unshifted truncations and the nontrivial parenthesizations in the pasted formula.
The shift sign follows `le_shift`: shifting an object bounded above and below by j by
j puts it at cutoff zero. No faithfulness or chosen adjunction is assumed.

Searches actually run (the search log is retained in the sandbox):

- msearch LeanFinder: “Canonical cohomology comparisons of t exact triangulated functors
  compatible with natural transformations composition and pasting”: eight hits, including
  `Functor.instIsHomologicalCompOfIsTriangulated`, spectral-object map equations,
  `mapTriangleCompIso`, `isTriangulated_iff_comp_right`, `map_distinguished_exact`,
  `IsTriangulated.instComp`, and `comp_homologySequenceδ_assoc`. None is the statement.
- msearch Loogle: `Functor.eTruncLTIso, Functor.commShiftIso, TStructure.homology`:
  zero hits, with the explicit diagnostic “unknown identifier 'Functor.eTruncLTIso'”.
  This upstream-only name was therefore checked directly in the project source;
  this diagnostic is not evidence that the declaration is absent from the project.
- msearch grep `cohomologyComparison|homologyIso|commShiftIso` in
  `CategoryTheory/Triangulated`: 25 hits, principally shift comparisons and subcategories.
- msearch LeanSearch: “A t exact triangulated functor commutes with cohomology naturally
  in shift compatible transformations and composition”: eight hits, chiefly
  `Functor.IsTriangulated`, its composite instance and derived/homotopy functor instances;
  no canonical double-truncation cohomology comparison and pasting theorem.
- msearch grep `cohomologyComparison|truncGELE|homologyIso` in
  `CategoryTheory/Triangulated/TStructure`: five hits for the existing `truncGELE` and
  its comparison to `truncGELT`, not this cross-category statement.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for cohomology comparison names,
  `eTruncLTIso`, `eTruncGEIso`, `homologyIso`, and the exact node id: the upstream
  SpectralObject module has the canonical single and double truncation components;
  `TExactCohomologyBoundaryComparison` constructs a shift-first comparison and boundary
  compatibility; `CoefficientStageDescent.Comparisons` has a q field and formula but no
  transformation/composition/pasting theorem. `ConstructibleTruncations` writes the same
  cohomology endofunctor. The present file writes the existing functors directly rather
  than privately duplicating them, and constructs the particular q specified by this node.
- rg of Mathlib, the project, and `dag/lean_names_upstream.json` for all proposed public
  names found no collision. The recorded example module is now a withdrawn empty module;
  its node points to the existing upstream compact-object definition instead.

Validation: scompile.py compiled the final module separately in sandbox and library mode
against the published live build, each under four seconds, with no errors or warnings.
All ten declarations are listed in the node record. The only definition is the natural
isomorphism composite; all nine theorem proofs remain `sorry` as required by stage 2.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
