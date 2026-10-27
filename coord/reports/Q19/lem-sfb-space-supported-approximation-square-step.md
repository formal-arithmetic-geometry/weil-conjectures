## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSupportedApproximationSquareStep` states
`AlgebraicGeometry.AlgebraicSpace.hasSupportedPerfectApproximation_of_distinguishedSquare`,
with one theorem and its whole proof `sorry`. Its docstring carries the complete corrected
12-step DAG proof. No data definition, helper theorem, or private replacement is introduced.

Source read: `literature/stacks-project/spaces-perfect.tex`, Tag 08HN,
`lemma-induction-step`, including the full proof and the preceding affine lemma.
The DAG already records the four corrections to the printed proof (union formula,
uniform loss, approximation degree, induction endpoint); these are retained verbatim.
The statement itself is unchanged.

Hypothesis and conclusion correspondence:

- Universes and base: explicit `universe u w`, `{S : Scheme.{u}}`, and the two
  `[HasDerivedCategory.{w} _.SmallModules]` binders put both small module derived
  categories in the fixed larger universe. These are size/existence interfaces, not
  extra geometric conditions.
- Ambient algebraic space: `W : AlgebraicSpace S` uses the existing fppf-sheaf definition.
- Quasi-compactness of W: `hWqc : CompactSpace (Point W.obj.obj)` means that every open
  cover of its existing point space has a finite subcover.
- Absolute quasi-separatedness: `hWqs : IsAbsolutelyQuasiSeparated W` is precisely the
  landed affine-test definition equivalent to quasi-compactness of the absolute diagonal
  (Stacks 0AHR). This avoids accidentally assuming the base scheme quasi-separated.
- Open subspace: `A : OpenSubspace W` is the existing subfunctor with inclusion
  representable by open immersions. `U : AlgebraicSpace S` and
  `e : U.obj.obj ≅ A.val.toFunctor` present that open as the algebraic space to which
  the existing approximation predicate applies. The induced inclusion is
  `e.hom ≫ A.val.ι`; no arbitrary map is substituted for the inclusion.
- Quasi-compactness of that open: `hUqc : CompactSpace (Point U.obj.obj)`.
- Scheme chart over S: `V : Over S`; `hV : IsAffine V.left` is actual affineness;
  `j : yoneda.obj V ⟶ W.obj.obj` is its morphism into W; `hj : IsEtale j`
  is representability and étaleness on every scheme test.
- Reduced closed complement: `C : ClosedSubspace W` is the existing scheme-theoretic
  closed subspace; `hCred : IsReduced (C.val : AlgebraicSpace S)` gives reducedness on
  étale charts, and `hC` identifies its point image with `(pointImage A.val.ι)ᶜ`.
  The existing unique-existence theorem ensures this represents exactly the reduced
  complement Z; no choice of an unrelated closed subset is permitted.
- Distinguished condition: `hZ : IsIso (Limits.pullback.snd j C.val.arrow.hom.hom)`
  is exactly the canonical presheaf/sheaf fibre-product projection V ×_W Z → Z.
  An isomorphism of these sheaves is an isomorphism of the represented spaces.
- Quasi-compact overlap: `hUV : IsCompact (schemePointMap j ⁻¹' pointImage A.val.ι)`.
  Since A is an open subfunctor, this inverse image is the open subscheme U ×_W V
  of V, with its scheme topology, so this is precisely the required quasi-compactness.
- Premise: `hU : HasSupportedPerfectApproximation U` is the recorded small-étale
  uniform supported approximation property, including its support, cutoff and
  uniform-in-m,F quantifiers.
- Conclusion: `HasSupportedPerfectApproximation W` is exactly the same property on W;
  it does not weaken any cohomology isomorphism, epimorphism, support or uniformity clause.

Dependency declarations read and used:

- `def-weil-size-convention`: `None` / `None`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace` / `AlgebraicGeometry.AlgebraicSpace`.
- `def-a1-space-open-subspace`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace` / `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`.
- `lem-sfb-space-reduced-closed-support`: `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport` / `AlgebraicGeometry.AlgebraicSpace.exists_unique_reduced_closed_subspace`.
- `def-a1-space-point-topology`: `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` / `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`.
- `def-sfb-space-supported-perfect-approximation`: `Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation` / `AlgebraicGeometry.AlgebraicSpace.HasSupportedPerfectApproximation`.
- `def-sfb-space-absolute-quasi-separated`: `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated` / `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.

The size convention has no object declaration: its recorded convention is implemented
by explicit universe binders. The reduced-closed-support module supplies `ClosedSubspace`
and `IsReduced` through its public imports, and its
`exists_unique_reduced_closed_subspace` uniquely characterizes C. The point-topology
module uses the existing `Point`, `schemePointMap`, `pointImage` and final topology.
The approximation module's full definitions of `IsMPseudoCoherent`, `ModuleSupportedOn`
and `HasSupportedPerfectApproximation` were read, including all quantifiers.

Added existing landed statement dependency `def-sfb-space-absolute-quasi-separated`
for the actual predicate used in hWqs. No new node is necessary. All other statement
and proof fields are preserved.

Every currently recorded proof dependency module is imported without `public`, unless
it already supplies a statement dependency. Mathlib proof inputs include cohomology
exact sequences, finite affine covers, and pretriangulated structure. Proof nodes
currently lacking recorded declarations are not fabricated or imported under guessed
names: etale-pseudocoherence-descent, etale-detects-perfect, space-qcoh-kernels-colimits,
space-qcoh-extension-closed, space-supported-etale-excision, space-etale-sum-stalks,
space-etale-conservative-geometric-points, space-distinguished-derived-gluing, and
ringed-site-m-pseudocoherent-triangle (each prefixed lem-sfb-). These affect future
proof imports only, not the present statement.

Edge cases checked before writing:

- U empty: its approximation property is meaningful and the distinguished condition
  identifies V with the reduced complement; the theorem does not assume nonemptiness.
- U = W: C is empty and hZ is automatic; the assertion transports A(U) along the
  presentation, without requiring a nonempty chart.
- V empty: hZ forces the reduced complement empty, hence the open is all of W.
- Empty overlap is allowed by `IsCompact`; no finite cover with positive size is assumed.
- Nonreduced W is allowed: only its closed complement C is required reduced.
- Base S arbitrary, including non-quasi-separated; absolute, not relative,
  quasi-separatedness is used. No Noetherian, finite-type or characteristic assumption.
- No approximation degree or support is fixed in this theorem: the complete quantified
  property remains the existing definition. Zero derived objects are therefore included.

Searches for an existing declaration (all run using the prescribed wrapper):

- LeanSearch: "uniform supported perfect approximation algebraic spaces distinguished
  square" returned eight unrelated topology/uniformity and scheme-quasi-separatedness hits.
- LeanFinder: "supported perfect approximation algebraic space elementary distinguished
  square etale affine induction step" returned eight scheme/étale-presentation hits,
  none stating this induction step.
- Loogle: `AlgebraicGeometry.AlgebraicSpace.HasSupportedPerfectApproximation`:
  unknown identifier, zero hits in Mathlib search.
- Mathlib grep in AlgebraicGeometry:
  `SupportedPerfectApproximation|supported.*approximation|approximation.*square`:
  zero hits.
- `rg` in live `lean/WeilConjectures` and `lean/Sheaf`:
  `SupportedPerfectApproximation|supported.*approximation|lem-sfb-space-supported-approximation-square-step`.
  Found the existing scheme affine theorem and the space property definition, plus the
  downstream theorem's proof-docstring citation; no space square-step theorem.
- `rg` for `hasSupportedPerfectApproximation_of_distinguishedSquare` in both roots and
  `dag/lean_names_upstream.json`: zero hits.

Validation: prescribed scompile.py compiled the delivered module separately in sandbox
and library modes, 1.7 seconds each, no errors or unexpected warnings.
No STATEMENT-DISPUTED issue or node-statement fault was found.

## Second reading by Q19

Performed a second in-thread reading with the node and completed Lean signature open.
The dispatcher explicitly forbids starting another agent; this is a self-check, not a
claim of an independent worker review. The maintainer's independent delivery review
remains applicable.

Checked each binder against the correspondence above. In particular the presentation
`e` identifies the very open A, hC uses A's point image, hZ is the projection to C
(rather than to V), and hUV uses scheme points, not an unrelated topology on a
presheaf pullback. Re-read the two definitions of absolute quasi-separatedness and
uniform approximation: hWqs uses the absolute affine-test criterion and hU/conclusion
retain every quantifier. No false extra nonemptiness, qc base, separated base, or
point-set reducedness assumption was added. No signature change was needed after this
second reading. The only node delta besides lean is the landed absolute-qs stmt_dep.
