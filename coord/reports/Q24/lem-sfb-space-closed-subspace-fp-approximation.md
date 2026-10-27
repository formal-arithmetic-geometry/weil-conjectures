## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceClosedSubspaceFpApproximation` states
`AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_finitePresentation_limit`
with its sole proof `sorry`. It introduces no definitions. The mathematical statement,
proof and proof dependencies of the assigned node are unchanged. Three already landed
statement dependencies cite the predicates actually used:
`def-sfb-space-morphism-properties`, `def-sfb-space-quasi-compact-presheaf-map`, and
`def-sfb-stack-qcqs-morphism`.
No new nodes, dependency repairs, statement correction or disputed statement.

Source checked: Stacks `spaces-limits.tex`, Tag 0A0U,
`lemma-closed-is-limit-closed-and-finite-presentation`, including its proof and the
finite-type submodule construction of Tag 0829. Also checked the current blueprint's
`det-thm-sf-ctf-stability-direct-images` proof (3). The source proof's phrase
"closed subspace of X" is the already reviewed ambient-space typo: the stages are
closed subspaces of Y. The source statement and assigned node are correct.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Work over Spec Z: `X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`. The lifted
  integers give Spec Z at the same universe as the schemes and presheaf values;
  this does not specialize to schemes, affine spaces or Noetherian spaces.
- The supplied closed immersion is `i : X ⟶ Y` with
  `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  This quantifies over every scheme test, as required.
- Quasi-compact Y: `hYqc : IsQuasiCompact Y.obj` uses the existing definition
  from `StackQcqsMorphism`. Its body supplies a scheme `U : Over (Spec Z)`, an
  atlas `a : yoneda.obj U ⟶ Y.obj.obj`, and
  `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`. Neither Hausdorffness nor
  quasi-separatedness of the atlas is imposed; the body is not copied inline.
- Quasi-separated Y: `hYqs` is `IsQuasiCompactPresheafMap` of its absolute
  diagonal `prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)`. This is the diagonal in
  presheaves on schemes over Spec Z, rather than a diagonal relative to an
  arbitrary possibly non-separated base.
- A small nonempty directed set: existential `I : Type u`, `Preorder I`,
  `Nonempty I`, and `IsDirected I (· ≤ ·)`. Preorder is the directed-set
  convention of Stacks 00D3 and the current project brief. There is no extra
  index universe that could fall below the schemes' universe. On a finite affine
  etale atlas, finite-type quasi-coherent subideals are determined by finite lists
  of sections; hence their index can be shrunk to this bound. No countability or
  finiteness of I is required.
- The stages over Y and compatible transition maps are the functor
  `D : Iᵒᵖ ⥤ Over Y`. Here `(D.obj a).left` is X_a and `(D.obj a).hom` is i_a.
  A relation a ≤ b gives the opposite arrow from b to a, hence r_ba.
  Functor laws give transition identities and composition, and Over morphisms
  give `r_ba ≫ i_a = i_b`.
- Each i_a is a closed immersion by the first conjunct under `∀ a : Iᵒᵖ`.
  The other three conjuncts give quasi-compactness, quasi-compactness of its
  relative diagonal, and `MapIsLocallyOfFinitePresentation (D.obj a).hom`.
  These are exactly finite presentation as defined in the node. The chart
  predicate uses Mathlib's scheme `LocallyOfFinitePresentation`.
- All transitions are closed immersions by the conjunct quantifying over every
  `f : a ⟶ b` and testing `(D.map f).left.hom.hom` on schemes.
- The compatible q_a are the components of
  `q : (Functor.const Iᵒᵖ).obj (Over.mk i) ⟶ D`. Each is a closed immersion
  by the next conjunct. The source is exactly the original X over Y, without
  choosing a merely isomorphic unrelated vertex. The over-category triangle
  `(q.app a).w` states `q_a ≫ i_a = i`. Naturality, after forgetting to
  algebraic spaces and simplifying the constant functor, states
  `q_b ≫ r_ba = q_a` for a ≤ b.
- The final clause `Nonempty (IsLimit (Cone.mk (Over.mk i) q))` states the full
  universal property in algebraic spaces over Y, with vertex the given X and
  cone precisely q. No independently existing limit or sheaf-limit assumption
  is added. The two compatibility equations are already structural fields of
  q and its components, so no separate tautological conjuncts are appended.
- The node's preliminary explanations of separatedness, local finite type and
  finite type are conventions; none is an extra hypothesis or conclusion here.
  The local finite presentation and closed-immersion notions are used through
  the existing chart and representability interfaces, rather than scheme-only
  predicates applied to algebraic spaces.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`; this is the
  recorded fppf-sheaf/full-subcategory model, not a private algebraic-space type.
- `def-weil-size-convention` has a convention-only Lean record: explicit
  `universe u`, the chosen Spec Z, and the small index implement that convention.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` (used through the chart predicate).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  its imported quasi-compactness interface; imported as the recorded statement
  dependency establishing the node's finite-type convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and the same sheaf pullbacks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocallyOfFinitePresentation`, defined using `MapIsLocally`
  and Mathlib's `LocallyOfFinitePresentation` on compatible etale scheme charts.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicSpace.IsQuasiCompactPresheafMap`, the exact atlas-based affine-test
  quasi-compactness predicate used for the absolute and relative diagonals. The
  owning definition node is `def-sfb-space-quasi-compact-presheaf-map`; no conclusion
  of the etale-locality theorem is used to state this item.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `AlgebraicSpace.IsQuasiCompact`,
  the existing qc-scheme-atlas predicate applied to `Y.obj`, owned by
  `def-sfb-stack-qcqs-morphism`.

The following recorded proof modules are plain imports:
`AlgebraicSpacePointTopology`, `Mathlib.Topology.Defs.Filter`,
`AlgebraicSpaceIdealClosedSubspaceCorrespondence`,
`AlgebraicSpaceModuleFpDirectedApproximation`, `AlgebraicSpaceAffineChartCalculus`,
and `AlgebraicSpaceClosedStructureFinitePresentation`. Their relevant declarations
are `pointTopologicalSpace`, `CompactSpace`, `ideal_closedSubspace_correspondence`,
`exists_finitePresentation_filtered_colimit`, `quasiCoherent_affine_chart_calculus`,
and `closedImmersion_structure_finitePresentation_iff`.
`lem-sfb-space-qcoh-kernels-colimits` currently has no Lean record or Mathlib match;
its proof import is consequently omitted under the rule to import stated proof
nodes. Its content remains in the proof docstring and its proof dependency is
preserved. It is not needed to type the statement. The proof docstring reproduces
all six accepted steps, including directedness, images, closed transitions and
uniqueness for arbitrary algebraic-space test cones.

Edge cases checked before writing:

- Y empty implies X empty; a singleton constant system gives the conclusion.
- The zero ideal gives X = Y with the constant identity system, including Y empty.
- The unit ideal gives the empty closed subspace; it is finite type and can occur
  as a finitely presented stage. No nonemptiness of X or Y was added.
- An already finitely presented immersion permits a singleton system. Identity
  transitions are included in the all-arrows quantifier and are closed immersions.
- For a non-finitely-generated ideal in a non-Noetherian ring, finite subideals
  supply many stages; no finite-presentation assumption on i was inserted.
- The index cannot be empty: both `Nonempty I` and directedness are stated. No
  surjectivity of transitions, separation of Y, or schemeness of X is imposed.

Searches (2026-10-24; wrapper outputs are saved in `searches.jsonl`):

- `msearch.py leanfinder`, query "A closed immersion of quasi compact quasi
  separated algebraic spaces is an inverse limit of finitely presented closed
  immersions": eight hits, all scheme closed-immersion facts, no match.
- `msearch.py leanfinder`, query "Algebraic space closed subspace finite presentation
  inverse limit directed finitely generated ideals": eight hits, including scheme
  local finite presentation and scheme affine-transition limits, no space theorem.
- `msearch.py leansearch`, query "Closed immersion algebraic space inverse limit
  finite presentation": eight scheme closed-immersion hits, no match.
- `msearch.py loogle`, query "IsClosedImmersion, LocallyOfFinitePresentation":
  unknown unqualified identifier, no hits. Retried with fully qualified
  "AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation":
  no hits.
- `msearch.py grep`, query `closed.*[Ll]imit|[Ll]imit.*closed|closed.*finitePresentation`
  in Mathlib/AlgebraicGeometry: eight hits, on categorical closure and scheme
  pullbacks/equalizers, not this theorem.
- `rg` in both project source roots for closed limits, closed fp approximation,
  and the proposed declaration name: scheme-only approximation modules and
  algebraic-space consumers, but no theorem with this statement. In particular
  `FiniteClosedFpApproximation`, `LocallyFiniteTypeLimitClosedFp`, and upstream
  `ProperFinitePresentationClosedLimit` use schemes, so cannot be reused as an
  exact match. `SpaceSeparatedFiniteTypeFPEnvelope` names this node in its proof
  but does not state or define the required approximation.
- `grep -rn` for the exact node id in `lean/WeilConjectures`: no hits.

Validation: scompile.py compiled the repaired module cleanly in sandbox and library
module contexts on the server (8.6 s and 10.0 s). No errors or unexpected warnings.
All variables and universes are explicit, `autoImplicit` is false, no diagnostic
commands remain, and every Lean line has at most 100 columns.
The delivery dry run and final push are performed through deliver2.py.


## Returned delivery repaired

Against immutable returned head `925c5067e4b9` and the current main node:

1. H2: replaced the added theorem dependency
   `lem-trf-space-qc-separated-etale-local` with the already landed definition node
   `def-sfb-space-quasi-compact-presheaf-map`. Read its exact `lean` record and
   `IsQuasiCompactPresheafMap` definition. The public import of
   `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal` remains, because that module
   contains the definition. The theorem's conclusion is not a statement dependency.
2. H4: replaced the inline qc-atlas existential with
   `hYqc : IsQuasiCompact Y.obj`. Read `StackQcqsMorphism` and verified that this
   predicate unfolds verbatim to the previous existential, so all hypotheses,
   universes and edge cases are preserved. Added its public import and the owning
   definition node `def-sfb-stack-qcqs-morphism` to `stmt_deps`.

The node is refreshed from current main, keeping every base field and dependency;
only `lean` and the authorized added `stmt_deps` differ. The existing base dependency
`lem-trf-space-fibre-products-etale-covers` is retained as the review requested.
The theorem conclusion, six-step proof docstring and sole `sorry` are unchanged.
The report and verbatim `lean.statement` have been updated to the repaired signature.
No independent second reading is claimed: the maintainer reviews this delivery.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
