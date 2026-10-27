## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceProperFlatGeometricComponentCount`
states `AlgebraicGeometry.AlgebraicSpace.proper_flat_geometric_component_count`.
Its only theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The source was read in `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-proper-flat-geom-red` (Tag 0E1E), and `spaces-over-fields.tex`,
`definition-geometrically-connected` and the lemmas at Tags 0A10, 0A12 and 0A13.

Hypothesis and clause correspondence:

- Scheme target: `{S : Scheme.{u}} (T : Over S)` retains an arbitrary scheme over an
  ambient scheme. Taking `S = T` and the identity includes every scheme target. The
  underlying base space in the conclusion is `T.left` with its Zariski topology.
- Algebraic-space source and its morphism: `(Y : AlgebraicSpace S)` and
  `(h : Y ⟶ schemeSpace T)`. The existing `schemeSpace` is the representable fppf sheaf
  of `T`, so `h.hom.hom` is literally the source presheaf's map to `yoneda.obj T`.
- Proper: `hproper : MapIsProper h`, the existing conjunction of separatedness,
  finite type and universal closedness; no scheme representability is imposed.
- Flat: `hflat : MapIsFlat h`, using the existing compatible-etale-chart test.
- Finite presentation: `hlfp : MapIsLocallyOfFinitePresentation h`,
  `hqc : MapIsQuasiCompact h.hom.hom` and
  `hqs : MapIsQuasiCompact (pullback.diagonal h.hom.hom)`.
  This is exactly the node's expanded convention; it is not finite type alone.
- Reduced geometric fibres: `hred` quantifies over every `Ω : Type u`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, every `a : Spec (.of Ω) ⟶ T.left`, every scheme `U : Over S`,
  and every representable etale chart `b` of the actual presheaf pullback along `a`.
  It concludes `_root_.IsReduced (U.left.presheaf.stalk x)` for every `x : U.left`.
  The root qualification selects the ring predicate, not the scheme predicate.
- The number function: `∃ n : T.left → ℕ`. For each `t`, each algebraically closed
  field `Ω` and every residue-field embedding
  `ι : T.left.residueField t ⟶ CommRingCat.of Ω`, the first conjunct states both
  `Finite (ConnectedComponents (Point (...)))` and `Nat.card (...) = n t`.
  The pullback arrow is exactly the Yoneda image of
  `Spec.map ι ≫ T.left.fromSpecResidueField t`, as a morphism over `S`.
  No algebraicity assumption on `Ω/κ(t)` is made, so this includes every algebraic
  closure, all choices of its embedding, and every larger algebraically closed field.
  Equality to the same `n t` gives all the asserted independence clauses.
- Components: Mathlib `ConnectedComponents` quotients by equality of the maximal
  connected subsets `connectedComponent x`. These are nonempty and maximal, exactly
  as the node requires, and the point space uses the existing atlas topology.
- Local constancy: `IsLocallyConstant n`, Mathlib's open-inverse-image definition,
  equivalent to constancy on some open neighbourhood of each point.
- Empty fibres: `IsEmpty (Point (...)) → n t = 0`, where the pullback is along the
  canonical `Spec κ(t) → T.left`. This refers to the ordinary fibre. The first
  conjunct also gives zero for an empty algebraically closed fibre, since its
  component quotient is empty.
- Count one criterion: `n t = 1 ↔ ∀ (L : Type u) [Field L] (ι : κ(t) ⟶ .of L),
  ConnectedSpace (Point (...))`, without algebraic-closedness or algebraicity on `L`.
  `ConnectedSpace` includes `Nonempty`, so empty fibres are excluded here exactly
  as in Stacks and the node. The identity extension is included.
- Open locus: the final `IsOpen` contains exactly that same universal
  `ConnectedSpace` predicate, not an arbitrary subset or a stronger condition.
- There are no Noetherian, smoothness, scheme-source, surjectivity, positive-count,
  finite-dimensional, characteristic or chosen-atlas assumptions. All universes and
  variables are explicit (`set_option autoImplicit false`). Fields and schemes are
  in the same test universe `u` of the algebraic-space framework, never an independent
  smaller universe that could make an extension quantifier vacuous.

Dependency declarations used (their actual source declarations and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and its scheme-test representability predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsProper`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
  Its public import `Sheaf.AlgebraicGeometry.ProperCurveModuli` supplies the existing
  `MapIsQuasiCompact`, also used on the relative diagonal.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, `Scheme.SpecToEquivOfField`; the latter's inverse
  is the `Spec.map ι ≫ fromSpecResidueField` formula used in the statement.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure` (proof import).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` supplies the algebraic-space meaning of the sheaf
  pullbacks. The statement directly uses `CategoryTheory.Limits.pullback` on presheaves.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point` (from its public
  `AlgebraicSpacePointClasses` import) and `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: the existing `schemeSpace`.
  Added its already landed owning definition node `def-trf-scheme-algebraic-space`
  to `stmt_deps`; this is the only non-lean node-field change, explicitly permitted
  for citing a landed construction. No statement correction is needed.
- Mathlib `ConnectedComponents`, `ConnectedSpace`, `Nat.card` and `IsLocallyConstant`
  supply their standard meanings; none is privately duplicated.

The already recorded proof dependency modules are plain imports:
`WeilConjectures.FieldTheory.CommonExtensionFields`,
`WeilConjectures.AlgebraicGeometry.PerfectComplex`,
`Sheaf.AlgebraicGeometry.PerfectJumpLoci`, and
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`.
The remaining algebraic-space proof prerequisites have no `lean` record yet and are
therefore not imported: `lem-sfb-space-sepclosed-components-base-change`,
`lem-sfb-space-proper-base-change`, `lem-sfb-space-proper-global-algebra-components`,
`lem-sfb-proper-flat-space-derived-base-change`, and
`lem-sfb-space-flat-proper-components-lower-semicontinuous`.
They remain in the DAG and the six-step proof docstring; none is needed to type this
stage-2 statement.

Edge cases checked before writing: empty source/fibre (zero components, and false
`ConnectedSpace`); empty base (all pointwise conclusions vacuous and the empty locus
open); a single geometric component (nonempty connectedness); disjoint finite unions
(component cardinality rather than point cardinality); arbitrary characteristic;
non-Noetherian bases; nonschematic source spaces; arbitrary transcendental residue-field
extensions; the identity residue-field extension; and two distinct choices of algebraic
closure. Finiteness is stated separately, since `Nat.card` alone is zero for an infinite
set and would not assert finiteness.

Searches made, all on 2026-10-24:

- `msearch.py ... leanfinder`, query: "The number of geometric connected components of
  a proper flat finitely presented algebraic space with geometrically reduced fibres
  is locally constant". Eight hits: module rank local constancy, scheme flatness,
  universally open scheme morphisms, finite scheme fibres, proper scheme sections.
  None states this algebraic-space assertion.
- `msearch.py ... leansearch`, query: "A proper flat finitely presented algebraic space
  with geometrically reduced fibres has locally constant geometric connected component
  count". Eight hits: module rank, scheme smooth/flat/finite-presentation facts,
  Noetherian irreducible-component finiteness, finite scheme fibres and abstract
  componentwise locally constant functions; no exact result.
- `msearch.py ... loogle`, query: `"IsProper", "IsLocallyConstant"`: zero hits.
- `msearch.py ... grep`, query:
  `(locallyConstant|locally_constant|IsLocallyConstant).*([Cc]omponent|[Ff]iber)|([Cc]omponent|[Ff]iber).*(locallyConstant|locally_constant|IsLocallyConstant)`.
  Twelve hits in abstract locally constant/condensed topology, none the node.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for geometric/component-count
  terms: existing scheme-only `ProperSmoothGeometricComponentsLocallyConstant`,
  `FlatProperComponentCountLowerSemicontinuous` and `GeometricComponentCountBaseChange`
  do not allow algebraic-space sources or merely geometrically reduced flat families.
  Exact item-id search in `lean/WeilConjectures` found no declaration.
- `rg` over `AlgebraicSpace*.lean` for component counts, geometric connectedness,
  reduced fibres and finite presentation found the existing property interfaces and
  inline finite-presentation convention; no duplicate component-count theorem.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no `proper_flat_geometric_component_count`
  declaration. Read Mathlib `ConnectedComponents`, `ConnectedSpace`, `IsReduced`,
  `Nat.card`, `IsLocallyConstant`, residue-field and algebraic-closure definitions.

Validation: `scompile.py Q84 lem-sfb-space-proper-flat-geometric-component-count <module>`
compiled both sandbox and actual library module successfully, 2.3 seconds each, without
errors or unexpected warnings. Initial probes exposed namespace shadowing of `pullback`
and `IsReduced`, and an underconstrained `Over.homMk` source; these were repaired by
`Limits.pullback`, `_root_.IsReduced` and explicit canonical `Over.mk` source schemes.
No `#check`, local notation, private helpers or placeholder data remain.

## Second reading by Q84

Author's own check under the dispatcher brief; independent review belongs to the
maintainer. I reopened the complete node and final module and matched each clause as
listed above. Proper/flat/lfp/qc/qs remain the existing predicates. The geometric
reducedness hypothesis uses every etale chart, not only an atlas or rational points.
All occurrences of the extension fibre use the same canonical residue-field map,
including its base `Over.mk`; none chooses an arbitrary map or adds algebraicity.
The finite/cardinality conjunct precedes the topological assertions and includes every
algebraically closed extension, giving closure independence. The ordinary empty-fibre
clause and all-field `ConnectedSpace` criterion retain the identity extension and
nonemptiness. The last open set is literally the criterion's right side. No mathematical
mismatch or statement fault was found; the only changes during checking were the
elaboration qualifications and explicit source objects described above. All six proof
steps are in the theorem docstring, with the corresponding DAG prerequisites. This
report does not claim a separate worker or independent reviewer was started.
