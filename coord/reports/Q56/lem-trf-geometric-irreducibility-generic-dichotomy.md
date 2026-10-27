## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricIrreducibilityGenericDichotomy` states
`AlgebraicGeometry.geometricallyIrreducible_genericDichotomy`, with `sorry` as its
only proof. It introduces no definitions, new nodes, or dependency repairs. The
item is unchanged except for its `lean` record. Read Stacks More on Morphisms,
Tags 055A and 055B, including the full generic-constancy lemma and the second
paragraph of the constructibility proof. The latter uses the former; its finite
presentation/Noetherian reduction is not needed for this extracted assertion.

Hypothesis and clause audit:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`, at arbitrary explicitly
  bound universe `u`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the conjunction
  specified by `def-weil-finite-type-morphism`; not finite presentation.
- Closed subset: `(Z : Set Y) (hZclosed : IsClosed Z)`.
- Nonempty irreducible subset: `(hZirreducible : IsIrreducible Z)`. Mathlib's
  `IsIrreducible` includes `Z.Nonempty`, so no separate assumption is missing.
- A relatively open subset of Z: `∃ V : Set Z, IsOpen V`. The subtype `Z` carries
  its subspace topology; being a subset of Z is enforced by the type.
- V is nonempty: the explicit conjunct `V.Nonempty`.
- First alternative: `∀ t : Z, t ∈ V → GeometricallyIrreducible
  (f.fiberToSpecResidueField t.val)`.
- Second alternative: `∀ t : Z, t ∈ V → ¬ GeometricallyIrreducible
  (f.fiberToSpecResidueField t.val)`.
- Precisely one alternative: `Xor` of those two propositions. This retains
  exclusivity explicitly; nonemptiness makes simultaneous truth impossible.
- The scheme-theoretic fibre is the domain of `f.fiberToSpecResidueField t.val`,
  namely `f.fiber t.val = pullback f (Y.fromSpecResidueField t.val)`, and its
  target is `Spec (Y.residueField t.val)`. Thus geometric irreducibility is over
  exactly the residue field in the node, not of f over the whole base.
- Geometric irreducibility uses Mathlib's field-base-change `IrreducibleSpace`
  predicate; that class includes nonemptiness. Empty fibres therefore fail
  it and fall in the second alternative. No flatness, reducedness,
  surjectivity, characteristic, or Noetherian condition is imposed.

Dependency declarations read and used:

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | Scheme.Hom.fiber; fiberι; fiberToSpecResidueField |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField | Scheme.residueField; Scheme.Hom.residueFieldMap |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible | IsIrreducible; irreducibleComponents |
| def-pc-geometrically-irreducible | Mathlib.AlgebraicGeometry.Geometrically.Integral | AlgebraicGeometry.GeometricallyIrreducible, publicly imported from Geometrically.Irreducible |
| lem-sc-scheme-sober | Mathlib.AlgebraicGeometry.Properties; Mathlib.Topology.Sober | scheme QuasiSober/T0Space instances; QuasiSober.sober; IsGenericPoint.eq |
| lem-trf-geometric-component-count-generic-constancy | Sheaf.TraceFormula.GeometricComponentCountGenericConstancy | AlgebraicGeometry.geometricComponentCount_genericConstancy |
| def-pd-separable-closure | WeilConjectures.Mathlib.FieldTheory.IsSepClosed | IsSepClosure.exists_intermediateField_mem; imported Mathlib IsSepClosure interface |
| lem-sc-irreducible-components-cover | Mathlib.Topology.Irreducible | exists_mem_irreducibleComponents_subset_of_isIrreducible; mem_irreducibleComponent; irreducibleComponent_mem_irreducibleComponents |
| lem-sbc-subset-geometric-irreducibility | WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility | AlgebraicGeometry.isIrreducible_preimage_of_isSepClosed_extension |

Statement dependencies are public imports. Dependencies used only by the proof
are ordinary imports; the component-cover interface is already a public import
because its module also defines the irreducibility in the statement. The
recorded geometric-integrality module publicly provides the exact geometric
irreducibility class needed here, so its record needs no repair. Every postponed
proof step is included in the theorem docstring, with the DAG dependency names.

Edge cases checked before writing:

- Empty Y has no nonempty irreducible Z, so no false existence conclusion.
- Empty Z is excluded by `IsIrreducible Z`, as in the node.
- Empty X (and individual empty fibres) gives the negative alternative, since
  base change remains empty and `IrreducibleSpace` requires nonemptiness.
- For a one-point base the relative open must contain that point: the result
  reduces to geometric irreducibility or its negation, with no genericity gap.
- Identity morphisms have one-point geometric fibres and give the positive
  alternative. Two disjoint copies of the base give the negative alternative.
- Nonreduced geometrically irreducible fibres are allowed: no reducedness
  hypothesis or geometric-integrality conclusion has been substituted.
- Non-Noetherian bases and nonflat finite type morphisms remain allowed. The
  source 055A and the recorded count theorem cover them.
- Separable versus purely inseparable field extensions do not change the
  intended test: the existing geometric-irreducibility class quantifies over
  all field-valued points after base change.

Searches for an existing exact statement (2026-10-24):

1. `msearch.py ... leanfinder "For a finite type morphism of schemes every
   irreducible closed subset of the target has a nonempty relatively open
   subset on which geometric irreducibility of fibres is constant"` returned
   eight hits about finite/discrete fibres, Jacobson spaces, and local finite
   type. None asserts this dichotomy.
2. `msearch.py ... loogle "AlgebraicGeometry.GeometricallyIrreducible,
   IsIrreducible"` returned only `Scheme.Hom.isIrreducible_preimage`, which
   assumes an already geometrically irreducible open morphism.
3. `msearch.py ... grep "(geometricallyIrreducible|GeometricallyIrreducible).*(generic|dichotomy|constructible)|(generic|dichotomy|constructible).*(geometricallyIrreducible|GeometricallyIrreducible)" AlgebraicGeometry`
   returned zero Mathlib hits.
4. `msearch.py ... leansearch "For a finite type scheme morphism geometric
   irreducibility of fibres is constant on a nonempty relative open subset of
   any irreducible closed subset"` returned eight hits about irreducible
   closed subsets, finite fibres, integral schemes, partial maps, and finite
   component sets on Noetherian schemes. None is the assertion.
5. `rg` of the upstream WeilConjectures and project Sheaf algebraic geometry
   sources for geometric irreducibility and generic/constructible/dichotomy
   terminology found the component-count theorem, the affine finite
   presentation constructibility theorem, and the distinct section-component
   dichotomy. Read their signatures: none states this theorem for arbitrary
   finite type morphisms and arbitrary irreducible closed Z. Searching the
   exact node id in both trees returned no declaration.
6. The proposed name `geometricallyIrreducible_genericDichotomy` has no hits
   in Mathlib, WeilConjectures, Sheaf, or `dag/lean_names_upstream.json`.

No statement correction or disputed statement. The requested example Sheaf
CompactObject module is now withdrawn; its node points at the upstream
`WeilConjectures.CategoryTheory.CompactObject` definition. This does not affect
any dependency of the item.

Validation: server compilation and delivery preflight are recorded below after
running the prescribed wrappers. The maintainer performs the independent review;
no second worker was started, as directed by the dispatcher brief.

Server `scompile.py` passed for the delivered file in both sandbox and library
module mode (1.6 s / 1.7 s), without errors or unexpected warnings.
`deliver2.py Q56 lem-trf-geometric-irreducibility-generic-dichotomy --no-push`
printed `OK (dry run): commit 8529f7095ce passes the preflight and compiles;
nothing pushed`. Only the prescribed three delivery files were staged.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
