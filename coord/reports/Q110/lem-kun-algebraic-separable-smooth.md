## Worker report

The module `Sheaf.FieldTheory.AlgebraicSeparableSmooth` states
`FieldTheory.algebraic_separable_extension_is_filtered_colimit`, with `sorry` as its
only theorem proof. The two real definitions `finiteSubextensionDiagram` and
`finiteSubextensionCocone` construct the finite intermediate-field inclusion system
and its canonical cocone. They belong to this node's colimit assertion; they introduce
no independent mathematical notion. Their structure equations are definitional.

The current blueprint file in `literature/blueprint/main-20261015/blueprint/` agrees
verbatim with the node's mathematical statement. No node correction is needed.
There is no maintenance repair note for this item.

Hypotheses and clauses:

- Fields `K` and `L` are `{K : Type u} {L : Type v} [Field K] [Field L]`;
  their extension is `[Algebra K L]`. The universes are independent and explicitly bound.
- Algebraic separability is `[Algebra.IsSeparable K L]`. Mathlib's definition says
  that every element has separable minimal polynomial; this includes algebraicity
  (`Algebra.IsSeparable.isAlgebraic`), since the zero polynomial is not separable.
  No redundant algebraicity assumption or transcendental separability predicate is used.
- Finite extensions are the actual intermediate fields
  `{E : IntermediateField K L // Module.Finite K E}`. For fields, `Module.Finite`
  means finite-dimensional, not that the underlying set is finite. Each stage has
  the inherited field and `K`-algebra structures.
- Filteredness is `IsFiltered` of precisely this inclusion poset. It includes
  nonemptiness and a common upper stage for any pair; parallel-arrow equalization
  is automatic for a poset. It is asserted, not assumed.
- Each finite stage is separable by `Algebra.IsSeparable K E.1` in the first
  part of the stage conjunction.
- Each is finite étale: finiteness is its index property, and étaleness is
  `Algebra.Etale K E.1`, the second part of the stage conjunction.
- Each is smooth over `K`: `Algebra.Smooth K E.1`, the third part. This is
  Mathlib's existing smooth-algebra notion, formally smooth and finitely presented.
  On affine spectra it agrees with the recorded scheme smoothness notion.
- `Nonempty (IsColimit (finiteSubextensionCocone K L))` asserts the full universal
  property, in `CommAlgCat K`, with apex exactly `L`. Both transition maps and cocone
  maps are the canonical `K`-algebra inclusions. Thus it is a filtered colimit of
  finite separable extensions, and the very same diagram is the claimed filtered
  colimit of smooth algebras. The last sentence needs no second presentation.

Dependency declarations read and used:

- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. This module is publicly imported;
  its affine ring notion is the existing `Algebra.Smooth` used in the conclusion.
  The dependency record explicitly identifies affine-local smooth ring maps with
  the formally smooth, locally finitely presented scheme notion (Stacks 02H6).
- `lem-weil-pbc-finite-separable-extension-etale`:
  `Algebra.Etale.of_finite_of_isSeparable` in
  `WeilConjectures.Mathlib.RingTheory.Etale.Field`. Its full signature has fields,
  an algebra, `Module.Finite`, and `Algebra.IsSeparable`, and concludes
  `Algebra.Etale`. The module is publicly imported and the proof docstring names
  this exact declaration. The node's Mathlib match was also read: the formally
  étale theorem together with finite presentation gives this same result.
- The remaining recorded proof dependency is imported without `public`:
  `AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale` in
  `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`. Its smoothness
  clause supplies the scheme form of the étale-to-smooth step.
- The construction reuses `IntermediateField.inclusion` and `IntermediateField.val`
  from Mathlib, and `CommAlgCat.of`, `CommAlgCat.ofHom`, `Cocone`, `IsColimit`, and
  `IsFiltered`. No dependency notion is copied or repaired.

The proof docstring gives every node proof step: finite simple extensions contain
each element; finite composita give common upper bounds and the bottom field
gives nonemptiness; the union is `L` and compatible algebra maps glue uniquely;
separability descends; finite separable stages are étale and then smooth; the
diagram and colimit are unchanged in the final smooth presentation.

Edge cases checked before drafting: `L = K` has the bottom intermediate field
and the identity inclusion. Infinite algebraic separable extensions require no
finite-dimensionality of `L`. Arbitrary characteristic, including imperfect
positive-characteristic bases, is allowed: separability is an explicit hypothesis.
The index cannot be empty, as the base field is a finite intermediate field.
The index is a subtype of the set of intermediate fields, in `Type v`, the same
universe as the stage carriers; no smallness or equality of `u` and `v` is imposed.
The colimit is in algebras, not in the category of fields, so it includes the
usual arbitrary commutative-algebra test objects.

Searches made (via `msearch.py` unless marked `rg`/`grep`):

- LeanSearch: `algebraic separable field extension is a filtered colimit of finite
  separable intermediate fields`. Eight results concerned separability inheritance,
  simple extensions, and separable closure membership. None supplied this
  filtered finite-stage colimit statement.
- LeanFinder: `An algebraic separable field extension is a filtered colimit of
  finite separable intermediate fields and finite etale smooth algebras`.
  Results included `Algebra.FormallyEtale.of_isSeparable`, its auxiliary theorem,
  `Algebra.Etale.iff_exists_algEquiv_prod`, formally smooth separably generated
  algebras, `Algebra.IsSeparable`, and a separably closed lift. These are inputs,
  not the colimit assertion.
- Loogle: `Algebra.IsSeparable, Algebra.Etale, IntermediateField`: zero hits.
- Mathlib grep: `finite.*[Cc]olimit|[Cc]olimit.*[Ii]ntermediate|[Ii]ntermediate.*[Cc]olimit`
  in `FieldTheory`: zero hits. Further direct searches of intermediate fields and
  algebra categories found the inclusion maps and general category interfaces,
  not this finite-stage statement or its diagram/cocone definitions.
- Source `rg`: `algebraic.*separable.*smooth|finite.*[Cc]olimit|[Cc]olimit.*[Ii]ntermediate`
  in `WeilConjectures/FieldTheory` and `WeilConjectures/Mathlib/FieldTheory` found
  the commentary in `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`. Its theorem
  `IsSepClosure.exists_intermediateField_mem` was opened: it assumes a separable
  closure and gives an elementwise finite subextension, so it is not this statement.
- Source `grep -rn 'lem-kun-algebraic-separable-smooth' WeilConjectures`: no hit.
- Project `rg` over `lean/Sheaf` found
  `FieldTheory.separable_extension_is_filtered_colimit_smooth` and
  `FieldTheory.fg_separable_extension_is_filtered_colimit_smooth`. Both modules
  were read. They assert smooth stages without asserting finite separable
  field stages, so neither states this node. The coefficient-field diagrams
  concern a fixed padic algebraic closure and do not give the arbitrary `L/K` system.
- Candidate declaration names were searched in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No new node, dependency repair, or statement dispute is required. Only the item's
`lean` field is changed. `scompile.py Q110 lem-kun-algebraic-separable-smooth`
compiled the delivered module cleanly against the server library, with no errors
or warnings. The prescribed `deliver2.py` wrapper performs preflight and repeats
the per-file compile for the dry run and delivery.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
