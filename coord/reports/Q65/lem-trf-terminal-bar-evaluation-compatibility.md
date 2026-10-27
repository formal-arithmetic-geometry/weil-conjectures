## Worker report

The module `Sheaf.CategoryTheory.TerminalBarEvaluationCompatibility` states
`CategoryTheory.terminalBarCompatibility`, with proof `sorry`. It asserts the full
`TerminalBarCompatibility` proposition. Its other declarations are real definitions
of the comparison, two generator-formula predicates, the point-selecting functor, and
the proposition packaging the assertion. No data are selected from an unproved theorem.
The source is Stacks, sites-cohomology.tex, 08PG (example-left-derived-colimits),
08PH (example-morphism-categories), 08Q9 (lemma-compute-by-cosimplicial-resolution),
and cotangent.tex, 08QV (lemma-polynomial-on-top). These source passages were read.

Hypotheses and objects:

- The size convention is the explicit `universe u`; `E : Type u` with
  `[SmallCategory E]`, `R : Type u` with `[CommRing R]`, and
  `F : Eᵒᵖ ⥤ ModuleCat.{u} R`. We use the dependency's notation `E = Jᵒᵖ`,
  so `F` is the covariant coefficient diagram of the node. This is a reparametrization
  by opposites, with no condition on the ordinary category beyond smallness.
- The existing `B : CategoryColimitBarSystem.{u}` is explicitly supplied, not chosen
  from its existence theorem. `B.models E R` is precisely the recorded reversed-face
  bar model for the identity-cover site. Its `coordinates`, `positive`, and
  `differential` fields give the direct sums, positive-degree zero objects and faces.
- The first-vertex dependency already uses the SAME complex with signed coordinates
  `SimplicialDerivedColimit.forwardGenerator B F n a`. Its `Computation.forwardDifferential`
  reverses the face numbering and gives first-vertex alternating signs; its
  `Computation.forwardMap` gives the unchanged string-reindexing formula. A second
  construction of that complex would duplicate its notion. Therefore the comparison
  `terminalBarSignIso` is `Iso.refl` on the underlying realized complex. This is an
  isomorphism between the two coordinate realizations; it does not claim that the two
  originally unsigned differential matrices are equal.
- Terminality is `(t : E) (ht : IsInitial t)`: on `J`, every `j` has exactly one
  morphism to `t`. `ht.to a.right` is the opposite of that morphism. No terminality
  is required of the arbitrarily reindexed category `D`.

Conclusion, clause by clause:

- `TerminalBarCompatibility.sign` says on EVERY degree `-n` summand that the
  comparison takes the reversed generator to
  `(-1 : ℤ) ^ (n * (n + 1) / 2) • forwardGenerator ...`. Because the latter
  generator itself is the dependency's signed coordinate, this states exactly the
  specified scalar matrix, with the same inverse since the sign squares to one.
  The type of `terminalBarSignIso` is an isomorphism of cochain complexes.
- `degreeZero` states that its degree-zero component is identity.
  `coefficientNaturality` states its strict square for every natural coefficient map;
  `reindexNaturality` states the strict square for every indexing functor, allowing
  also a natural coefficient map. The existing first-vertex model uses the same
  `B.map` in its signed coordinates, as specified in its `forwardMap` field.
- `IsBarCoconeAugmentation` renders the degree-zero formula for any cocone and
  makes every other component zero. `coconeCompatibility` says the sign comparison
  commutes with every such augmentation, as a chain-map equality.
- `terminal` asserts existence of a chain map `e` to
  `(CochainComplex.singleFunctor _ 0).obj (F.obj (op t))`, i.e. `H(t)[0]`.
  `IsTerminalBarAugmentation` makes its degree-zero component on a summand equal
  to `F.map (ht.to a.right).op`, and every other component zero. The following
  quantified clause proves uniqueness among ALL chain maps with these formulas,
  independently of the later quasi-isomorphism and compatibility properties.
- The conjuncts `QuasiIso e` and `IsIso (DerivedCategory.Q.map e)` are exactly the
  quasi-isomorphism and consequent isomorphism in `D(R)`.
- The universally quantified `v : D ⥤ E` clause uses the actual chain map
  `B.map v (RingHom.id R) (𝟙 (v.op ⋙ F)) ≫ e`. Its degree-zero value on every
  generator is `F.map (ht.to (v.obj a.right)).op`; every other component is zero.
  Thus it is precisely the map from the pullback diagram specified in the node.
  The last equality of this clause states the same strict composite after the
  source sign comparison. The terminal sign comparison commutes by degreeZero
  and the displayed augmentation formula; reindexNaturality supplies its square.
- `terminalBarPoint t : Discrete PUnit ⥤ E` selects `t`. On opposite categories
  this is the node's functor from the one-object identity category to `J`.
  Its pullback coefficient is canonically the constant coefficient `H(t)`:
  every arrow maps to `F.map (𝟙 _) = 𝟙 _`. We retain the literal pullback to
  make the reindexing map type-correct without arbitrary coefficient identifications.
  The `ePoint` clause states the canonical point augmentation by the identity on
  EVERY degree-zero summand and zero components elsewhere, and asserts
  `B.map (terminalBarPoint t) ... ≫ e = ePoint` as a chain-map equality.
  These component formulas determine `ePoint` uniquely. The final equality is
  that same identity after the first-vertex comparison. The point differential
  is the canonical alternating sum of identity faces, by the existing bar model.

Dependency declarations used:

- `Sheaf.CategoryTheory.DerivedColimitBar`:
  `CategoryTheory.CategoryColimitBarSystem`, its `models`, `map`, `formula`, and
  `CategoryColimitBarModel.generator`; its standard module-derived-category instance.
  The complete model and system records, generator definition, and existence theorem
  docstring/signature were read. No replacement of a dependency is required.
- `Sheaf.CategoryTheory.SimplicialDerivedColimitComputation`:
  `CategoryTheory.SimplicialDerivedColimit.forwardGenerator`, and the recorded
  first-vertex interpretation in `Computation.forwardDifferential` and `forwardMap`.
  Its module, helper definitions, full record, and `computation_exists` signature and
  docstring were read. We need only the already defined signed generators in the file.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and inversion of quasi-isomorphisms;
  these signatures and docstrings were read. This is the recorded abstract derived
  category dependency. The size-convention dependency is metatheoretic and has no
  module/declaration to import.
- `Mathlib.CategoryTheory.Limits.Shapes.Terminal`: `IsInitial` and its unique arrows;
  `CochainComplex.singleFunctor` and `HomologicalComplex.singleObjXSelf` give the
  actual degree-zero target and its canonical component identification.

Edge cases checked before writing: an empty indexing category is allowed in the sign
and cocone clauses, and as `D` in reindexing; the terminal clause requires an actual
terminal object and hence does not assert one exists in the empty category. At `n=0`
the exponent is zero and the comparison is identity. At `n=1` the sign is minus one,
converting the reversed boundary to the usual first-vertex boundary. The point has
all faces identity, hence alternating differential zero in odd chain degrees and
identity in even positive chain degrees; its degree-zero augmentation is identity.
Zero modules, the zero ring, characteristic two, non-poset categories and infinitely
many objects/arrows are retained. There is no flatness, projectivity, finite-category,
resolution, or contractibility hypothesis. Initial objects of `E` are exactly the
terminal objects needed in the covariant category `Eᵒᵖ`.

Searches performed with `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- leanfinder: "Terminal object bar complex augmentation quasi-isomorphism compatible
  with reversing face numbering and reindexing". Eight hits, including monoid
  standard resolutions, `ExtraDegeneracy.homotopyEquiv`, and alternating constant
  complex comparisons. None gives the arbitrary-category assertion with the recorded
  two bar conventions and strict reindexing formulas.
- loogle: `"bar", "IsTerminal"`. Zero hits.
- grep: `[Bb]ar.*[Tt]erminal|[Tt]erminal.*[Bb]ar`. Zero Mathlib hits.
- leansearch: "Terminal object evaluation of a category bar complex is a
  quasi-isomorphism with strict reindexing compatibility". Eight hits, all general
  quasi-isomorphism definitions/closure results, no statement matching this item.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` with the terminal/bar pattern found
  only `PreorderBarTerminalAugmentation` and importers. That module was read: it is
  the specialized preorder/bar-totalization construction, not this arbitrary-category
  coefficient model and sign compatibility. `grep -rn` of the item id on
  `lean/WeilConjectures` returned no hit. Exact-name `rg` for all six new declaration
  names in Mathlib, `WeilConjectures`, and `Sheaf` returned no hit.

No statement correction, disputed statement, new DAG node, or dependency repair is
needed. The node copy changes only `lean`. Every public declaration carries the
item's source/blueprint docstring. The theorem docstring gives all five proof steps,
including the terminal contraction and degree-zero endpoint.

Validation: prescribed `scompile.py Q65 lem-trf-terminal-bar-evaluation-compatibility`
compiled the module cleanly in both sandbox and library contexts (12.7 s and 11.1 s).
`set_option autoImplicit false` forbids auto-bound variables. A direct line-width
check found no line above 100 characters. No other file was edited in the read clone.

## Delivery review

The dispatcher explicitly assigns a single worker and forbids starting other agents;
the maintainer performs the independent review after delivery. This report's detailed
clause mapping is the worker's own check, not a claim of an independent second reading.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
