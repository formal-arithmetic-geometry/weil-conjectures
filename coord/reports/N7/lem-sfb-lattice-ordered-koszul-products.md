## Worker report

The module `Sheaf.CategoryTheory.LatticeOrderedKoszulProducts` states
`Profinite.DiscreteLattice.OrderedKoszul.lattice_ordered_koszul_products`.
Its only postponed theorem is this theorem, with all six DAG proof steps in its
docstring. The definitions have real data; the `Products` structure is the complete
conclusion, and the theorem asserts its existence. No node statement was changed.

Hypotheses and clauses, checked against the node:

- Arbitrary commutative condensed ring: `R : Profinite.CondensedRing.{u}` and
  `[IsCommMonObj R.X]`. The recorded coherent profinite site and internal modules
  are inherited through `DiscreteLattice.Modules`. There is no topological-ring
  presentation, nonzero, characteristic, completeness, or flatness hypothesis.
- Rank: arbitrary `r : ℕ`, including zero. Discrete lattice and trivial action are
  the recorded `Equivariant R r` and its tensor unit. `Mon.trivial` is precisely
  the regular coefficient algebra with that trivial action.
- Existing complex and pairing: bind the recorded `KoszulModel R r`, its
  `Comparison R r K`, and `TriangulatedCup.CupComparison` for that regular algebra.
  The existing comparison theorem supplies these; the theorem works for every
  such normalized model and cup, rather than introducing a second Koszul object.
  The cup's `coordinates` are exactly the stated disjoint-shuffle formula, including
  the inversion sign. Its twist operator is the identity on this trivial action.
- `S_q`: `single R q` is Mathlib's single complex in degree q, with regular module
  as its coefficient. `single_shift` and `single_shift_coordinates` explicitly
  identify it with `R[0][-q]`, with identity coefficient and no sign.
- Zero differential: `Products.differential_zero`, for all integral a,b.
- Subset inclusions: `incl` is a chain map from `single R I.card`;
  `incl_coordinates` makes its I component the identity and every other component
  zero. Outside this degree the source is zero.
- Canonical direct-sum decomposition: `decomposition` is an actual complex
  isomorphism; `decomposition_incl` identifies every one of its summand maps with
  the prescribed inclusion. This pins the isomorphism, including the empty subset.
- K-flatness: `kflat` quantifies over every acyclic complex E and asserts acyclicity
  of the ordinary total tensor K tensor E.
- Ordered shift-tensor comparison: `mul p q` is an isomorphism of the specified
  single complexes. `mul_coordinates` sets its unique component to the regular
  left unitor `R tensor_R R -> R`, without a sign. This uniquely characterizes the
  source's first-then-second shift extraction: the first comparison is unsigned,
  and the second acts in first-factor degree zero. No symmetry is inserted.
- Binary chain equality: `binary`, with `Disjoint A C`; its scalar is the cardinality
  of the filtered product `{(a,c) | c<a}` raised as the exponent of -1. A transport
  along `card_union_of_disjoint` only identifies source degrees. The overlap branch
  is the zero chain map.
- Increasing iterated products: `orderedProduct` is genuine recursion, starting at
  `incl ∅` and appending a singleton with `mul q 1` inverse and the original star.
  `increasing` asserts equality with the image-subset inclusion for every strictly
  increasing `Fin q -> Fin r`, including q=0. Equality of chain maps includes zero
  in every other component, and the surviving coefficient is +1. The proof's
  consecutive-block argument makes any ordered rebracketing give this same map.
- Empty product and canonical unit: the base recursion is `incl ∅`, and
  `empty_unit` identifies it with the recorded cup unit.
- Localization and derived tensor: `tensor_model` asserts invertibility of the
  canonical localization tensorator on all pairs of single complexes. The cup's
  existing `tensorModel` does the same for K. `derived_binary` gives the signed
  formula with `Functor.LaxMonoidal.μ DerivedCategory.Q` on each side, explicitly
  exhibiting Q(star) as the derived pairing. `derivedOrderedProduct` uses the actual
  inverse tensorator, with its proof supplied by `tensor_model`, and
  `derived_increasing` gives the localized equality for all increasing lists.
  The empty recursion is Q of the empty inclusion, hence also retains the unit.
- Rank zero: `rank_zero_iso` and `rank_zero_coordinates` identify K with R[0] by
  its unique empty coordinate; `rank_zero_identity` states that the empty inclusion
  becomes the identity under exactly this identification.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`;
  the module-object structure and its morphisms are the existing Mathlib notions.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`;
  no private replacement of internal modules or their action notion.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`. The localization universe is u+2,
  the one already selected by the recorded lattice model.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `Modules`, `Group`,
  `Equivariant`, `Subsets`, `KoszulModel`, `Comparison`, and
  `discrete_lattice_koszul_resolution`.
- `Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison`:
  `TriangulatedCup.CupComparison`, its coordinates, unit and tensorModel, and
  `lattice_koszul_triangulated_cup_comparison`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: the canonical relative
  `Mod.monoidalCategory`, its regular unit and induced unitors.
- `Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor`: `DerivedCup.trivial`,
  `moduleHasDerivedTensor` and the normalized ordinary K-flat localization tensor.
- Proof imports: `Sheaf.CategoryTheory.RelativeTensorFiniteFreeCoordinates`,
  `CategoryTheory.sfb_relative_tensor_finite_free_coordinates`; and
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctorShift₁Iso`,
  `mapBifunctorShift₂Iso` and their component formulas. The latter is the recorded
  Mathlib match, not a dependency lacking a Lean statement.
- `def-weil-size-convention` is explicitly a metatheoretic convention; it has no
  declaration to import. Explicit universe u and the existing u+2 localization
  implement it without restricting rings or categories.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
This item is the agent-extracted algebraic normalization below that paragraph;
its exact internal-module reference remains WANTED as the node already records.
The six DAG proof steps are reproduced in the theorem docstring without changing
that provenance.

Searches:

- msearch leanfinder: “Ordered products of singleton subset inclusions in a zero
  differential Koszul complex of internal modules”: eight hits, including
  `ExteriorAlgebra.ι_mul_prod_list` and `HomologicalComplex.single_obj_d`.
  The former is an element identity in an ordinary exterior algebra, not this
  internal complex-map statement; the latter only supplies the single differential.
- msearch loogle: `"ExteriorAlgebra", "prod"`: twelve hits about ordinary exterior
  algebra products and its product equivalence, no internal complex or localized
  ordered-subset statement.
- msearch grep: `koszul.*(mul|prod|cup)|(mul|prod|cup).*koszul`: zero Mathlib hits.
- msearch leansearch: “Subset inclusion morphisms in a Koszul complex multiply with
  shuffle inversion signs and increasing products have coefficient one”: eight
  hits, including `HomologicalComplex.ιTensorObj` and total-complex inclusions;
  none states this result.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for ordered Koszul terms and this
  blueprint id: found unrelated ringed completion complexes and the existing
  `DiscreteLatticeCupExterior` consumer. Read that consumer: it proves that the
  exterior cup arrow is invertible, not this binary and ordered chain formula.
  No exact statement already exists. Reused all recorded Koszul/cup constructions.

Edge cases checked before writing: r=0 leaves only the empty coordinate, r=1 has
one degree-one inclusion with square zero, r=2 reverses the two singleton factors
with sign -1, and in r=3 the product of {0,2} and {1} has sign -1. Empty factors
have zero inversions and regular unitor multiplication. Increasing lists longer
than r do not exist; q=0 is allowed. Over the zero ring all morphisms are the unique
zero morphisms, including identities; in characteristic two minus signs coincide
with plus signs. Negative complex degrees have no subset labels. No dispute or
statement correction was necessary.

## Second reading by N7

Dispatcher instruction prohibits starting another agent; this is a separate self-review,
not a claim of an independent worker's review. Reopened the node and module and matched
the clauses listed above. Found that merely asserting invertibility of the rank-zero
inclusion would leave the specific identity implicit; replaced it with the coordinate
isomorphism and its explicit identity equation. Added the single-shift isomorphism with
identity coefficient so the alternative single-complex presentation is explicit. Checked
that the derived recursion uses invertibility asserted in the conclusion, not an extra
hypothesis on R. Checked the unit, overlap branch, inversion direction, first-then-second
unsigned convention, empty list, and the full original-site universe convention. All data
are existing constructions or structure fields whose existence is the theorem's precise
conclusion; the only sorry is the named item theorem.
