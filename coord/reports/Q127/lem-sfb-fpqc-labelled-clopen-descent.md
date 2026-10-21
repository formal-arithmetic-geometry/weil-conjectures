## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcLabelledClopenDescent` states
`AlgebraicGeometry.labelledClopenPartition_existsUnique_of_fpqc`, with its proof `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
The node copy changes only `lean`. The theorem docstring records all four proof steps
and the nodes used by them.

Read the item and all four statement-dependency records, their Mathlib declarations
and docstrings, both proof-dependency records, and the upstream compatible-open descent
theorem. Read Stacks `descent.tex`, Tag 03N0, `lemma-open-fpqc-covering` at line 4101,
and `topologies.tex`, Tag 022D, `lemma-fpqc` at line 3105, including their proofs.
These sources provide descent of the individual open label fibres and the base-change
covering used in the test-morphism clause.

Hypotheses, clause by clause:

- The base scheme is `{X : Scheme.{u}}`. The arbitrary covering index set is
  `{I : Type v}`; the source schemes are `{U : I → Scheme.{u}}`, and the morphisms
  are `(f : ∀ i, U i ⟶ X)`.
- The fpqc covering condition is
  `hf : Presieve.ofArrows U f ∈ Scheme.fpqcPrecoverage X`, using exactly the
  recorded dependency interface. It does not require individual covering arrows
  to be quasi-compact. Mathlib's `propQCPrecoverage` is the intersection of the
  quasi-compact-cover precoverage and the jointly-surjective flat precoverage.
  `QuasiCompactCover` uses finite affine-local refinements, as the node requires.
- The label set is `{A : Type w}`, with no topology, finiteness, decidable equality
  or nonemptiness instance required. `v` and `w` are independent universes.
- The functions are `(ρ : ∀ i, U i → A)`. The only fibre hypothesis is
  `hρ : ∀ (i : I) (a : A), IsOpen (ρ i ⁻¹' {a})`. Closed fibres are not assumed.
- `hcompat` says, for every `i j`,
  `ρ i ∘ pullback.fst (f i) (f j) = ρ j ∘ pullback.snd (f i) (f j)`.
  These are functions on the actual scheme fibre product, not on a Cartesian
  product of underlying point sets.

Conclusions, clause by clause:

- `∃! Z : A → X.Opens` gives the labelled family and uniqueness. An element of
  `X.Opens` is an actual open subset. Its standard open subscheme is
  `(Z a).toScheme`, and its canonical inclusion is `(Z a).ι`, an open immersion.
  The `Restrict` import supplies this structure; no extra choice or copied
  definition of an open subscheme is introduced.
- `∀ a, IsClosed (Z a : Set X)` supplies closedness of the already open pieces.
- `Pairwise (fun a b ↦ Disjoint (Z a) (Z b))` is disjointness for distinct labels.
  Disjointness in the lattice of opens is exactly disjointness of their subsets.
- `(⋃ a, (Z a : Set X)) = Set.univ` is exhaustiveness over all labels.
- `∀ (i : I) (a : A), f i ⁻¹' (Z a : Set X) = ρ i ⁻¹' {a}` gives precisely the
  prescribed inverse images.
- The final universally quantified clause introduces an arbitrary
  `(V : Scheme.{u})`, `(h : V ⟶ X)` and `(σ : V → A)`, without any regularity
  hypothesis on `σ`. Its premise is, for every `i`, equality of the two label
  functions after the first and second projections of `pullback (f i) h`.
- Its conclusion is, for every `a`,
  `h ⁻¹' (Z a : Set X) = σ ⁻¹' {a} ∧ IsClopen (σ ⁻¹' {a})`. This includes both
  the test inverse-image identity and the asserted openness and closedness of
  the fibres of `σ`.
- All properties, including the moreover clause, are inside the unique-existence
  predicate. This is equivalent to the node's uniqueness of the base family:
  the prescribed inverse images already determine each subset by joint
  surjectivity, and the test clause is then a property of that same family.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, read at lines
  35–45 and 73–76. Also uses the existing `Scheme.Opens` at line 71.
- `def-weil-pbc-fpqc-covering`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fpqcPrecoverage`, read at lines 56–64; read the
  underlying `propQCPrecoverage` in `Sites/QuasiCompact.lean` and
  `AlgebraicGeometry.QuasiCompactCover` in `Cover/QuasiCompact.lean`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`, read at
  lines 94–116. Existence for schemes is supplied by the existing imports.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, read at lines 34–39. The canonical open
  subscheme realization is `AlgebraicGeometry.Scheme.Opens.toScheme` and `ι`
  in `Mathlib.AlgebraicGeometry.Restrict`, lines 44–57, including the open
  immersion instance on `ι`.
- Proof dependency `lem-weil-pbc-open-subscheme-fpqc-descent`:
  `WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent`,
  `AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`. Read its full
  docstring and signature at lines 29–62. Its module is a non-public import.
- Proof dependency `lem-galois-fpqc-covering-base-change` is a Mathlib leaf:
  `CategoryTheory.Precoverage.mem_coverings_of_isPullback`, read at
  `Mathlib/CategoryTheory/Sites/Precoverage.lean`, lines 132–139, together with
  the base-change stability instance at `Sites/Fpqc.lean`, lines 60–64.
  This declaration is available through the fpqc import.

Edge cases checked before writing:

- `A` empty: every `U i` is empty because `ρ i` exists. Joint surjectivity forces
  `X` empty. The empty family has union `Set.univ` on the empty space. Test
  schemes mapping to the empty base are empty as well. No `Nonempty A` appears.
- `I` empty: the covering condition forces `X` empty. All prescribed inverse
  image and overlap conditions are vacuous. There is exactly one open subset of
  the empty base, hence exactly one family for any `A`.
- Empty components and empty test scheme impose no additional assumptions.
- A singleton label has one descended piece, the whole base. Unused labels
  produce empty pieces, which are permitted by the disjointness condition.
- Infinite `I` and infinite `A` are allowed; the complement of one piece is an
  arbitrary union of all the other open pieces. No finite instance is used.
- The base and the test scheme need not be quasi-compact. The same universe `u`
  for schemes is the standard universe-polymorphic category of schemes, not an
  independent smaller test universe. Index and label universes are unrestricted.

Searches actually run:

- `msearch.py ... leanfinder`, query: "Compatible locally constant labels on an
  arbitrary fpqc covering family of schemes descend uniquely to a clopen
  partition of the base and commute with test morphisms". Eight hits: affine
  transition-limit auxiliary lemmas, `CompHausLike.LocallyConstant.presheaf_ext`,
  and open-cover/gluing lemmas. None has the node's statement.
- `msearch.py ... loogle`, query: `AlgebraicGeometry.Scheme, IsClopen`.
  One hit: `Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber`, a statement
  about a point in a quasi-finite fibre, not descent of a labelled partition.
- `msearch.py ... leansearch`, query: "Fpqc descent of compatible open and closed
  labelled partitions of schemes". Eight hits, primarily descent of morphism
  properties and affine transition-limit auxiliary lemmas. Read the nearby
  open-immersion descent declaration in `Morphisms/FlatDescent.lean`: it concerns
  descent of a morphism property, not a labelled family of subsets.
- `msearch.py ... grep`, query: `fpqc|[Cc]lopen|[Ll]ocallyConstant`, subdirectory
  `AlgebraicGeometry`. Twenty-five hits, including fpqc topology definitions
  and `isSheaf_fpqcTopology_continuousMapPresheaf` in `Sites/ConstantSheaf.lean`.
  Read that file through its fpqc-sheaf theorem. The latter is a general sheaf
  property for continuous maps, not the node's explicit clopen partition,
  uniqueness and arbitrary-test-function conclusion.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the exact node id and
  for `fpqc.*[Cc]lopen|[Ll]abelled.*[Cc]lopen|fpqc.*[Ll]ocally[Cc]onstant`:
  no matching statement. Hits concerning labelled partitions elsewhere concern
  different coefficient constructions.
- Further `rg` on both projects' `AlgebraicGeometry` directories for
  `fpqc|[Cc]lopen.*[Dd]esc|[Ll]ocallyConstant.*[Dd]esc` found the compatible-open
  descent dependency and the specialized `EtaleOpenFpqcDescent` and pro-etale
  model-type-open results. Read these interfaces: none states arbitrary
  labelled clopen descent and its test-function clause.
- `rg` on `dag/lean_names_upstream.json` for clopen, label and locally constant
  names found unrelated clopen/rank/constant-sheaf statements. The proposed
  declaration name was also searched in Mathlib, both Lean roots and that name
  index; there was no collision.

No statement dispute or node fault was found. Initial `scompile.py` validation
compiled the delivered file in both sandbox and module contexts, cleanly with
no errors or warnings (10.3 seconds and 3.5 seconds respectively).

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
