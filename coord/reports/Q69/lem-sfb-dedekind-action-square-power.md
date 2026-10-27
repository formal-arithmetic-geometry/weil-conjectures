## Worker report

The module `Sheaf.AlgebraicGeometry.DedekindActionSquarePower` states
`AlgebraicGeometry.exists_tensorPow_square_of_dedekind_action`, with proof `sorry`.
There are no new definitions, dependency modules, or statement corrections. The item JSON
changes only in `lean`; its signature is copied verbatim from the delivered file.

I read the item, all twelve statement-dependency node statements and their recorded Lean
interfaces, their declaration signatures and docstrings, and the stated proof-dependency
module records. The CompactObject example has been withdrawn and contains no declarations;
I followed the module/header convention shown by the existing NormalGroupSquarePower and
SquareActionGenerationLocusStable modules instead.

Source read: [BLR, Neron Models, primary scan](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf),
6.3, printed pp.148–151 (PDF pp.154–157): the definition preceding Theorem 1, Theorem 1,
and the universal square difference and generic-fibre reduction of Lemma 2. The theorem
applies to the affine dimension-at-most-one base and extra separatedness assumptions of
this node. Its functorial definition takes classes modulo base lines on every test scheme;
the statement below expresses equality of those classes as existence of a base line and
an isomorphism. It asks for neither choices nor coherence.

Hypothesis-by-hypothesis and clause-by-clause comparison:

| Node text | Lean rendering |
| --- | --- |
| D is a Noetherian integrally closed domain | `D : Type u`, `[CommRing D]`, `[IsDomain D]`, `[IsNoetherianRing D]`, `[IsIntegrallyClosed D]` |
| Krull dimension at most one | `hdim : ringKrullDim D ≤ 1` |
| S = Spec D | Both `H` and `X` have type `Over (Spec (CommRingCat.of D))` |
| K = Frac D with its canonical D-algebra structure | `FractionRing D` and `algebraMap D (FractionRing D)` |
| H is a group scheme over S | `[GrpObj H]` in `Over S`; its multiplication, inverse, identity and laws are Mathlib's existing internal group structure |
| H is smooth, separated, finite type | `[Smooth H.hom]`, `[IsSeparated H.hom]`, `[LocallyOfFiniteType H.hom]`, `[QuasiCompact H.hom]` |
| H has geometrically connected fibres | `[GeometricallyConnected H.hom]`, equivalent to geometric connectedness of every residue-field fibre |
| X is smooth, separated, finite type over S | The same four morphism classes on `X.hom` |
| The action has unit and associativity | `[ModObj H X]`; `smul` is an S-morphism and `one_smul`, `mul_smul` are exactly its two action identities |
| The generic fibre X_K | `pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))))` |
| X_K is nonempty and geometrically connected | `hgeneric : GeometricallyConnected (pullback.snd X.hom ...)`; geometric connectedness uses `ConnectedSpace`, which includes nonemptiness, including for the identity field extension |
| L is an invertible O_X-module | `L : X.left.Modules`, `[L.IsInvertible]` |
| There exists one integer r ≥ 1 | `∃ r : ℕ, 1 ≤ r ∧ ...`; positive integer exponents and positive natural exponents are the same range |
| M = L to the r-th tensor power | Every occurrence is `L.tensorPow r`, using the existing module tensor power |
| For every S-scheme B and two B-points g,h | `∀ (B : Over (Spec (CommRingCat.of D))) (g h : B ⟶ H)` |
| X_B, its two projections | `X ⊗ B` in `Over S`, with `fst X B`, `snd X B`; this is canonically the chosen scheme pullback |
| M_B | `(Scheme.Modules.tensorPullback (fst X B).left).obj (L.tensorPow r)` |
| Translation by g, followed by projection to X | `((snd X B ≫ g) • fst X B).left` |
| Product translation | Replace g by `(g * h)` in the preceding expression; the point-group multiplication has exactly this order |
| There is an invertible line N on B | `∃ N : B.left.Modules, N.IsInvertible ∧ ...` |
| q_B-star N | `(Scheme.Modules.tensorPullback (snd X B).left).obj N` |
| The square isomorphism | `Nonempty` of the displayed isomorphism: product-translation pullback tensor M_B equals g-translation pullback tensor h-translation pullback tensor q_B-star N |
| No chosen isomorphisms/coherence | Both N and the isomorphism occur only in existential propositions, after B,g,h |

The translation expression is the composite of the actual base-changed translation with
`X_B → X`: on generalized points it sends `(x,b)` to `g(b)·x`. Thus its pullback of M is
canonically `tau_g^* M_B` by `tensorPullbackSectionComp`. This expands a canonical
composite rather than adding arbitrary maps or stronger assumptions. The tensor
parenthesization differs only by the existing associator. The existing `tensorPow` starts
at the monoidal unit and tensors on the left; for positive exponents it is canonically the
same tensor power as the node's convention.

Dependency interfaces used (imports are public for statement dependencies):

- `def-weil-affine-spectrum`, `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`, `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and its imported
  `AlgebraicGeometry.QuasiCompact`.
- `def-weil-connected-scheme`: Mathlib `ConnectedSpace` (the dependency's `mathlib_match`,
  not a missing record). Nonemptiness is part of this exact class.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`,
  imported through `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`; it works over every
  base S without specializing the base to a field. The action uses Mathlib's
  `CategoryTheory.ModObj` and the induced Hom action in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`; no private action definition.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, imported by
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`; `IsSeparated` is exactly closedness of
  the diagonal, rather than an unrelated topological separation condition.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.snd`; `Over S`
  products are identified with scheme pullbacks by `Over.prodLeftIsoPullback`.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, and its existing tensor
  category instance. The same source proves its sheaf tensor interpretation.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly importing
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; its section-normalized composition
  interface identifies the composite action pullbacks above.
- `def-pc-geometrically-irreducible`: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` is imported, together with
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`, whose
  `AlgebraicGeometry.GeometricallyConnected` is explicitly named by the node's match/note.
- `def-pur-sheaf-tensor-product`: the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is imported; scheme
  modules use the existing sheaf tensor monoidal structure, not a new tensor.

The stated proof-dependency modules are imported without `public`, including regular local
normality/dimension one, smooth regular ascent, smooth connected generic geometry,
regular/normal decomposition, FieldProductSquarePower, InvertibleAffineLimitDescent, and
RegularLocalUFDBoundaryFactorization, plus the recorded Mathlib proper/base-change, Noetherian, torsion-free,
quasi-separated and finite-presentation modules and the upstream closed
`Smooth.flat_and_locallyOfFinitePresentation` module. Proof-only nodes not yet recorded are cited in the eight-step
docstring but are not invented or duplicated here. There is only one postponed theorem,
and the docstring carries all eight steps, including the corrected projection to X and
the normalization at the pair of identity sections.

Edge cases checked before writing:

- D a field has dimension zero and is allowed; no nonfield or dimension-equals-one binder.
- The empty X or an empty generic fibre fails geometric connectedness because
  `ConnectedSpace` includes `Nonempty`; no accidental preconnectedness substitution.
- Empty, nonreduced, disconnected, and non-quasi-compact B are all allowed: the conclusion
  binds every object of `Over S` and puts no extra class on B.
- X may have empty or disconnected special fibres. In particular an open generic-fibre
  model over a DVR is not excluded by a surjectivity or all-fibres-connected assumption.
- H need not be commutative; `(g * h)` is kept in that order, with left translation.
- Trivial group/action and the structure line cause no spurious exclusions; exponent one
  remains available. Exponent zero is explicitly excluded.
- `universe u` is explicit for the base ring and all schemes, including B and the fraction
  field. This is the project's standard fixed universe of schemes, with no independent
  test-field universe that could make a hypothesis vacuous. Auto implicits are disabled.

Searches for an existing statement (all returned results read):

- `msearch.py ... leanfinder`, query: "Theorem of the square for a smooth group scheme
  acting on a smooth scheme over a Dedekind domain: a positive tensor power of any
  invertible sheaf satisfies the square condition". Eight hits: ring Picard group tensor
  identities, formally unramified Spec maps, and scheme tensor/pullback congruences;
  no action square-power theorem.
- `msearch.py ... leansearch`, query: "A positive tensor power of a line bundle satisfies
  the theorem of the square for a smooth group action over a Dedekind domain". Eight hits
  concerning `TensorPower` and linear maps on tensor products; no scheme-action result.
- `msearch.py ... loogle`, query: "GrpObj, Action, tensorPullback". Zero hits, with index
  diagnostic `unknown identifier 'GrpObj'`; not treated as positive evidence of absence.
- `msearch.py ... grep`, query:
  `[Ss]quare[Cc]ondition|square_condition|[Tt]heorem.of.the.[Ss]quare`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for square-condition and theorem of
  the square spellings. Relevant results: `NormalGroupSquarePower` is only the
  multiplication action X = H, while `SquareActionGenerationLocusStable` and
  `SquareActionProjImmersionLocusStable` assume the square condition rather than produce
  a power. `FieldProductSquarePower` is the proof input, not the same theorem.
- `rg` for `lem-sfb-dedekind-action-square-power` in `lean/WeilConjectures`: no hit.
  Name collision search for `exists_tensorPow_square_of_dedekind_action` in Mathlib/project
  and upstream-name metadata found no declaration.

No node fault or disputed statement was found. The existing action, group, tensor and
pullback definitions suffice, so no new node is needed.

Validation: `scompile.py Q69 lem-sfb-dedekind-action-square-power` compiled the delivered
final file in both sandbox and library contexts successfully (28.7 s and 1.7 s), under the
standard 60-second per-file limit. All binders are explicit, every line is at most
100 characters, and the only theorem body is `sorry`.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
