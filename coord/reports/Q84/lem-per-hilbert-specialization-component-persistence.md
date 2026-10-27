## Worker report

The module `Sheaf.AlgebraicGeometry.HilbertSpecializationComponentPersistence` states
`AlgebraicGeometry.HilbertSamuel.components_eq_of_function_eq_specialization`, with one
`sorry` and no new definitions. The item's statement and proof are unchanged. Its
`stmt_deps` gains the already landed `def-trf-hilbert-samuel-invariant` so the sequence is
reused rather than redefined. No dependency repair, new node or statement correction is needed.

Hypotheses, definitions and conclusions, clause by clause:

- The schemes are `{X Z : Scheme.{u}}` for arbitrary explicit universe `u`. The rational
  field is `ULift.{u} ℚ`, the existing universe-compatible field lift, canonically
  isomorphic to ℚ. This allows every scheme universe without imposing smallness on X.
- The smooth ambient structure map is `p : Z ⟶ Spec (.of (ULift.{u} ℚ))` with `[Smooth p]`.
  Together with `[QuasiCompact p]` this is precisely a smooth finite-type Q-scheme:
  Mathlib derives `LocallyOfFiniteType p` from smoothness.
- The locally closed embedding is `i : X ⟶ Z` with `[IsImmersion i]`. Mathlib's
  `IsImmersion.isImmersion_iff_exists` identifies this with a closed immersion followed
  by an open immersion, exactly the immersion clause of `def-weil-closed-immersion`.
  The Q-structure on X is `i ≫ p`; `[QuasiCompact (i ≫ p)]` gives finite type, since
  Mathlib derives `LocallyOfFiniteType i` from the immersion and local finite type is
  stable under composition. Thus no extra local finite type hypothesis is needed.
- There is no `IsReduced`, generic reducedness, equidimensionality, separatedness or
  closed-point condition on X. The embedding is an immersion, allowing globally locally
  closed, rather than only globally closed, embeddings.
- The raw sequence `h_{X,u}` is the existing `HilbertSamuel.localFunction X u`, namely
  `(Module.length (X.presheaf.stalk u) ((X.presheaf.stalk u) ⧸
  IsLocalRing.maximalIdeal (X.presheaf.stalk u) ^ (n + 1))).toNat`.
  Finite type over a field gives a Noetherian local ring and finite lengths for these
  quotients, so `.toNat` is literal, not its infinite junk value.
- The existing `HilbertSamuel.summation` is inclusive summation `∑ i ∈ range (n+1), f i`.
  `HilbertSamuel.function (i ≫ p) u` iterates this summation by
  `Cardinal.toNat (Algebra.trdeg (ULift ℚ) (X.residueField u))`, with the canonical
  residue-field algebra from `(i ≫ p).residueFieldAlgebraMap u`. Residue fields of
  finite-type schemes have finite transcendence degree, so this is exactly the node's
  `Λ^{t_u} h_{X,u}`; the field lift does not change transcendence degree or length.
- The points are `(z x : X)`; `hspecializes : x ∈ closure ({z} : Set X)` writes the
  specified specialization with its orientation literally.
- `heq : function (i ≫ p) z = function (i ≫ p) x` is equality of entire natural-valued
  sequences, including index zero, not eventual equality or equality of polynomials.
- The first conclusion is `∀ C : Set X, C ∈ irreducibleComponents X →
  (x ∈ C ↔ z ∈ C)`. This concerns the same actual components of X through comparable
  points, not just an equality of numbers of components or possible dimensions.
- The second conclusion is equality of the two comprehensions
  `{d : WithBot ℕ∞ | ∃ C : Set X, C ∈ irreducibleComponents X ∧
  x ∈ C ∧ topologicalKrullDim C = d}` and the analogous comprehension at z.
  The dimension is the subspace topological Krull dimension of each component.
  Both directions and the explicit dimension-set consequence are retained.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, through the equivalent immersion interface in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `AlgebraicGeometry.IsImmersion` and
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `Mathlib.RingTheory.Length`, `Module.length`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` (canonical algebra construction used by
  the recorded invariant).
- `Mathlib.Topology.Irreducible`, `irreducibleComponents`.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`,
  `AlgebraicGeometry.HilbertSamuel.function`, `.localFunction` and `.summation`.

The source was read online at https://arxiv.org/html/0905.3580v1, sections 6.1--6.3,
including Remark 6.2; section 6.1 gives precisely the extended sequence in the statement.
The explicit component-retention assertion uses the node's schematic-closure argument,
not an assertion that arbitrary unrelated local rings have their component dimensions
recovered from one sequence. The module docstring carries all six steps and names their
DAG dependencies. Stated proof dependencies are imported privately, with repeated modules
included once. `lem-per-scheme-hilbert-samuel-test-presentations` and
`lem-trf-maximal-adic-graded-length-bridge` have no recorded declarations yet; no import
can be added for those until their modules exist. They are proof dependencies only and
no interface from them is needed to write this statement.

Edge cases checked before writing: the empty scheme has no points z,x, so the statement
has no inhabited point case; z=x gives identical component families; irreducible X has
one component; distinct comparable points are allowed and use their respective
transcendence degrees. The length uses n+1 also at n=0; at transcendence degree zero the
iteration is the identity. Nilpotents remain in the stalk quotients. A reducible scheme
with a new component through x cannot satisfy the sequence-equality hypothesis, as the
schematic-closure proof explains. No component dimension is replaced by local dimension.

Searches for existing statements and notions:

- `msearch.py ... leanfinder "Equality of extended Hilbert Samuel functions at specializing
  points preserves irreducible components"`: eight hits, including
  `Module.stableUnderSpecialization_support`, `genericPoints.component_ofComponent`, and
  stalk-specialization identities; none state this Hilbert--Samuel comparison.
- `msearch.py ... loogle '"HilbertSamuel"'`: zero hits.
- `msearch.py ... grep 'Hilbert.?Samuel|hilbertSamuel|extendedHilbert'`: zero Mathlib hits.
- `msearch.py ... leansearch 'Hilbert Samuel equality specialization irreducible components'`:
  eight hits, including `irreducibleComponents` and prime-spectrum/minimal-prime
  correspondences; none assert equality under equal extended sequences.
- `rg` of Hilbert--Samuel names in `lean/WeilConjectures`: no such invariant or statement;
  `rg` of the item id there also returned no match. Upstream declaration-name index and
  all Lean source were searched for `components_eq_of_function_eq_specialization`: no match.
- `rg` in `lean/Sheaf`: found and read `HilbertSamuelInvariant.lean`,
  `HilbertSamuelEqualityComponentRigidity.lean` and the smooth dimension profile module.
  The invariant is reused. Component rigidity concerns points on a blowup strict
  transform, assumes reducedness, and concludes equality of dimension sets, so is not
  this specialization statement about the very same components of X.
- DAG search of Hilbert--Samuel functions found the landed definition node
  `def-trf-hilbert-samuel-invariant`, whose full statement and Lean source were read.

Validation: `scompile.py Q84 lem-per-hilbert-specialization-component-persistence` compiled
both sandbox and library-module names cleanly (6.3 s and 3.4 s); no warnings or errors.

## Second reading by Q84

I reread the complete node and delivered module after compiling. This is a worker
self-check; the maintainer's independent review remains the independent reading required
by the dispatch brief. No second agent was started, as instructed by the dispatcher.

The field lift, smooth quasi-compact ambient scheme, immersion, quasi-compact intrinsic
structure map, arbitrary points, directed specialization, sequence equality, component
membership iff and explicit equality of dimension sets match the node as detailed above.
In particular finite type was checked against the Mathlib implication from immersions
and smooth morphisms, not silently dropped. The previously landed summation convention
has n+1 terms and uses residue-field transcendence degree, not dimension of the ambient
scheme. No theorem for unrelated local rings or reduced schemes was substituted. No
statement mismatch or node fault was found, and no correction was made.
