## Worker report

The module `Sheaf.AlgebraicGeometry.StableAndSmoothFamilyOpenLoci` states
`AlgebraicGeometry.stable_and_smooth_family_open_loci`, with its only theorem proof
postponed by `sorry`. No statement correction is made.

Hypothesis and clause correspondence:

- Field: `(k : Type u) [Field k]`; no characteristic restriction.
- Genus: `(g : ℕ) (hg : 2 ≤ g)`.
- Ambient stack of flat proper finitely presented algebraic-space families with geometric
  dimension at most one: `ProperCurveModuli (Spec (.of k))`, using its existing `family`,
  `projection`, and `isCurve` data. Sources are algebraic spaces, not assumed schemes.
- The stable and smooth opens for every family are the dependent functions `stableOpen`
  and `smoothOpen`, with values in `X.base.left.Opens`. An open is used as a scheme via
  `.toScheme` and its inclusion `.ι`.
- Stable universal property: for every `T : Over (Spec (.of k))` and `h : T ⟶ X.base`,
  the existence of `l` with `l ≫ (stableOpen X).ι = h.left` is equivalent to
  `IsStableGenusSpaceFamily g T` of the actual presheaf pullback and its second projection.
- `IsStableGenusSpaceFamily` is a helper predicate belonging to this node, not a new
  stable-curve definition. Its witness `Y : StablePointedModuli S g 0` uses the recorded
  `IsStablePointedCurve`, with zero labelled sections, all normalized-component stability
  inequalities, nonempty connected reduced pure one-dimensional nodal geometric fibres,
  the projective-bundle convention, and the exact geometric H1 genus condition.
  The base isomorphism `b : Y.base ≅ T`, source-presheaf isomorphism `e`, and equation
  `e.hom ≫ yoneda.map (Over.homMk Y.projection rfl) ≫ yoneda.map b.hom = f`
  require the represented family to be the given family over its specified base.
  Thus this is neither a bare existence of an unrelated stable curve nor a chosen
  embedding as part of its moduli data. An isomorphic base avoids equality transports.
- Arbitrary base change compatibility: for every cartesian arrow `a : Y ⟶ X`, both
  opens of `Y` equal the inverse images of the opens of `X` under `a.base.left`.
  In `ProperCurveModuli` arrows are precisely cartesian squares, so this covers every
  chosen representative of every scheme pullback, including isomorphic ones.
- Scheme source and finite locally free projective-bundle embedding over the stable
  open: `HasFiniteLocallyFreeProjectiveRealization` applied to the presheaf pullback
  along that inclusion and its actual second projection. This second helper predicate
  has an actual scheme `Y`, structural morphism `p`, and a representing isomorphism `e`
  with `e.hom ≫ f = yoneda.map p`. The module `E` is quasi-coherent and
  `E.IsFiniteLocallyFree` (variable finite local rank is allowed). The map `i` is a closed
  immersion into `SymmetricAlgebraSheaf.gradedAlgebraData E hE |>.relProj`, the recorded
  quotient projective bundle, and its composite with `.relProjHom` is exactly `p.left`.
  No globally constant rank, Noetherian hypothesis, or quasi-compact base is imposed.
- Open substack: `∃ A : OpenModuliSubstack (ProperCurveModuli.category ...)` with
  `A.property X ↔ IsStableGenusSpaceFamily ...`. This is the full subcategory with all
  original isomorphisms, and its existing definition includes the actual 2-fibre-product
  scheme tests, the correct projections, and pullback stability.
- Containment in the nodal substack: `A.property X → X.family.HasNonemptyNodalGeometricFibres`.
- Smooth whole-family open: factorization through `smoothOpen X` is equivalent to
  `Smooth` for every representable etale scheme chart of the pulled-back presheaf,
  with the structural map obtained by `yoneda.preimage` of the chart map followed by
  the actual second projection. This tests the whole pulled-back algebraic space,
  and does not impose genus, connectedness, or nonemptiness on the smooth family.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (through the existing imported framework).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`: `IsStablePointedCurve`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`;
  its full stable predicate and geometric module-cohomology genus field are reused.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`, `ProperCurveModuli`,
  `ProperCurveModuli.category`, its cartesian `Hom`, and the existing chartwise properties.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`.
- `Sheaf.AlgebraicGeometry.CurveModuliGroupoids`: `HasNonemptyNodalGeometricFibres`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, allowing varying local ranks.
- The stable-curve imports provide the existing canonical symmetric graded algebra and
  projective bundle, `SymmetricAlgebraSheaf.gradedAlgebraData`.
- Proof-only import `Sheaf.AlgebraicGeometry.NodalCurveStackSmooth` supplies
  `nodal_curve_stack_smooth`. The other six geometric proof lemmas currently have
  no Lean records and hence no modules to import; they are named step by step in the
  theorem docstring. They are proof inputs, not missing notions needed for this signature.

The four additional statement dependencies are already landed definition nodes:
`def-sfb-proper-curve-moduli`, `def-sfb-open-moduli-substack`,
`def-sfb-curve-moduli-groupoids`, and `def-amb-finite-locally-free-module`.
There are no new DAG nodes and no replacement dependency modules. Both helper predicates
only package the scheme-representation clauses of this item's own assertion, using real
definitions throughout; neither introduces postponed proof obligations.

Source reading: Stacks `moduli-curves.tex`, `lemma-stable-curves` (0E76),
`lemma-stable-one-piece-per-genus` (0E78), `lemma-smooth-curves` (0DZZ), and
`lemma-smooth-dense` (0E86); `curves.tex`, `lemma-tricanonical` (0E8X).
The canonical-positivity and relative-evaluation arguments are retained in the docstring,
including how the finite locally free embedding strengthens scheme representability.

Edge cases checked: the empty base makes geometric conditions vacuous but permits its
empty stable family; an empty source over a nonempty base has empty stable locus and
whole smooth locus; zero-dimensional smooth fibres are included in the smooth locus,
while the stable condition requires pure dimension one; self-nodes count both branches
in the imported predicate; disconnected curves cannot become stable because the existing
stable object requires connected geometric fibres; all characteristics and arbitrary
nonreduced bases are allowed. The local rank of `E` may vary on disconnected bases.
Every universe is explicit, `set_option autoImplicit false` is enabled, and the field,
chart, presheaf-value, and scheme universes follow the recorded big-site convention.

Searches for an existing statement:

- `msearch.py ... leanfinder "Stable genus and smooth-family open loci for proper flat
  finitely presented families of curves"`: eight hits concerning smooth morphisms,
  smooth relative dimension, and permanence; none asserts this stable-family open.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, IsOpen"`: zero hits.
- `msearch.py ... leansearch "open locus in the base of a proper flat curve family where
  its fibres are stable curves"`: eight hits about restriction/base change of proper
  and flat morphisms; no match.
- `msearch.py ... grep '(stable.*[Ll]ocus|[Ss]table.*[Cc]urve|smooth.*[Ll]ocus)'
  AlgebraicGeometry`: ten hits, principally `Scheme.Hom.smoothLocus`, a source-scheme
  smooth locus rather than the whole-family open over the base.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for stable/open, smooth-family,
  this node id, the new predicate names, and theorem name: no existing exact statement.
  Found and reused `ProperCurveModuli`, `OpenModuliSubstack`, stable pointed families,
  and the nodal-family predicate. Existing downstream docstrings cite this unstated node;
  the nodal stack theorem is not the stable-genus or smooth-family locus theorem.
- Read the recorded signatures/docstrings and all six original statement-dependency
  statements; the Mathlib leaves `Field`, `Scheme`, and `Smooth` are used directly.

Validation: the server compile succeeded for both the sandbox and library module names,
with no errors or non-sorry warnings. A first large inline realization clause caused
an elaboration heartbeat timeout; naming the same projection-preserving predicate and
making the `Over.homMk` types explicit eliminated it without changing the assertion or
increasing any limit. Final delivery preflight and per-file compile are run via deliver2.py.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
