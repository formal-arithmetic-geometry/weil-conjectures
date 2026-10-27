## Worker report

This delivery states `AlgebraicGeometry.semisimple_cyclic_closure_linearlyReductive`
in `Sheaf.AlgebraicGeometry.SemisimpleCyclicClosureLinearlyReductive`. Its proof is
`sorry`. It also supplies the missing arbitrary-characteristic definition of linear
reductivity; both definitions in that module have explicit data and no postponed proofs.
The source read was Milne, Algebraic Groups (iAG2017), Corollary 13.8, printed p.257,
its first proof paragraph, Section 9.19, printed p.171, and Definition 12.52, printed
p.248. The node statement and its accepted six-step split are preserved.

Hypothesis and clause correspondence:

- The field and algebraic closure hypotheses are `{k : Type u} [Field k]
  [IsAlgClosed k]`.
- The group scheme H is `H : Over (Spec (.of k))` with `[GrpObj H]`. Affineness
  is `[IsAffine H.left]`. Finite type is `[LocallyOfFiniteType H.hom]
  [QuasiCompact H.hom]`, as required by the recorded finite-type dependency.
- The rational point is `s : StandardGroupSchemes.affine k k ⟶ H`. Its source is
  exactly Spec k with its canonical k-structure. `hs : IsSemisimpleGroupSchemePoint H s`
  is the existing definition testing every finite-dimensional rational representation
  for diagonalizability. It includes the empty index set.
- The cyclic subgroup is the integer powers `s ^ n`, with the existing group structure
  on morphisms into a group object. Evaluating at `IsLocalRing.closedPoint k` gives
  their underlying topological points. Both positive and negative powers occur.
- `G : Over (Spec (.of k))`, `j : G ⟶ H`, `[IsClosedImmersion j.left]`,
  `[IsReduced G.left]`, and `hG : Set.range j.left = closure (...)` say exactly
  that G is the reduced induced closed subscheme supported on that closure. This is
  the customary arbitrary-model formulation of “let G be the reduced closed
  subscheme”: a reduced closed immersion is uniquely determined up to unique
  isomorphism over H by its support. No group structure on G is assumed.
- `∃ (_ : GrpObj G), IsClosedSubgroupScheme j` asserts the restricted group
  operations. The existing class includes `IsMonHom j`, so the unit and multiplication
  commute with the inclusion; inverses then commute as well. Its injectivity on all
  algebra-valued points and closed immersion are the recorded subgroup notion.
- `Smooth G.hom` is precisely smoothness over k, and
  `IsLinearlyReductiveGroupScheme G` is the definition in the new node below.
- The final existential gives a lift `t` of s with `t ≫ j = s` and
  `DenseRange (fun n : ℤ ↦ (t ^ n).left (IsLocalRing.closedPoint k))`.
  Since j is a homomorphism, this lifts every integer power, so it says both
  containment of Γ in G(k) and density in the entire underlying space of G.
- There is no connectedness or characteristic hypothesis. There is no extra
  smoothness or reducedness hypothesis on H.

Dependency declarations used:

- `Field` in Mathlib.Algebra.Field.Defs and `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic (the algebraic-closure node records this
  component notion). Their definitions and the field/scheme/geometry dependency
  signatures were read in the source, not inferred from declaration names.
- `CategoryTheory.GrpObj`, its group on points and `IsMonHom` in
  Mathlib.CategoryTheory.Monoidal.Grp / Monoidal.Cartesian.Grp, with the group-scheme
  convention and `IsClosedSubgroupScheme` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The latter class's full signature
  and docstring were read; it is used directly, not replaced by a private predicate.
- `AlgebraicGeometry.Scheme`, `IsAffine`, `IsReduced`, `IsClosedImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `Smooth`, in the recorded Mathlib modules
  Scheme, AffineScheme, Properties, Morphisms.ClosedImmersion, Morphisms.FiniteType,
  Morphisms.QuasiCompact, and Morphisms.Smooth respectively.
- `AlgebraicGeometry.IsSemisimpleGroupSchemePoint` in
  Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint, whose complete definition was
  read. The existing definition node is added to the item's statement dependencies.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom` and `RationalHom.points`, from
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie. Its signature
  requires `IsMonHom` and its action is evaluated on every algebra's points.
  `AlgebraicGeometry.points` in GroupScheme.Lie.Ring uses the canonical affine source.
- `Matrix.toLin'`, `Submodule.span`, `iSupIndep` and the submodule supremum are the
  Mathlib notions used to render action, scalar extension and internal direct sums.

Proof-plan imports are GroupoidScheme, PerfectFieldGroupoidImageClosure,
GeometricReducedFiniteTypePerfectField, Mathlib.AlgebraicGeometry.Group.Smooth,
WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, and
WeilConjectures.Mathlib.RingTheory.Nullstellensatz. The image-closure theorem,
geometric-reducedness theorem, `smooth_of_grpObj`, kernel construction, and
Nullstellensatz declarations were read. The recorded normal-subgroup representation
kernel and rational-representation semisimple-point proof prerequisites have no Lean
record yet, so there is no module to import for those two. They are only proof
prerequisites, not missing objects needed to state this theorem.

Edge cases checked: s = 1 gives the trivial reduced group. Finite order prime to
positive characteristic may give a disconnected reduced group and is included. Tori
and infinite-order semisimple points are included. No characteristic-zero assumption
has slipped in; a nontrivial unipotent point in a faithful representation fails hs.
The empty index type gives the zero representation and its empty direct sum. Nonzero
summands are required (`U ≠ ⊥`), preventing the zero representation from being simple.
Invariance tests arbitrary algebras, including nonreduced ones, so field-valued points
are never substituted for scheme-theoretic invariance. The scalar-extension subspace
is explicitly the A-span of the coordinatewise image of U; this is U tensor A under
the canonical finite-basis identification. Quantifying over algebras in `Type u`
is the standard group-scheme universe convention: all the universal finite-matrix
coefficient tests live there, so the condition extends to larger algebras by naturality.
Every finite-dimensional vector space, regardless of its original carrier universe,
is isomorphic to k^ι for a finite index type in `Type u`.

Searches performed:

- msearch leanfinder: “The reduced Zariski closure of the cyclic subgroup generated
  by a semisimple point of an affine algebraic group is smooth and linearly reductive”.
  Eight hits: reduced/semisimple rings, IsReduced, semisimple endomorphisms and
  semisimple Lie algebras; no group-scheme cyclic-closure statement.
- msearch loogle: `"IsSemisimple", "closure"`: 0 hits.
- msearch grep: `LinearlyReductive|RationalRepresentation|SemisimplePoint|cyclicClosure`:
  0 Mathlib hits.
- rg of WeilConjectures for the item id: no declaration; rg of both project Lean
  roots for semisimple points, rational representations and linear reductivity found
  the semisimple point and RationalHom interfaces cited above. RationalHom.IsSimple
  and IsSemisimple require CharZero, so they cannot render this arbitrary-characteristic
  notion. They are not duplicated or silently applied with stronger assumptions.
- The separate searches for the new definition are recorded below and in its node.

No statement correction or STATEMENT-DISPUTED issue was found. Initial compiler
errors were repaired by using the actual Mathlib.Order.SupIndep module and opening
Mathlib's existing MonObj scope for integer powers; no local notation is introduced.
Both delivered files compiled cleanly via scompile.py in dependency order, with the
expected sorry proof on the main theorem and no other warnings.

## New nodes

`def-sfb-linearly-reductive-group-scheme` defines scheme-theoretic invariant subspaces
and linear reductivity, following Milne Definition 12.52 (p.248) and the first paragraph
of Corollary 13.8 (p.257). Its module is
Sheaf.AlgebraicGeometry.LinearlyReductiveGroupScheme. A simple summand is a nonzero
invariant subspace whose invariant subspaces are zero or itself. An independent family
whose supremum is top is its internal direct sum. The predicate quantifies over all
finite-dimensional rational representations using the existing RationalHom interface.

Before creating it I searched the DAG definition nodes: only adequate-moduli-space
mentions linear reductivity and does not define it. `tools/blueprint_refs.py search
'linearly reductive'` returned 0 blueprint nodes. The ancestor query returns null;
the inherited null ancestor and the item's full via trace are preserved. Searches for
'invariant subspace' returned generic Lie/stability blueprint material, with no such
arbitrary-characteristic group-scheme definition. Mathlib msearch leansearch query
“An affine group scheme is linearly reductive if every finite dimensional rational
representation is a direct sum of simple representations” returned eight affine-scheme
and reducedness results. Leanfinder query “An affine group scheme is linearly reductive
when every finite dimensional rational representation decomposes into simple invariant
subspaces over all algebras” returned eight abstract finite-group representation and
IsAffine results. msearch grep `LinearlyReductive|linearly.reductive|IsInvariantSubspace`
returned 0 hits. rg of WeilConjectures and Sheaf found no definition of linear
reductivity; the existing rational simple and semisimple predicates assume characteristic
zero and test k-points, so they cannot be used here. No new independent notion of
rational representation is introduced.

## Second reading by Q140

No second worker was started, as instructed by the dispatcher. The maintainer's
independent review reads this delivery. A final self-check matched every hypothesis
and clause above to the node and Lean; both definitions have real data, the theorem
assumes no group structure on G, and the invariance test includes all algebra extensions.

The first dry run required the new node’s standard `import_flags` field; added the
empty list, as the node is reached by this item and has no import flags.
