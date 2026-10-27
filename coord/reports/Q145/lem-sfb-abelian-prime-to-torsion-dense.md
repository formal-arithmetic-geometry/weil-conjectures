## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.PrimeToTorsionDense` states
`AlgebraicGeometry.IsAbelianVariety.eq_univ_of_contains_primeToTorsion` with a single
`sorry`. There are no new definitions, dependency repairs, or statement changes.
Only the item's `lean` field changes.

Clause-by-clause correspondence:

- An algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The abelian variety B/F is `(B : Over (Spec (.of F))) [GrpObj B]
  [IsAbelianVariety B]`: the group scheme structure is explicit; the recorded
  abelian-variety predicate supplies properness, smoothness, and connectedness.
- Every integer n at least 1 is `∀ (n : ℕ), 0 < n → ...`. Positive integers
  and positive naturals are canonically the same indexing set.
- Its image in F is nonzero is `(n : F) ≠ 0`. In a field this is exactly
  invertibility. No characteristic has been fixed or excluded.
- B[n], the kernel of multiplication by n, is the recorded
  `torsionSubgroupScheme B n`. Its inclusion is `torsionSubgroupScheme.ι B n`.
- The F-rational points B[n](F) are
  `(torsionSubgroupScheme B n).hom.fieldPoints F`. These are sections of its
  structure morphism over Spec F, using the self algebra structure on F.
- The image in B of each such rational point q is
  `(torsionSubgroupScheme.ι B n).left (q.1.base default)`.
  Spec F has exactly one point; evaluation at `default` is its full topological image.
- A closed subset of the underlying topological space is `(Z : Set B.left)
  (hZ : IsClosed Z)`. Containment of the entire union T is the universal
  membership hypothesis `hT`, quantifying all permitted n and every q.
- Being the whole underlying space is `Z = Set.univ`. This is precisely the
  node's explicit closed-subset formulation of Zariski density; no additional
  closed-point or schematic-density condition is substituted.
- The zero-dimensional case is included because there is no positive-dimension
  hypothesis or binder. An empty abelian variety cannot arise, since the group
  unit supplies a point (and the existing predicate supplies connectedness).

Statement dependencies read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; the dependency record explicitly
  identifies this algebraically-closed-field clause, as well as AlgebraicClosure
  and IsAlgClosure for the other notions that dependency also describes.
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`.
- `def-sc-mult-n`: `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
  `AlgebraicGeometry.torsionSubgroupScheme` and its canonical `.ι`.
- `def-pc-rational-point`: `WeilConjectures.AlgebraicGeometry.DensePoints`,
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`; its full signature and
  docstring explicitly use `Scheme.Hom.fieldPoints` as the rational-point
  sections. The statement uses that underlying point notion; no field extension
  or base-change conclusion is requested here, so the base-change function itself
  does not occur in the signature. Its recorded module is publicly imported.

Proof-dependency imports follow the existing DAG: GroupoidScheme,
Mathlib.Topology.KrullDimension, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
Mathlib.AlgebraicGeometry.Limits,
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic (both characterization and
commutativity), WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion,
GroupNeutralComponentTranslates, PerfectFieldGroupoidImageClosure, and
ConstantGroupSchemeMultiplication. The one proof dependency
`lem-sfb-abelian-closed-subgroup-reduced-component` has no Lean record or
Mathlib match in the read checkout; therefore there is no module to import for
it yet. It is only a proof dependency, not a missing notion in this statement.
The theorem docstring retains it in the complete six-step proof plan.

Edge cases checked before writing: n = 0 is excluded explicitly, avoiding the
whole variety as its own 0-torsion; n = 1 contributes the identity point and is
allowed in every characteristic; in characteristic zero every positive n is
allowed; in characteristic p exactly the positive integers not divisible by p
are allowed, including characteristics 2 and 3. The trivial abelian variety
Spec F has its unique point in B[1](F), so the conclusion is valid in dimension
zero. No dimension, prime, polarization, separability, or nontriviality
hypothesis has been added. An arbitrary universe u covers field and scheme
sizes using the project's standard Over encoding.

Sources: read the node's entire statement and six proof steps, every statement
dependency's statement and recorded interface, and their source signatures and
docstrings. Also opened Milne's January 2, 2022 article at
https://www.jmilne.org/math/xnotes/AVs.pdf, Section 12, printed p.19, first
unnumbered lemma after Proposition 12.1. It states density of the union of
prime-to-characteristic kernels; over the algebraically closed field these
finite etale kernels' points give exactly the node's union. No source-based
correction is needed.

Searches made with the prescribed msearch.py wrapper (raw results are retained
in sandbox searches.jsonl):

- leanfinder: "The prime to characteristic torsion points are Zariski dense in
  an abelian variety over an algebraically closed field". Eight hits, including
  `AlgebraicGeometry.dominant_eq_topologically`, `Scheme.Hom.denseRange`,
  `IsDominant.denseRange`, rational/partial-map dense-domain results, an
  Ax-Grothendieck theorem, and AddCircle density; none concerns abelian torsion.
- loogle: `"AlgebraicGeometry", "torsion"`: zero hits.
- leansearch: "Prime to characteristic torsion points of an abelian variety
  are Zariski dense". Eight hits: characteristic lemmas, rational-map domains,
  IsAlgClosed.perfectRing, an affine-site density instance,
  AddSubgroup.torsionBy, and the closed-set/zero-locus characterization; no match.
- grep via msearch.py: `torsion.*[Dd]ens|[Dd]ens.*[Tt]orsion|AbelianVariety`:
  three unrelated convex-segment hits in Mathlib.
- rg on both `lean/WeilConjectures` and `lean/Sheaf`:
  `torsion.*[Dd]ens|[Dd]ens.*[Tt]orsion|lem-sfb-abelian-prime-to-torsion-dense`.
  Only unrelated torsion/cohomology density material and the existing consumer
  SubvarietySeparableDefinition's proof docstring; no density declaration.
- Checked proposed theorem name `prime_to_torsion_dense` / actual new name
  against the project and upstream declaration-name inventory; no duplicate.

Validation: the delivered file passed scompile.py Q145
lem-sfb-abelian-prime-to-torsion-dense, both sandbox and library module passes
(17.5 s and 7.8 s), with no errors or unexpected warnings. `autoImplicit false`
is explicit; all variables and the universe are bound. Every theorem proof is
`sorry`. No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q145

A separate in-thread rereading of the original node and final signature was
performed; no other agent was started, as the dispatcher explicitly prohibits
it. The maintainer's independent review remains the independent reading.

Checked that the two predicates Field and IsAlgClosed render the base exactly;
Over plus GrpObj plus IsAbelianVariety render the abelian variety exactly;
positive naturals with nonzero cast render exactly the allowed integers; the
recorded kernel and its canonical inclusion render B[n] and its map to B;
fieldPoints imposes the section condition, so q is not an arbitrary morphism
or an arbitrary point of the kernel's underlying space. The composite point
image is in B.left, and `hT` requires every permitted point to belong to Z.
`hZ` makes Z closed and equality to Set.univ is the entire conclusion.
There is no positive dimension restriction, extra group assumption, or
missing characteristic-zero case. No mismatch was found and no statement
change was made. The proof docstring follows all six node steps, including
the finite-component bound and its dimension-zero ending.
