## Worker report

Existing declarations, no new module: `topologicalKrullDim` in
`Mathlib.Topology.KrullDimension` and `topologicalKrullDimAt` in
`WeilConjectures.Mathlib.Topology.KrullDimension` (source line 333).
The main record names the latter; its `declarations` list records both notions.
Read both full definitions and docstrings, including the section variables
`{X : Type*} [TopologicalSpace X]` for `topologicalKrullDimAt`.

Clause-by-clause correspondence:

- A scheme is `X : AlgebraicGeometry.Scheme.{u}`; its coercion to a type is its
  underlying topological space, with its existing topology. Both declarations
  specialize to this type, without further assumptions on the scheme or universe.
- The Krull dimension of X is `topologicalKrullDim X : WithBot ℕ∞`.
  Its body is `Order.krullDim (TopologicalSpace.IrreducibleCloseds X)`.
  The latter consists of closed irreducible sets ordered by inclusion;
  `IsIrreducible` requires nonemptiness. `Order.krullDim` takes the supremum
  of `p.length` over strict chains `p : LTSeries`, where length is the last
  index r of a chain Z₀ < ... < Zᵣ. This renders every part of the first sentence.
- A point is `x : X`; the dimension at x is `topologicalKrullDimAt x`.
  The body `⨅ (U : TopologicalSpace.Opens X) (_ : x ∈ U), topologicalKrullDim U`
  ranges over all and only open neighbourhoods of x. The subtype U carries
  the subspace topology. The whole space supplies a neighbourhood, and
  `WithBot ℕ∞` is well ordered, so this infimum is attained and equals the
  stated minimum. Every such U is nonempty, so its dimension is at least zero.
- The final paragraph explicitly announces finite-type finiteness and the
  dimension formula as properties recorded elsewhere. It supplies no extra
  defining data or hypothesis: these two definitions apply to every scheme.
  No finiteness or dimension-formula theorem is added or assumed here.

Dependency declarations read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (underlying carrier and topology).
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, precisely the global dimension used here.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt`,
  `WeilConjectures.Mathlib.Topology.KrullDimension`, precisely the local dimension.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`, in Mathlib's morphism modules
  `FiniteType` and `QuasiCompact`. These enter only the announced property.
- `def-kun-support`: read `Sheaf.AlgebraicGeometry.EtaleSupport`, including
  `Scheme.Hom.pointsOfTrdegLE`, `Scheme.etaleSheafSupport` and
  `Scheme.etaleComplexSupport`. Its transcendence-degree notation is used
  only by the announcement of `lem-kun-dimension-formula`.

Edge cases: the empty scheme has no irreducible closed subsets, so its dimension
is ⊥ (negative infinity); it has no point to which local dimension applies.
A one-point nonempty space has a length-zero chain and dimension zero.
All neighbourhoods of an actual point are nonempty. Unbounded lengths and
neighbourhoods all of infinite dimension give ⊤, which the codomain permits.
No finite-type, nonemptiness, irreducibility, field or characteristic restriction
is imposed on either definition.

Searches made:

- msearch leanfinder: "Krull dimension of a scheme and dimension at a point as
  minimum over open neighbourhoods": eight hits, including `topologicalKrullDim`;
  no local dimension in Mathlib.
- msearch loogle: "topologicalKrullDim": seven hits; confirms the global definition.
- msearch grep: "topologicalKrullDim|dimAt|localDimension" in AlgebraicGeometry:
  five Mathlib uses of `topologicalKrullDim` in Artinian.lean, no local definition.
- msearch leansearch: "dimension of scheme at point minimum Krull dimensions
  open neighborhoods": service unavailable (Internal Server Error), recorded.
- rg of the source project for `dimAt`, `topologicalKrullDimAt`, dimension defs,
  and the node id: finds the exact local definition at line 333 and its uses
  in Smooth.lean; no declaration tagged with this node id.
- rg of `dag/lean_names_upstream.json` and the source for the node id: no match.
- rg of `lean/Sheaf` for dimension: finds `Scheme.dim` and its comparison theorem
  in `Sheaf.AlgebraicGeometry.Dimension`. That definition uses local rings;
  we use the already existing topological definitions directly, without relying
  on the comparison theorem, whose proof remains sorry.

Source validation: the blueprint markdown named in the node is not present on
this machine. Read the full node and its stage-1 source review, and opened
[Stacks 0055](https://stacks.math.columbia.edu/tag/0055) and
[Stacks 04MT](https://stacks.math.columbia.edu/tag/04MT).
They specify exactly these topological definitions for a scheme and its points.
No statement correction, new node, unusable dependency or disputed statement.
No Lean file is written or compiled for this existing-declaration delivery.

## Second reading by E1

Independent reader: I opened the sandbox node, both existing definition bodies,
all five dependency records, and the dependency declarations themselves. No
statement correction, new definition node, dependency module or Lean repair is
needed. The recorded signature is verbatim the source declaration before `:=`;
its implicit parameters are bound by the immediately preceding section variables.

Source checked independently: the blueprint markdown is absent on this machine.
I read the Stacks TeX directly from the official stacks/stacks-project repository:
`topology.tex`, section `section-krull-dimension`, definition `definition-Krull`
([0055](https://stacks.math.columbia.edu/tag/0055)), and `properties.tex`, section
`section-dimension`, definition `definition-dimension`
([04MT](https://stacks.math.columbia.edu/tag/04MT)). The sections introduce only a
topological space and a scheme respectively; they impose no standing Noetherian,
finite-type, separatedness or field hypothesis. The node's stage-1 review also
identifies these exact sources. The source definition agrees with the node.

My object/hypothesis/clause inventory and comparison:

1. **Arbitrary scheme X and its underlying space.**
   `AlgebraicGeometry.Scheme.{u}` extends `LocallyRingedSpace`; its `CoeSort`
   instance returns `X.carrier`, with the carrier's topology. Thus
   `topologicalKrullDim X` and `topologicalKrullDimAt (x : X)` refer to precisely
   the underlying space of the scheme, as 04MT requires. Verdict: exact, with
   no added hypothesis and arbitrary universe u.
2. **Nonempty irreducible closed subsets, ordered by strict inclusion.**
   `topologicalKrullDim` is `Order.krullDim (IrreducibleCloseds X)`.
   I read `Topology/Sets/Closeds.lean`: this structure has a carrier, an
   `IsIrreducible` proof and an `IsClosed` proof; its partial order is the
   set-inclusion order. `IsIrreducible` in `Topology/Irreducible.lean` is
   `s.Nonempty ∧ IsPreirreducible s`. Verdict: exact; empty closed sets cannot
   enter a chain, and strict order means proper inclusion.
3. **Supremum of chain lengths r, with r+1 members.**
   `Order.krullDim` in `Order/KrullDimension.lean` is
   `⨆ (p : LTSeries α), p.length`; its docstring explicitly specifies the
   rightmost index of `a₀ < ... < aₙ`. Thus the length is r, not r+1.
   The result `WithBot ℕ∞` admits negative infinity and positive infinity.
   Verdict: exact first definition, including the dimension-zero case.
4. **Point x and every open neighbourhood U, carrying the subspace topology.**
   The local definition has section parameters `{X : Type*} [TopologicalSpace X]`
   and explicit `(x : X)`. Its body is
   `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`.
   `Opens X` ranges over all open subsets, and its carrier subtype has the
   inherited topology. The membership binder restricts the range to precisely
   the neighbourhoods in the node. Verdict: exact objects and quantifier order.
5. **Minimum, rather than just an unattained infimum.**
   The neighbourhood family is nonempty because it contains the whole space.
   Its dimension values form a nonempty subset of the well-ordered extended
   naturals `WithBot ℕ∞`, hence have a least member. Their infimum is that member.
   Every neighbourhood contains x and has dimension at least zero. Verdict:
   the infimum definition gives exactly the source minimum without an extra
   finiteness or existence hypothesis.
6. **Final finite-type paragraph.** This expressly records finiteness elsewhere
   and announces the dimension formula; it is commentary, not additional
   defining data. I read `LocallyOfFiniteType`, `QuasiCompact` and the dependency
   `Scheme.Hom.pointsOfTrdegLE` in `EtaleSupport.lean`, whose residue-field
   algebra is induced by the structure map. They are not assumptions on either
   dimension definition. Verdict: no omitted defining clause. In particular
   dimension at a point is not replaced by dimension of its local ring.

The global and local notions are the recorded declarations of
`def-kun-topological-krull-dimension` and
`def-kun-topological-dimension-at-point`, not private copies. `Scheme.dim` in
`Sheaf.AlgebraicGeometry.Dimension` is expressed using local rings and has a
separate comparison theorem; the worker correctly uses the existing topological
notion directly. No hollow definition or new proof occurs in this delivery.
Existing source docstrings describe exactly the two notions; the blueprint
annotation requirement for newly written modules has no module to apply to here.

Edge cases independently checked: the empty scheme (including Spec of the zero
ring) has no irreducible closed set and hence dimension bottom; it has no local
point. A singleton has a length-zero chain and dimension zero. The neighbourhood
index set at an actual point cannot be empty, although individual non-neighbourhood
opens contribute only top through the empty membership binder. Unbounded chains
and a point all of whose neighbourhoods have infinite dimension are admitted.
No characteristic is selected and no field is required. Both declarations are
universe-polymorphic; using a scheme carrier introduces no universe equality or
smallness restriction beyond that scheme's own universe.

Independent searches, using additional wording:

- msearch leanfinder `infimum dimensions neighbourhoods local dimension
  topological space`: eight Hausdorff-dimension hits, none the Krull notion.
- msearch loogle `"topologicalKrullDim"`: seven hits, including the exact global
  definition in `Mathlib.Topology.KrullDimension`.
- msearch grep `local dimension|dimension at|IrreducibleCloseds` under Topology:
  finds the global definition and its irreducible-closed-set structure.
- msearch leansearch `length chains irreducible closed subsets dimension open
  neighborhood point`: unavailable (Internal Server Error); no verdict inferred.
- Direct rg of `WeilConjectures` and `lean/Sheaf` for dimension definitions and
  `local dimension|dimension at`: confirms `topologicalKrullDimAt` in the source
  topology module and the distinct local-ring presentation `Scheme.dim` in
  the project's Dimension module. I opened both, not merely their names.

Mismatches found: none. Changes: appended this independent reading; preserved
all correct node fields and the existing declaration record. No Lean file is
created, so there is no new module to compile; the delivery preflight validates
this existing-declaration delivery.
