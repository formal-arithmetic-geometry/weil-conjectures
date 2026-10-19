## Worker report

The module `Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents` states
`AlgebraicGeometry.normal_topologicallyNoetherian_components`. Its sole theorem proof is
`sorry`; its docstring supplies all eight proof steps of the node and their dependencies.
There are no definitions, new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- A scheme Z: `(Z : Scheme.{u})`, with the universe explicitly bound.
- The underlying space is Noetherian: `[TopologicalSpace.NoetherianSpace Z]`. Mathlib defines
  this as the ascending-chain condition on opens, equivalently the descending-chain
  condition on closed subsets. It is not the ring-theoretic `IsNoetherian` scheme class.
- Every local ring is a normal domain: `hnormal : ∀ z : Z,
  IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)`.
  This is exactly the normal-domain inline form recorded by def-weil-pbc-normal-ring.
- There are finitely many irreducible components: `(irreducibleComponents Z).Finite`.
- Distinct components are disjoint: `(irreducibleComponents Z).Pairwise Disjoint`.
- Each component is open and closed: for `C ∈ irreducibleComponents Z`,
  `∃ hC : IsOpen C, IsClosed C ∧ ...`.
- Its open subscheme is integral: `IsIntegral (Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens))`.
  This is the actual restriction of Z to C, rather than an arbitrarily chosen scheme
  or the closed subscheme from an unspecified ideal.
- Its open subscheme is normal: for each `z : (Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens))`, the final
  conjunction states `IsDomain` and `IsIntegrallyClosed` for its actual stalk.
- The empty scheme is allowed: no nonemptiness hypothesis is imposed on Z. Irreducible
  components are nonempty by their definition, so an empty space has none; finiteness,
  pairwise disjointness and the component conclusions all apply vacuously.
- No local ring Noetherian hypothesis occurs. Normality means integrally closed domains,
  rather than merely reduced stalks or integrally closed rings without the domain clause.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` in `Mathlib.AlgebraicGeometry.Scheme`.
  Its recorded structure extends a locally ringed space with affine neighbourhoods;
  its `Scheme.Opens` and open subscheme `toScheme` give the canonical restriction.
- def-weil-pbc-normal-ring: `IsDomain` and `IsIntegrallyClosed` in the recorded inline form;
  public import `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
  The latter is `IsIntegrallyClosedIn R (FractionRing R)`. The normal-domain clause is
  used directly on stalks; the universal prime-localization ring clause is not substituted.
- def-weil-irreducible-components: `irreducibleComponents` in `Mathlib.Topology.Irreducible`,
  the recorded `mathlib_match`. It is the set of maximal nonempty irreducible subsets.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`. It includes nonemptiness and domain section rings
  on nonempty opens, equivalently the node's reduced irreducible criterion.

The proof-only imports include the recorded algebraic Tag 030C theorem
`reduced_normal_iff_integrallyClosed_totalFractions` from
`Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions` and the Mathlib modules
for affine open charts/stalks, open immersions and irreducible closed-subspace transport.
Other proof dependencies are supplied by the public Mathlib modules already imported.

Source checked: `literature/stacks-project/properties.tex`, Tag 0357,
`lemma-normal-locally-finite-nr-irreducibles`, including its affine reduction to Tag 030C
and its globalization by intersections with affine opens. Its hypothesis is finite
components on quasi-compact opens; topological Noetherianness implies this by Tag 0052.
The node is precisely the resulting topologically Noetherian specialization.

Edge cases checked before drafting: the empty scheme (zero components); the spectrum of
an integrally closed domain (one integral component); a finite product of normal domains
(disjoint coordinate-idempotent opens); a rank-one non-discrete valuation domain (its
spectrum is Noetherian although its ring need not be); and xy=0 (meeting components, but
the local ring at their intersection is not a domain, so excluded by normality).

Searches performed with `msearch.py NH lem-trf-normal-topologically-noetherian-components`:

- LeanFinder, query: "A normal scheme with Noetherian underlying topological space has
  finitely many disjoint clopen irreducible components which are normal integral open
  subschemes". Eight results: topological/scheme finiteness, integral irreducibility,
  Noetherian classes and normalization open covers. None states the complete conclusion.
- Loogle, query: `irreducibleComponents, IsClopen, NoetherianSpace`. No hits, unknown
  identifier `NoetherianSpace`; its actual name is namespace-qualified.
- Mathlib grep, query: `normal.*[Cc]omponent|[Cc]omponent.*normal|NormalScheme`, subdirectory
  `AlgebraicGeometry`. No hits.
- LeanSearch, query: "normal scheme irreducible components open disjoint topologically
  Noetherian". Eight hits, giving components, finite components in Noetherian spaces,
  irreducible finite decompositions and integral irreducibility; no complete match.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` trees for normal/component
  terminology and the chosen theorem name; `rg` in upstream for this blueprint id.
  No exact statement/name/id match upstream. Read the side modules
  `NormalEtaleComponentsClopen` and `NormalSectionsFiniteProduct`: both impose
  `IsLocallyNoetherian` and cannot replace the present theorem. The former additionally
  concerns an etale map and the latter section-ring decompositions.
- Read the actual Mathlib signatures/docstrings for Scheme, IsIntegral,
  IsIntegrallyClosed, irreducibleComponents and NoetherianSpace, plus the recorded
  proof-dependency modules. No private replacement definitions were introduced.

The previous worker's stale-assignment conclusion confused the Q53 stage-1 split with a
stage-2 statement landing. The Q53 report is explicitly headed "Stage-1 report", and the
current node had no `lean` or `reviewed_lean` record. This delivery supplies the missing
stage-2 statement while preserving every other node field.

## Second reading by NH

This dispatcher starts a single worker and explicitly forbids starting another agent;
the maintainer's independent review is external to this delivery. This section records
my own second reading, not an independent worker review. I reopened the node, Stacks
0357, the four dependency records and the final signature. Each hypothesis and clause
is matched above. In particular the open component is formed by `⟨C, hC⟩` itself, its
normality uses its own stalks, the global finiteness uses only the underlying topology,
and the empty scheme is not excluded. I found no mismatch requiring a correction.

The compiler initially rejected dot notation on the constructed open; explicitly naming
`Scheme.Opens.toScheme` fixed namespace lookup without changing the mathematical statement.
