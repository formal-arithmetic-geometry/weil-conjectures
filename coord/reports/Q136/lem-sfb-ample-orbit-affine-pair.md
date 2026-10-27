## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleOrbitAffinePair` states
`AlgebraicGeometry.Scheme.Modules.exists_ample_orbit_affine_pair`, with its proof
postponed by `sorry`. It introduces no definitions or additional nodes. The item's
statement, statement dependencies and proof are unchanged. The statement follows the
recorded agent construction from Stacks Properties, Tag 09NV, whose full statement and
proof were read in `literature/stacks-project/properties.tex`, beginning at line 5293.

Hypotheses and conclusions, matched individually:

- The scheme is `Y : Scheme.{u}`; nonemptiness is `[Nonempty Y]`.
- Noetherian means exactly `[IsLocallyNoetherian Y] [CompactSpace Y]`, as specified by
  the node. The second condition is quasi-compactness without Hausdorffness.
- Topological dimension at most one is `hdim : topologicalKrullDim Y ≤ 1`, with
  Mathlib's dimension in `WithBot ℕ∞`.
- The invertible module is `L : Y.Modules` with `[L.IsInvertible]`; ampleness is the
  recorded `hL : IsAmple Y L`. There is no additional module or action structure.
- A finite group is `{G : Type v} [Group G] [Finite G]`; its scheme-automorphism action
  is `ρ : G →* Aut Y`. The group universe is independent of the scheme universe.
  No field, separatedness, faithfulness or equivariant structure on L is assumed.
- The generic set E is the existing Mathlib `genericPoints Y`, literally the points
  whose singleton closures are irreducible components. Its finiteness and nonemptiness
  are the first two conjuncts `(genericPoints Y).Finite` and `.Nonempty`.
- The integers p and q are natural numbers, each with an explicit `0 <` conjunct.
  The node's u and v sections are named `s` and `t` in Lean: they are elements of
  `(L.tensorPow p).val.presheaf.obj (Opposite.op ⊤)` and the corresponding q power.
- The witnesses `U V : Y.Opens` are exactly the two section loci, by their set
  equalities to `nonvanishingLocus (L.tensorPow p) s` and its q analogue. This uses
  the recorded maximal-ideal-times-stalk formulation of nonzero residue-field value,
  not nonzero germ. The equalities also identify their open subschemes uniquely.
- Affineness is `IsAffineOpen U ∧ IsAffineOpen V`; containing all the generic points
  is `genericPoints Y ⊆ (U : Set Y) ∩ (V : Set Y)`.
- Z is written directly as `(U : Set Y)ᶜ`. Its finiteness is the `.Finite` conjunct;
  its points being closed in Y is `∀ z : Y, z ∈ (U : Set Y)ᶜ → IsClosed ({z} : Set Y)`.
  Closedness of Z itself is inherent in U being an open.
- The existential set T is fixed by the equality
  `T = ⋃ g : G, (ρ g).hom ⁻¹' (U : Set Y)ᶜ`. The preimage is under the action map of g,
  exactly g^{-1}Z in the node's notation. `T.Finite` is explicit.
- Every inverse translate preserves T by `∀ h : G, (ρ h).hom ⁻¹' T = T`, and the final
  conjunct `T ⊆ (V : Set Y)` places the whole orbit boundary inside the second open.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, and its scheme
  morphisms and open subschemes (available through the statement imports).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  the definition of `IsNoetherian` was also read to check its equivalence with the
  two explicit binders and the topological Noetherian-space proof input.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (publicly available through the
  Noetherian import).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `tensorPow`, imported publicly
  through `WeilConjectures.AlgebraicGeometry.Ample`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`; both full
  definitions and docstrings were read.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`.
  This is the residue field in the recorded definition's fibre interpretation; the
  statement itself uses that dependency's equivalent stalk-ideal formulation.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, exposed through
  `Mathlib.Topology.Sober`, whose `genericPoints` is used directly, avoiding a new
  definition of E. Their exact definitions were read.
- `Mathlib.CategoryTheory.Endomorphism`: `CategoryTheory.Aut` for the scheme action.
- Proof-only import `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`:
  `AlgebraicGeometry.Scheme.Modules.exists_affine_section_neighbourhood_of_finite`;
  its complete signature and proof docstring were read.
- Proof-only import `WeilConjectures.Mathlib.Topology.KrullDimension`:
  `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`, whose
  signature was read. The remaining proof dependencies are supplied by the
  Noetherian and sober-space imports, including finite irreducible components and
  scheme sobriety. The theorem docstring reproduces all five proof steps and names
  their DAG dependencies.

Edge cases checked before writing:

- An empty scheme is excluded by the node's own nonempty hypothesis, necessary for
  the nonempty E conclusion; dimension zero and isolated components are included.
- If U is all of Y, its boundary and T are empty. Neither is forced nonempty.
- Disconnected and nonreduced schemes are allowed. The argument uses only the
  underlying Noetherian space for its component and boundary assertions.
- Trivial groups and nonfaithful actions are allowed; group actions impose no
  linearization of L and no orbit-size hypothesis.
- No common exponent is imposed: p and q are independent, as required in particular
  over finite fields. The proof uses Tag 09NV twice rather than infinite-field
  hyperplane avoidance.
- The closed complement misses every component's generic point. A length-two strict
  chain would violate the explicit dimension bound, so the cited zero-dimensional
  closed-subset theorem applies without separatedness.

Searches (all on 2026-10-24):

1. `msearch.py leanfinder`, query: "An ample invertible module on a Noetherian scheme
   of dimension at most one has two affine section opens with the second containing
   the finite group orbit of the complement of the first". Eight hits, including
   `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen`, Proj affine covers and
   basic-open lemmas. None states the two-section orbit-boundary result.
2. `msearch.py loogle`, query:
   `AlgebraicGeometry.IsAffineOpen, AlgebraicGeometry.Scheme`. Twelve hits on affine
   opens, their covers, isomorphisms and preimages; none supplies this result.
3. `msearch.py grep`, query `ample.*orbit|orbit.*affine|IsAmple` in Mathlib's
   `AlgebraicGeometry`: zero hits.
4. `msearch.py leansearch`, query: "An ample line bundle on a Noetherian curve admits
   two affine section opens with the second containing all finite-group translates
   of the complement of the first". Eight hits on affine opens, scheme covers and
   Noetherian affine covers; no matching theorem.
5. `rg` in the project's `lean/WeilConjectures/AlgebraicGeometry` and
   `lean/Sheaf/AlgebraicGeometry`, for `ample.*orbit|orbit.*ample|affine.*orbit|orbit.*affine`:
   the latter has finite quotient admissibility and orbit-in-affine results, but none
   constructs these sections and boundary. Broader generic-point and `Aut` searches
   identified the standard APIs already used by existing modules.
6. `grep -rn` for the item id in `lean/WeilConjectures`: no matches.
   `rg` for `ample_orbit_affine_pair|exists_affine_section_pair|orbit_affine_pair` in
   Mathlib, both project roots and `dag/lean_names_upstream.json`: no matches.

Validation: the complete delivered module was compiled through `scompile.py`, in
both the wrapper's sandbox and library module contexts, with no errors or warnings.
All universes and variables are explicitly bound and `autoImplicit` is disabled.
No statement dispute or dependency-interface repair was needed.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
