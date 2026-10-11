## Worker report

The module states that an integral scheme `Z` of finite type over an algebraically closed
field `k`, with `topologicalKrullDim Z = 0`, has an isomorphism structure morphism to
`Spec k`.  The field hypothesis is `[Field k]`; algebraic closedness is `[IsAlgClosed k]`;
the scheme is `[Z.Over (Spec (.of k))]`; integrality is `[IsIntegral Z]`; finite type is rendered
by `[LocallyOfFiniteType (Z ↘ Spec (.of k))]` and `[QuasiCompact (Z ↘ Spec (.of k))]`; the
dimension clause is `(h_dim : topologicalKrullDim Z = 0)`; and the conclusion is
`IsIso (Z ↘ Spec (.of k))`.

Dependencies used are Mathlib's `AlgebraicGeometry.IsIntegral` from
`Mathlib.AlgebraicGeometry.Properties`, `Mathlib.FieldTheory.IsAlgClosed.Basic`'s
`IsAlgClosed`, `Mathlib.Topology.KrullDimension`'s `topologicalKrullDim`, and the finite-type
morphism classes `LocallyOfFiniteType` and `QuasiCompact` from Mathlib morphism modules.
The project convention node `def-weil-pbc-scheme-conventions` supplies the interpretation of
finite type over `Spec k`; no private definitions are introduced.

Edge cases checked: `IsIntegral` includes nonemptiness, so the empty scheme is excluded;
`topologicalKrullDim` uses `WithBot ℕ∞`, and equality to `0` is the stated zero-dimensional
case; no characteristic or cardinality restriction beyond a field and algebraic closedness
is added; the universe of `Z` and `k` is shared (`Type u`).

Searches: `rg -n "zero.*dim|dim.*zero|integral.*point|IsIso.*↘ Spec"` over the project and
slopmaster2 source found no matching declaration.  `rg -n "topologicalKrullDim|IsIntegral.*Scheme"`
found only general dimension and integral-scheme declarations.  Mathlib searches recorded in
the node found no theorem identifying an integral zero-dimensional finite-type scheme with
`Spec k`, so this statement module is required.

Additional searches made through `msearch.py`:

- LeanFinder: "integral zero-dimensional scheme of finite type over an algebraically closed
  field has isomorphic structure morphism to Spec k" returned `affine_isIntegral_iff`,
  `IsIntegral`, the unique carrier of Spec of a field, and other ingredients; no match.
- Loogle: "AlgebraicGeometry.IsIntegral, topologicalKrullDim" returned zero hits.
- Grep: "IsAlgClosed|topologicalKrullDim" in AlgebraicGeometry returned Artinian and
  algebraically closed residue-field ingredients; no matching theorem.
- LeanSearch: "integral zero-dimensional scheme of finite type over algebraically closed
  field is Spec of that field" was unavailable (Internal Server Error), recorded as such.
- Exact node id and declaration-name searches in the upstream name map and source found
  no existing declaration. The earlier direct source and project searches also found none.

Read full defining signatures/docstrings for `IsAlgClosed`, `IsIntegral`,
`topologicalKrullDim`, `LocallyOfFiniteType`, and `QuasiCompact`. The convention node is
explicitly a collection of pointers, with no declaration to import. No new notion or
unusable dependency is needed. Stacks 06LH was read at
https://stacks.math.columbia.edu/tag/06LH because the local literature file is absent;
its finite Artinian algebra conclusion specializes exactly to the integral case here.
No node correction or statement dispute is needed.

Server compilation succeeded with no errors or warnings after adding the explicit
QuasiCompact import. The final module contains exactly one theorem, with proof `sorry`.

The independent second reading is left to the dispatched second worker.

## Second reading by P1

I reread the node statement, its dependency records, the Stacks source (Varieties,
Lemma 33.20.2, tag 06LH), and the Lean declaration. The item-by-item rendering is:

- The algebraically closed field (k) is `{k : Type u} [Field k] [IsAlgClosed k]`.
  This gives exactly a field with algebraic closedness and introduces no characteristic
  or cardinality assumption.
- The scheme (Z) is `(Z : Scheme.{u}) [Z.Over (Spec (.of k))]`; the shared universe
  permits the same schemes covered by the node and the `Over` instance supplies its
  structure morphism to `Spec k`.
- Integrality is `[IsIntegral Z]`, the Mathlib scheme predicate corresponding to the
  node's integral scheme and carrying nonemptiness. No separate reducedness or
  irreducibility hypothesis is added.
- Finite type over (k) is rendered by
  `[LocallyOfFiniteType (Z ↘ Spec (.of k))]` and
  `[QuasiCompact (Z ↘ Spec (.of k))]`, exactly the convention's locally-finite-type
  plus quasi-compact characterization. No quasi-separated, noetherian, separated,
  or proper assumption is present.
- The dimension assumption is `(h_dim : topologicalKrullDim Z = 0)`, the recorded
  topological Krull dimension and the node's zero-dimensional clause.
- The conclusion is `IsIso (Z ↘ Spec (.of k))`, precisely that structure morphism is
  an isomorphism, with no extra conclusion or changed quantifier order.

The source's general finite disjoint union conclusion specializes to the integral case:
nonemptiness and irreducibility leave one component, and algebraic closedness identifies
its finite residue field with (k). Thus the specialized conclusion is sound. Edge cases
were checked: the empty scheme is excluded by `IsIntegral`; dimension zero is expressed
by equality in `WithBot ℕ∞`; (n=0) and characteristic cases are irrelevant and not
silently restricted; and the shared `Type u` universe does not exclude the node's cases.

I searched the project and slopmaster2 source with `rg`, and Mathlib with grep, LeanFinder,
Loogle, and `msearch.py` queries for zero-dimensional integral schemes, `IsIso` to
`Spec`, `topologicalKrullDim`, and `IsIntegral`; no existing declaration states this
specialization. The recorded `IsIntegral`, `IsAlgClosed`, `topologicalKrullDim`,
`LocallyOfFiniteType`, and `QuasiCompact` declarations match their dependency notions.
No new notion or dependency module is needed, and no mismatch was found. The module
compiled cleanly with `scompile.py`; its sole theorem remains a statement with `sorry`.
