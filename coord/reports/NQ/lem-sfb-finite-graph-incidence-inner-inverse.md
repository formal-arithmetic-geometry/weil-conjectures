## Worker report

The module `Sheaf.Combinatorics.FiniteGraphIncidenceInnerInverse` states
`FiniteGraphCycleCharacter.exists_incidence_innerInverse`. Its only theorem has
proof `sorry`; no new definitions, extra nodes, dependency repairs, or statement
corrections are needed. The original node changes only in `lean`.

Clause correspondence:

- Finite sets V and E: `{V : Type u} {E : Type v} [Finite V] [Finite E]`.
  The two explicitly declared universes are independent. These binders do not
  require an enumeration, decidable equality, inhabitedness, or connectedness.
- Source and target maps: `(s t : E → V)`.
- No loops: `(_hne : ∀ e : E, s e ≠ t e)`. The underscore only suppresses an
  unused-proof-argument warning; the hypothesis remains in the theorem type.
- Parallel edges are permitted: no injectivity or uniqueness condition is imposed
  on the endpoint pair map. Distinct edges can have identical endpoints.
- The free module Z^S of integer-valued functions is exactly `(S → ℤ)` with
  Mathlib's pointwise integer-module structure. `Pi.basisFun ℤ S` is its standard
  basis; on a finite type its basis vector is `Pi.single i 1`.
- The node says “let d be the linear map determined by” its standard-basis values.
  This is rendered by `(d : (E → ℤ) →ₗ[ℤ] (V → ℤ))` and
  `hd : ∀ e : E, d ((Pi.basisFun ℤ E) e) =
    (Pi.basisFun ℤ V) (t e) - (Pi.basisFun ℤ V) (s e)`.
  This is precisely the node's characterization, not an unconstrained map or an
  additional assumption on the graph. `Module.Basis.constr` constructs the map
  for every s,t, `Module.Basis.constr_basis` verifies its values, and basis
  extensionality gives uniqueness.
- The conclusion is `∃ r : (V → ℤ) →ₗ[ℤ] (E → ℤ), d ∘ₗ r ∘ₗ d = d`.
  Thus r has the specified direction, is integral-linear, and satisfies exactly
  the required equality of linear maps.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: recorded `Module.Free`, in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, read with its docstring and complete
  signature. The node also describes a basis, represented here by Mathlib's
  `Module.Basis` and the standard `Pi.basisFun` in
  `Mathlib.LinearAlgebra.StdBasis` (definition and basisFun_apply read).
  Both modules are public imports. The only proof dependency is this same node.
- `Module.Basis.constr`, `Module.Basis.constr_basis`, and `constr_eq` in
  `Mathlib.LinearAlgebra.Basis.Defs` were read to check that hd is the defining
  characterization of an always-existing unique map.
- Read `FiniteGraphCycleCharacter.boundary` in the already landed downstream
  module `Sheaf.Combinatorics.FiniteGraphCycleCharacterQuotient` and its node's
  declaration record. It is exactly the basis-extension construction for d.
  It is not imported: that theorem's proof uses the present item, so importing
  it would obstruct the intended dependency direction. No second definition of
  boundary is introduced here. Its existing helper can be passed directly as d
  using Mathlib's `Module.Basis.constr_basis`.

Source: read `literature/stacks-project/curves.tex`, lemma-glue-points,
lines 3105–3150 (Tag 0C1M). As the node explicitly says, that source motivates
the incidence auxiliary but does not claim this integral graph lemma. The
complete four-step agent-written proof from the accepted node is carried in the
theorem docstring: the vertex relation, representatives and witnessed paths,
linear extension, and cancellation on every edge followed by basis expansion.

Edge cases checked before writing: V empty forces E empty for endpoint maps;
then both lattices are zero. E empty with arbitrary V gives d = 0 and r = 0.
An isolated vertex causes no constraint and may be sent to zero. A single edge
has boundary b_target - b_source, with the displayed signs giving d r d = d.
Parallel edges are separate coordinates, including opposite orientations.
Disconnected graphs use one representative per class; a directed triangle is
allowed and the theorem makes no injectivity claim for d. No nonempty or
connectedness assumption enters the signature.

Searches made through msearch.py for NQ and this item:

- LeanFinder: “The integer incidence map of a finite directed multigraph has an
  inner inverse r satisfying boundary r boundary equals boundary”. Eight hits,
  chiefly `SimpleGraph.incMatrix` product identities; no matching theorem.
- Loogle: `LinearMap, "inverse"`. Twelve hits, including `LinearMap.inverse`
  and `LinearMap.leftInverse_splittingOfFunOnFintypeSurjective`. The former
  assumes a two-sided inverse, the latter surjectivity onto the full function
  module; neither holds for a general graph incidence map. Read their source
  signatures; these do not give the required inner inverse.
- Mathlib grep: `oriented.*incidence|incidence.*(split|range|image)|innerInverse`
  in LinearAlgebra: zero hits.
- LeanSearch: “The incidence homomorphism of a finite directed multigraph over
  the integers has an inner inverse”. Eight hits, including the unoriented
  simple-graph incidence matrix and generic inverse constructors; none matches.
- Read `Mathlib/Combinatorics/SimpleGraph/IncMatrix.lean` introduction and
  `incMatrix`: its entries are unsigned and oriented incidence is a TODO.
- `rg` on `lean/WeilConjectures` for incidence/innerInverse/finiteGraph found
  unrelated coincidence and algebraic-geometry incidence material; literal grep
  for the item id found no upstream declaration.
- `rg` on `lean/Sheaf` for incidence/finiteGraph/innerInverse found the downstream
  character-quotient boundary helper above, and unrelated incidence geometry.
  The helper is used through its exact basis-value interface, not redefined.
- Checked the proposed theorem name against `lean/Sheaf`, upstream Mathlib
  LinearAlgebra, and `dag/lean_names_upstream.json`: no collision.

Validation: scompile.py compiled the final module in sandbox mode and at its
library module path with no errors and no warnings. All variables and universes
are explicitly bound, and autoImplicit is false. No STATEMENT-DISPUTED issue or
node fault was found.

## Second reading by NQ

The dispatcher explicitly forbids starting another agent and states that the
maintainer performs an independent delivery review. This section records my
second pass over the node and final file, not a claim of an independent worker.
The finite-set and no-loop hypotheses are present; all function modules are
literally the node's integer-valued functions; hd is exactly the prescribed
standard-vector formula. The existential r and composite equality are identical
to the conclusion. Empty and disconnected cases remain included. Rechecked the
basis extension construction to ensure hd adds no restriction. No mismatch was
found in this pass, and no node correction was made.
