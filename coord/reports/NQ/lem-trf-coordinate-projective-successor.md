## Worker report

The module `Sheaf.TraceFormula.CoordinateProjectiveSuccessor` states
`Submodule.exists_coordinate_projective_successor` with its whole proof `sorry`.
It adds no definitions, helper theorems, assumptions, or statement corrections.
Source read: `literature/stacks-project/algebra.tex`, Tag 05A9,
`theorem-ffdescent-projectivity`, especially the successor paragraph at lines
22481–22502, and Tag 05A8, `lemma-adapted-submodule`, at lines 22438–22458.
The six-step proof docstring follows all six steps of the DAG node's proof.

Hypothesis and clause correspondence:

- Commutative rings and faithfully flat homomorphism: `{A : Type u} [CommRing A]`,
  `{B : Type v} [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]`.
  An algebra over a commutative ring encodes an arbitrary unital homomorphism to
  the commutative ring B; this imposes no extra condition on that map.
- Arbitrary A-module: `{M : Type w} [AddCommGroup M] [Module A M]`.
- Arbitrary index set and family of B-modules: `{I : Type t} {Q : I → Type s}`
  with the dependent additive group and B-module instances. All five universes
  are explicitly declared and independent; there is no cardinal restriction.
- Each Q_i countably generated: `hQcount`, the existence of a countable subset
  `c` with `Submodule.span B c = ⊤`. Span uses finite linear combinations.
- Each Q_i projective: `hQproj : ∀ i, Module.Projective B (Q i)`.
- The fixed decomposition is `θ : B ⊗[A] M ≃ₗ[B] ⨁ i : I, Q i`.
- U and H are the explicit binders `(U : Submodule A M) (H : Set I)`.
- T(U) = D_H is `hU`: the range of θ composed with
  `U.subtype.baseChange B` equals `DirectSum.coordinateSubmodule B I Q H`.
  The same range expression renders T(V) in the conclusion. This is a range
  over B, hence exactly the image of the inclusion after scalar extension.
- The specified x outside U is `(x : M) (hx : x ∉ U)`.
- The witnesses are `∃ (V : Submodule A M) (J : Set I)`.
- J lies in I minus H: `J ⊆ Hᶜ`.
- U is contained in V and V contains x: `U ≤ V ∧ x ∈ V`.
- T(V) = D_(H union J): the next range equality uses
  `DirectSum.coordinateSubmodule B I Q (H ∪ J)`.
- V/U is represented by `V ⧸ U.comap V.subtype`, the quotient of V by the
  inverse image of U. Under the preceding `U ≤ V` this is precisely V/U,
  not the image of V in a different ambient module.
- Countable generation of V/U: `∃ c : Set (V ⧸ U.comap V.subtype),
  c.Countable ∧ Submodule.span A c = ⊤`.
- Projectivity of V/U: `Module.Projective A (V ⧸ U.comap V.subtype)`.
- The canonical map V/U → M/U is
  `(U.comap V.subtype).mapQ U V.subtype le_rfl`.
  Here the compatibility proof `le_rfl` expresses the defining comap condition;
  it is not an extra hypothesis or a theorem proved in this delivery.
  Its `.baseChange B` is the canonical B-linear tensor map in the node.
  `Function.Injective` states exactly its requested injectivity.
- The induced quotient identification is the existential B-linear isomorphism
  `ρ : B ⊗[A] (M ⧸ U) ≃ₗ[B] ⨁ i : {i : I // i ∉ H}, Q i.val`.
  It is fixed by the equation
  `ρ (b ⊗ₜ[A] U.mkQ m) i = θ (b ⊗ₜ[A] m) i.val`
  for every b, m, and remaining index i. These equations uniquely determine it:
  quotient representatives lift from M, pure tensors generate the tensor
  product, and coordinates determine elements of a direct sum. Thus this is
  exactly the isomorphism induced by θ and projection, not an arbitrary
  isomorphism chosen to make the image assertion hold.
- Under that identification the final range equality states that the image of
  the canonical tensor map is the coordinate submodule indexed by
  `{i : {i : I // i ∉ H} | i.val ∈ J}`. This is exactly J among the remaining
  coordinates, with the same family Q restricted to those coordinates.
- No finite generation, finite presentation, nontriviality, nonempty index set,
  freeness, or countability of U, M, H, I, or J is assumed.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'` in Mathlib's TensorProduct
  Defs/Basic, and the standard scalar-extension map `LinearMap.baseChange`
  in `Mathlib.LinearAlgebra.TensorProduct.Tower` (lines 661–667).
- `def-weil-pbc-direct-sum-modules`: `DirectSum` in
  `Mathlib.Algebra.DirectSum.Basic`, its module structure and `DirectSum.lof`
  and `DirectSum.component` in `Mathlib.Algebra.DirectSum.Module`.
- `def-trf-coordinate-submodule`: `DirectSum.coordinateSubmodule` in
  `Sheaf.RingTheory.CoordinateSubmodule`, read in full. Its carrier is exactly
  the finite-support families whose coordinates outside the set vanish.
- `def-weil-pbc-projective-module`: `Module.Projective` in
  `Mathlib.Algebra.Module.Projective`; its split-free-surjection definition,
  lifting property, and direct summand equivalences were read.
- `def-weil-pbc-quotient-module`: `Submodule.hasQuotient`,
  `Submodule.Quotient.module`, `Submodule.mkQ`, `Submodule.mkQ_surjective`,
  `Submodule.ker_mkQ` in Mathlib's Quotient Defs/Basic, together with
  `Submodule.mapQ` (whose full signature and definition were read).
- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`. This recorded declaration
  directly describes faithful flatness of B for the algebra-map action.

Private proof imports retain the stated proof plan:
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`,
`Sheaf.LinearAlgebra.CountableSubmoduleAdaptedToBaseChangeSum`, and
`Sheaf.RingTheory.CountableProjectiveFaithfullyFlatDescent`.
The projective-sum and direct-summand dependencies are already supplied by the
public Projective import, and flat tensor injectivity is supplied by the public
FaithfullyFlat import. All six statement dependency interfaces are usable.
No dependency module or new node is needed.

Edge cases checked before writing:

- I empty: the tensor decomposition is zero and faithful flatness forces M zero;
  then hx is impossible. No nonempty assumption is introduced.
- H = I, U = M, M = 0, or the zero ring: the invariant and faithful flatness
  likewise preclude an x outside U, so these cases remain in the statement.
- H empty and U = 0 are allowed: the conclusion gives the ordinary first
  enlargement and the same canonical quotient map.
- Individual Q_i may be zero; no requirement that J be nonempty or countable
  is added. Such zero coordinates do not affect any image equality.
- U can be arbitrarily generated. Only Q_i and V/U have countable spanning
  subsets. Empty generating subsets are allowed for zero modules.
- The remaining index type is the actual complement subtype; the dependent
  family retains its original Q_i without a universe equality or transport.

Searches made on 2026-10-24 (msearch wrapper, NQ/item; raw results in the
sandbox's `searches.jsonl`):

- LeanFinder: "Faithfully flat scalar extension coordinate submodule enlargement
  containing a chosen element with countably generated projective quotient".
  Eight hits on faithful flatness and flat finite-presentation criteria; no
  coordinate successor theorem.
- Loogle: "Module.Projective, Module.FaithfullyFlat, Submodule". Zero hits.
- Mathlib grep: `(coordinate|adapted).*(submodule|projective)|(projective).*(countabl|faithfully)`.
  Ten unrelated elliptic-curve coordinate hits; no match.
- LeanSearch: "Faithfully flat base change coordinate enlargement with countably
  generated projective quotient". Eight hits on faithful flatness and base
  change, none stating the successor lemma.
- Local rg in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `coordinate_projective_successor|CoordinateProjectiveSuccessor`: no hits.
  Searching the item id in WeilConjectures also found nothing. Searching
  `dag/lean_names_upstream.json` for the proposed name found nothing.
- Concept search in WeilConjectures and Sheaf for coordinate successor/enlargement
  and projective quotients found no matching statement; related countable
  coordinate closure and the main faithful-flat projectivity theorem were read.
  The latter only states projectivity descent, not this enlargement lemma.

Validation: the prescribed scompile.py compiled both the sandbox probe and
`Sheaf.TraceFormula.CoordinateProjectiveSuccessor` successfully (4.5 s and 3.0 s).
The first compile exposed complement coercion syntax in subtype binders; using
explicit `{i : I // i ∉ H}` fixed it without changing any mathematics.
All declarations have explicit universes and binders; `autoImplicit` is false.
There are no diagnostics other than the expected admitted-proof allowance.
No statement fault or disputed assertion was found. Only the item's `lean`
field changes, preserving all other JSON fields and the accepted split.

## Second reading by NQ

Written by the maintainer's independent reviewer (cc review service, 2026-10-24), in place of
the worker's self-check, which explicitly disclaimed being an independent reading (H11). The
Lean statement and node record were read clause by clause against the node and against Stacks
algebra.tex Tag 05A9 (`theorem-ffdescent-projectivity`, successor paragraph, lines 22484–22502)
and Tag 05A8; nothing in the Lean or the record was changed.

Clause list and rendering:

- A → B faithfully flat, commutative rings: `[CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B]` — the recorded declaration of def-weil-pbc-faithfully-flat-ring-map. Correct.
- M an arbitrary A-module: `[AddCommGroup M] [Module A M]`; no finiteness. Correct.
- I a set, Q_i countably generated projective B-modules: `I : Type t`, `Q : I → Type s`,
  `hQcount` (countable set with span ⊤ = finite linear combinations), `hQproj`. Correct; no
  countability of I.
- θ : B ⊗_A M ≅ ⊕ Q_i, B-linear: `θ : B ⊗[A] M ≃ₗ[B] ⨁ i : I, Q i`. Correct.
- T(W) = θ(im(B⊗W → B⊗M)): `LinearMap.range (θ.toLinearMap.comp (W.subtype.baseChange B))`;
  range of a composite is θ of the image. Correct, used identically for U and V.
- D_H: `DirectSum.coordinateSubmodule B I Q H` (live carrier: ∀ j ∉ H, x j = 0). Correct.
- Hypotheses T(U) = D_H and x ∉ U: `hU`, `hx`. Correct.
- ∃ V, J ⊆ I∖H: `∃ V J, J ⊆ Hᶜ`. Correct.
- U ⊆ V, x ∈ V, T(V) = D_{H∪J}: verbatim clauses. Correct.
- V/U countably generated and projective over A: `V ⧸ U.comap V.subtype` is V/U given U ≤ V;
  countable spanning set and `Module.Projective A`. Correct.
- Canonical map B⊗(V/U) → B⊗(M/U) injective: `((U.comap V.subtype).mapQ U V.subtype le_rfl).baseChange B`
  is the map induced by inclusion; `Function.Injective`. Correct.
- Identification B⊗(M/U) ≅ ⊕_{I∖H} Q_i induced by θ and projection: `∃ ρ` with the pure-tensor
  coordinate formula `ρ (b ⊗ U.mkQ m) i = θ (b ⊗ m) i.val`; pure tensors of classes span and
  coordinates separate, so ρ is uniquely pinned (not an arbitrary isomorphism).
- Image = J-coordinate submodule: range equality with `coordinateSubmodule` on the complement
  subtype at `{i | i.val ∈ J}`, same family `Q i.val`. Correct.

Edge cases: I empty or H = I force B⊗M/U = 0 hence M = U by faithful flatness, so hx is
vacuous-excluded, not assumed away; zero Q_i and empty/uncountable J allowed; U = 0, H = ∅ allowed.
Universes u v w t s independent; no extra instance, no Noetherian/finite hypothesis.

One definition per notion: no new definitions; only the landed `DirectSum.coordinateSubmodule`
and Mathlib notions are used. Searched lean/Sheaf and the item name: no existing statement.

Records: `lean.statement` is verbatim the file signature; stmt_deps unchanged from the live node;
docstrings carry the source place, `(blueprint: lem-trf-coordinate-projective-successor)` and the
six proof steps; proof is `sorry`. Private imports (CountableSubmoduleAdaptedToBaseChangeSum,
CountableProjectiveFaithfullyFlatDescent) exist in the live tree. No mismatch found.
