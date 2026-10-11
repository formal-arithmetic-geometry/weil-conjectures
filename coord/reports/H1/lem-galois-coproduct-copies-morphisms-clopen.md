## Worker report

The module defines `AlgebraicGeometry.IsClopenDecomposition` and states
`AlgebraicGeometry.coproductCopiesMorphismsClopen`, with a `sorry` proof. It uses the
canonical scheme coproduct `∐ fun _ : E => U`, its coprojections `Sigma.ι`, and its fold
map `Sigma.desc (fun _ : E => 𝟙 U)`. The Stacks source is Groupoids, Example 03YW,
read at `/home/ubuntu/c1-stacks-review/groupoids.tex:534-562`; the repository's
`literature/stacks-project/groupoids.tex` was not present on this machine.

Hypotheses and clauses, in the order of the node:

- `U W : Scheme.{u}` and `s : W ⟶ U` render the base scheme, test scheme, and
  structural morphism. `E : Type v` with `[Small.{u} E]` renders an arbitrary set
  whose indexed coproduct belongs to the universe of `Scheme.{u}`. It permits empty
  and infinite indices; `Small` is Mathlib's universe requirement for this coproduct.
- `IsClopenDecomposition W E P` requires `P : E → W.Opens`, disjointness at unequal
  indices, and `⨆ e, P e = ⊤`. Closedness follows because each complement is the
  union of the other open pieces; it is not an additional hypothesis.
- Clause (a): the first conjunct says the opens `f ⁻¹ᵁ (Sigma.ι ... e).opensRange`
  form that decomposition whenever `f ≫ Sigma.desc ... = s`. Its `∀ e` equation
  is the required equality of morphisms after restricting along the open-subscheme
  inclusion `.ι`.
- Clause (b): the second conjunct states `∃! f` over `U` with exactly the prescribed
  preimages, for every indexed clopen decomposition `P`.
- The third conjunct gives an `Equiv` between the subtype of morphisms over `U`
  and the subtype of indexed clopen decompositions. Its equation specifies that the
  equivalence is precisely inverse image of the coprojection ranges.
- The fourth conjunct gives the equivalent bijection with `LocallyConstant W E`.
  Its fibre equation identifies each open component with `{x : W | b f x = e}`.
  Mathlib's `LocallyConstant` means locally constant into the discrete index type.
- Clause (c): the fifth conjunct says the section `s ≫ Sigma.ι ... e₀` has component
  preimage `⊤` at `e₀` and `⊥` at every other index.
- For empty `E`, the final conjunct explicitly asserts the coproduct is empty and
  an over-`U` morphism exists exactly when `W` is empty. Its uniqueness is also
  covered by clause (b), applied to the unique empty decomposition.

Dependency declarations checked in full: `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (`Mathlib.AlgebraicGeometry.Scheme`);
`AlgebraicGeometry.IsOpenImmersion` and `Scheme.Hom.opensRange`
(`Mathlib.AlgebraicGeometry.OpenImmersion`); the scheme coproduct instance,
`AlgebraicGeometry.sigmaOpenCover`, and `AlgebraicGeometry.disjoint_opensRange_sigmaι`
(`Mathlib.AlgebraicGeometry.Limits`). The same Mathlib modules provide `Sigma.ι`,
`Sigma.desc`, and the open-subscheme API. No private replacement is introduced.

Edge cases checked: empty `E`, empty `W`, nonempty `E` with the constant section,
empty pieces within a decomposition, and arbitrary infinite `E`. The equations
do not assume inhabitedness, finiteness, connectedness, or a characteristic.

Searches for an existing statement: `msearch.py leanfinder` query
"morphisms from scheme W to coproduct indexed copies of scheme U over U correspond
to clopen decompositions of W" returned `sigmaMk`, `sigmaOpenCover` and related
coproduct ingredients, not this correspondence. `msearch.py loogle` query
"AlgebraicGeometry.sigmaMk, AlgebraicGeometry.Scheme.fiberOpens,
CategoryTheory.Limits.Sigma.desc" returned no hits because `Scheme.fiberOpens` is
not in Mathlib. `msearch.py grep` query
"sigmaMk|fiberOpens|locallyConstant|clopen" in `AlgebraicGeometry` returned
`sigmaMk` and unrelated local-constancy lemmas. `rg` for coproduct/clopen and
`fiberOpens` in `WeilConjectures` found only partial ingredients, including
`Scheme.fiberOpens` in its Mathlib extensions; `grep -rn` for the node id in
`WeilConjectures` found nothing. `rg` in `lean/Sheaf` found no match.
Neither new full declaration name occurs in the source tree or Mathlib.

The server compile through `scompile.py` exited 0 with no messages or warnings.

## Second reading by H1

I read the node, its three statement dependencies, the Lean module, and Stacks
Groupoids Example 03YW (`groupoids.tex:535-562`). The source starts with an
arbitrary group and an arbitrary base scheme; its functor-of-points argument
only uses the underlying index set. Schemes 01JB and 01HI supply the gluing
and open restriction used by the node. There is no field, characteristic,
Noetherian, separatedness, or finiteness hypothesis.

- Objects: `(U W : Scheme.{u})` and `(s : W ⟶ U)` are exactly the base,
  test scheme, and structure morphism. `E : Type v` represents the index set.
  `[Small.{u} E]` is the size condition for Mathlib's `Scheme.{u}` coproduct,
  not a finiteness or inhabitedness condition. The node's `U_E`, `ι_e`, `π`,
  and `V_e` are respectively `∐ fun _ : E => U`, `Sigma.ι ... e`,
  `Sigma.desc (fun _ : E => 𝟙 U)`, and `(Sigma.ι ... e).opensRange`.
  Verdict: same objects and canonical maps.
- Decomposition: `IsClopenDecomposition W E P` takes `P : E → W.Opens` and
  requires disjointness at distinct indices and `⨆ e, P e = ⊤`.
  Its pieces are closed because each complement is the union of the other
  open pieces. `W.Opens` and `.ι` are Mathlib's open subschemes and their
  inclusions. Verdict: exactly the node's definition, without an extra
  closedness assumption.
- Clause (a): `∀ f`, followed by `f ≫ Sigma.desc ... = s →`, quantifies over
  morphisms over `U`. Its first conjunct asserts the inverse-image family
  is a decomposition. The `∀ e` equality after `.ι` is precisely
  `f ∘ j_e = ι_e ∘ s ∘ j_e`. Verdict: both clauses and quantifier order match.
- Clause (b): `∀ P`, followed by `IsClopenDecomposition W E P → ∃! f`, states
  existence and uniqueness with both the equation over `U` and every
  prescribed component preimage. The next `∃ b : ... ≃ ...` makes the
  resulting bijection explicit, with its forward-map equation.
  Verdict: no missing or stronger condition.
- Locally constant form: the second `∃ b : ... ≃ LocallyConstant W E` and
  its fibre equation identify the same morphisms with maps whose fibres
  are open. `LocallyConstant` is the Mathlib bundled locally constant map
  into a discrete type. Verdict: matches the equivalent formulation.
- Clause (c): `∀ e₀ e`, the preimage equality with `if e = e₀ then ⊤ else ⊥`
  expresses the constant section and all its components. The final
  `IsEmpty E →` gives the empty coproduct and the equivalence between an
  over-`U` map and `IsEmpty W`; uniqueness follows from clause (b).
  Verdict: both edge clauses match.

Edge cases: empty `E` and empty `W` are included; the empty decomposition
exists exactly for empty `W`. Nonempty `E` permits empty components, and the
constant-section formula includes them. Infinite `E` is allowed subject to
the category's universe size condition. No natural number or characteristic
occurs. The source's abstract group is not needed for this set-valued claim.

Independent search: `msearch.py leanfinder` for "scheme morphisms over a base
to disjoint union of copies classified by locally constant functions" returned
`sigmaMk`, `sigmaOpenCover`, and other coproduct ingredients, not the theorem.
`msearch.py loogle` for `AlgebraicGeometry.Scheme, LocallyConstant,
CategoryTheory.Limits.Sigma.ι` returned no hits. `msearch.py grep` for
`clopen decomposition|locally constant.*coproduct|coproduct.*locally constant|
opensRange_sigmaι` found only `disjoint_opensRange_sigmaι` in Mathlib.
Independent `rg` searches of Mathlib's AlgebraicGeometry files, the source
`WeilConjectures/`, and this project's `lean/Sheaf` found partial fibre and
gluing lemmas but no exact declaration or duplicate definition.

Mismatches found: none. Changes: replaced this section's pending marker with
the completed reading; the Lean module and node record needed no repair.
`scompile.py` exited 0 with no errors or warnings.
