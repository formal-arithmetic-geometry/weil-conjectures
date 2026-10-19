## Worker report

The module `Sheaf.Paper.AlgebraicNumberRealization` defines
`WeilConjectures.FiniteFieldDatum.CoefficientDatum.AlgebraicNumberRealization`.
Its value is exactly `Qbar ≃ₐ[ℚ] algebraicClosure ℚ C.Qbar`. The relative algebraic
closure is the existing Mathlib construction, used directly, rather than a second
subfield construction. The helper instance `ratAlgebra` constructs the rational
algebra structure by composing the two specified field embeddings. All data are
written in full. There are no theorems or `sorry`s in this delivery.

The source node was read alongside its original master blueprint file and the
current main-20261015 file, both in `sec-zeta-weil/sk-thm-intfactors` under the same
node filename. Their definition agrees with the DAG. The algebraic closedness and
existence claims are explicitly deferred by the DAG to `lem-weil-realization-exists`;
this definition does not depend on that downstream theorem or choose an isomorphism.

Clause-by-clause correspondence:

- The fixed prime `p`, positive exponent `a`, equality `q = p ^ a`, field `k₀` with
  `q` elements, and chosen algebraic closure `k` are the fields and instances of
  `D : WeilConjectures.FiniteFieldDatum.{u}`. In particular `D.prime`,
  `D.exponent_pos`, `D.cardinality_eq`, `D.card_base`, and `D.isAlgClosure` retain
  all conditions rather than introducing new versions of them.
- The prime `ℓ ≠ p`, the field of adic numbers, and its chosen algebraic closure
  are `C : D.CoefficientDatum`, with `C.l`, `[C.prime]`, `C.different`, the existing
  `Padic C.l`, and `C.Qbar` equipped with `C.field`, `C.algebra`, `C.isAlgClosure`.
- The rational prime-subfield embedding is the explicit composite
  `(algebraMap (Padic C.l) C.Qbar).comp (algebraMap ℚ (Padic C.l))`, turned into an
  algebra by `RingHom.toAlgebra`. Since these are embeddings of characteristic-zero
  fields, the ambient field has characteristic zero. No extra characteristic-zero
  assumption is added. The compiler needed this rational algebra interface because
  the supplied coefficient datum itself records only its adic algebra structure.
- The subfield `{z ∈ C.Qbar | z is algebraic over ℚ}` is precisely
  `algebraicClosure ℚ C.Qbar : IntermediateField ℚ C.Qbar`.
  `mem_algebraicClosure_iff` gives exactly `IsAlgebraic ℚ z`; intermediate fields
  supply containment of the image of `ℚ` and the subfield operations. This uses
  the dependency definition and its membership interface, without restating it.
- A fixed algebraic closure of `ℚ` is any `(Qbar : Type v)` with `[Field Qbar]`,
  `[Algebra ℚ Qbar]`, and `[IsAlgClosure ℚ Qbar]`. It is not restricted to one
  implementation of `AlgebraicClosure ℚ`.
- A realization `ȷ` is an element of the defined type. The existing `AlgEquiv`
  structure is a bijective ring map commuting with `ℚ`, exactly the requested
  bijective rational embedding. Its target is the subfield, not the whole
  adic algebraic closure, and surjectivity is retained.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.CoefficientDatum` (including their full fields
  and instance attributes).
- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic` and its field structure
  (through the datum's public imports), for `def-weil-l-adic-numbers`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` and `IsAlgClosed`, for
  `def-weil-algebraic-closure`; `IsAlgClosure` includes algebraicity and algebraic
  closedness. The canonical construction in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` was also read, but the module
  permits any fixed closure as the node requests.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`, `RingHom.toAlgebra`, for
  `def-pc-field-extension`. `Mathlib.Algebra.Algebra.Rat` supplies the canonical
  `DivisionRing.toRatAlgebra` on `Padic C.l`.
- `Mathlib.RingTheory.Algebraic.Defs`: `IsAlgebraic`, for
  `def-weil-algebraic-element`, used by the relative-closure membership criterion.
- `Mathlib.FieldTheory.AlgebraicClosure`: `algebraicClosure` and
  `mem_algebraicClosure_iff`, for `def-weil-relative-algebraic-closure`.
- `Mathlib.Algebra.Algebra.Equiv`: `AlgEquiv`, with its inherited ring equivalence
  and scalar-commutation field, for `def-weil-field-extension-isomorphism`.

Edge cases checked: `a = 1` is included; arbitrary prime powers and coefficient
primes are retained by the datum, including `ℓ = 2` when `p ≠ 2`. The excluded case
`ℓ = p` is exactly the node's exclusion, carried by `C.different`. Neither a zero
field nor positive characteristic can be an algebraic closure of a characteristic
zero field. The relative closure includes zero and all rational scalars and uses
Mathlib's field construction at nonzero inverses. The source algebraic closure
has independent universe `v`; the coefficient datum has universe `u`, and the
realization type lives in `Type (max u v)`. No finite-dimensional or topological
restriction is imposed. Existence and algebraic closedness of the relative closure
are not hypotheses of the realization definition.

Searches for an existing notion:

- `msearch.py leanfinder`, query “algebraic closure of rational numbers inside an
  algebraic closure of the l-adic numbers and l-adic realization as a rational
  algebra isomorphism”: eight hits, primarily `PadicAlgCl` and its embeddings,
  `PadicComplex` and the completion equivalence. None defines this realization.
  The first interrupted query had no retained process result; the repeated read-only
  query completed and its result was inspected.
- `msearch.py loogle`, query `algebraicClosure, AlgEquiv`: three hits,
  `algebraicClosure.map_eq_of_algEquiv`, `AlgEquiv.algebraicClosure`, and
  `algebraicClosure.algEquivOfAlgEquiv`. They transport relative closures along
  existing equivalences and do not define realizations in a fixed adic closure.
- `msearch.py grep`, query
  `adicRealization|AdicRealization|algebraicClosure.*(ℚ|Rat)|[Qq]bar`, subdirectory
  `FieldTheory`: no hits. Direct source inspection confirmed the general
  `algebraicClosure` construction and its precise membership criterion.
- Direct `rg` over upstream `WeilConjectures` and project `lean/Sheaf`, query
  `adic.?realization|realization.?of.?algebraic|algebraicClosure (ℚ|Rat)|def-weil-algebraic-closure-q`
  (case insensitive): only the unrelated adic realization of sheaf complexes in
  the upstream trace-formula module; no definition of this notion. Direct
  `grep -rn` for this blueprint id in upstream sources found no attachment.
- `rg` in `dag/lean_names_upstream.json` for `algebraicClosure|AlgEquiv|Realization`
  found no realization of algebraic numbers. Exact proposed-name searches for
  `AlgebraicNumberRealization|CoefficientDatum.ratAlgebra` over Mathlib, upstream
  and project sources returned no existing declarations.

No statement correction, missing dependency, new node, or disputed statement.
The item's copy changes only `lean`.

Validation: `scompile.py Q156 def-weil-algebraic-closure-q` compiled both its sandbox
check and the actual library module separately, within the required time limit,
with no errors or warnings. The first compile exposed the missing rational algebra
instance; the canonical composite instance above repaired it without adding an
assumption or replacing the chosen coefficient field.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
