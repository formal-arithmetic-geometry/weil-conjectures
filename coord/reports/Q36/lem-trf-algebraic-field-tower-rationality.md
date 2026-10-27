## Worker report

The module `lean/Sheaf/FieldTheory/AlgebraicFieldTowerRationality.lean` states
`IsAlgClosed.bijective_field_tower_of_bijective_or_comp`. Its only proof is `sorry`.
There are no new definitions, helper declarations, dependency repairs, or statement changes.
The original node changes only in `lean`.

The source was read in `literature/stacks-project/fields.tex`, lines 900–943:
Tags 09GQ and 09GR identify algebraic closedness with triviality of algebraic extensions.
The node extracts the elementary two-alternative argument from Step 3 of
`lem-trf-etale-completed-local-ring-iso`; its complete three-step proof plan appears
in the theorem docstring.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Fields k, K, L | `{k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]` |
| k algebraically closed | `[IsAlgClosed k]` |
| Specified unital field homomorphism i : k → K | `(i : k →+* K)` |
| Specified unital field homomorphism α : K → L | `(α : K →+* L)` |
| Set j = α ∘ i | `α.comp i`, everywhere j occurs; no independent j or compatibility hypothesis |
| L algebraic over K through α | `halg : ∀ z : L, ∃ p : Polynomial K, p ≠ 0 ∧ p.eval₂ α z = 0` |
| Each element is a root of a nonzero polynomial with coefficients in α(K) | `p.eval₂ α z` evaluates coefficients by α; injectivity of a field homomorphism makes `p ≠ 0` equivalent to its mapped polynomial being nonzero |
| Either i or j is bijective | `hbij : Function.Bijective i ∨ Function.Bijective (α.comp i)` |
| All three specified maps i, j, α are bijective | `Function.Bijective i ∧ Function.Bijective (α.comp i) ∧ Function.Bijective α` |

No finiteness, characteristic, separability, or abstract field-isomorphism assumption
has been substituted. The algebraicity formula is exactly Mathlib's `IsAlgebraic`
defining formula with the coefficient homomorphism specified explicitly, via the
algebra structure `α.toAlgebra`; it introduces no second definition.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, including its
  full signature/docstring. This is the three field-instance binders.
- `def-weil-algebraic-closure`: its `mathlib_match.how` explicitly names `IsAlgClosed`
  in `Mathlib.FieldTheory.IsAlgClosed.Basic`; this is the clause used here, rather
  than choosing a canonical `AlgebraicClosure`. Both source definitions were read.
- `def-pc-field-extension`: the recorded `Algebra` in `Mathlib.Algebra.Algebra.Defs`
  and its note expressly allow a specified ring homomorphism through
  `RingHom.toAlgebra`. The source of both declarations was read. We use the node's
  explicit-homomorphism presentation `RingHom`, with its unital structure and
  `RingHom.comp` from `Mathlib.Algebra.Ring.Hom.Defs`; no arbitrary algebra structure
  or additional tower compatibility is imposed.
- Proof dependency `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`:
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`, its complete signature
  and docstring in `Mathlib.FieldTheory.IsAlgClosed.Basic` were read. Its module is
  already the public import needed for the statement, so it is imported only once.
  The theorem docstring explains its application to the relative algebraic closure.

All statement/proof dependency modules are available through the sole public import
`Mathlib.FieldTheory.IsAlgClosed.Basic`. The statement's polynomial evaluation is
Mathlib `Polynomial.eval₂` (`Mathlib.Algebra.Polynomial.Eval.Defs`), whose source was read.

Edge cases checked before writing:

- Identity maps satisfy both alternatives and the conclusion.
- Bijective composite: injectivity of α cancels α(i(a)) = α(b), so i and α are
  surjective; this case needs no extra algebraicity assumption beyond the node's.
- Bijective first map: lifting coefficients preserves nonzeroness, and 09GQ/09GR
  forces every element into the image of the composite. Algebraicity is not replaced
  by the stronger condition of finite extension.
- Dropping algebraic closedness fails for the identity R → R followed by R → C.
- Dropping algebraicity fails for k → k → k(t), with k algebraically closed and
  the first map the identity.
- The zero polynomial is expressly excluded. Constants cannot witness a root
  unless zero, since α is injective. Empty/zero fields are excluded exactly by `Field`.
- Independent explicit universes u, v, w permit arbitrary sizes of the three fields;
  no characteristic restriction is present.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder query: `In a tower of field homomorphisms k to K to L with k algebraically closed and L algebraic over K, if either k to K or k to L is bijective then all three maps are bijective`.
  Eight hits, including `IsAlgClosed.algebraMap_bijective_of_isIntegral`,
  `Algebra.IsAlgebraic.algHom_bijective₂`, and scalar-tower bijectivity lemmas.
  None states the two-alternative assertion about these three specified maps.
- Loogle query: `IsAlgClosed, Algebra.IsAlgebraic`. Eleven hits, including the
  existing intermediate-field proof leaf and algebraic-closure/embedding results;
  none is the requested statement.
- Grep query: `algebraMap_bijective_of_isIntegral|bijective_of_isScalarTower|ringHom_bijective_of_isIntegral`,
  subdirectory `FieldTheory`. Five hits in `IsAlgClosed/Basic.lean` and
  `Normal/Defs.lean`; the former's candidate signatures were read. They give the
  algebraic-extension ingredient, not the disjunction and all three conclusions.
- LeanSearch: the same full tower query as LeanFinder. Eight hits, with
  `IsAlgClosed.ringHom_bijective_of_isIntegral` as another ingredient; no exact match.
- Local `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `algebraic_field_tower|algebraicFieldTower|bijective.*[Tt]ower|[Tt]ower.*bijective|lem-trf-algebraic-field-tower-rationality`:
  only unrelated quotient, stalk, representation and coefficient-tower declarations.
- Local `rg` for algebraic/rational tower variants and `bijective.*isAlgClosed`:
  unrelated finite-field and cohomological base-change statements. The finite-field
  result imposes finiteness and does not state the requested tower assertion.
- Required `grep -rn` for the item id under `lean/WeilConjectures`: no hits.
- Exact-name `rg` in Mathlib, both project roots and the upstream name index:
  no existing `bijective_field_tower_of_bijective_or_comp`.

No statement dispute or node fault was found. No repair note exists for this item.

Validation: `scompile.py Q36 lem-trf-algebraic-field-tower-rationality <file>` passed
both its sandbox and library-mode checks (1.1 s and 1.2 s), without errors or warnings.

## Second reading by Q36

Author's separate rereading of the node and completed file; independent delivery
review is the maintainer's responsibility under the dispatcher brief, which forbids
starting another agent. This is not represented as an independent review.

The three field binders match the node and all universes are explicitly declared.
`IsAlgClosed k` constrains only the bottom field. Both ring-homomorphism binders
preserve 1 by their bundled type; composition is literally `α.comp i`. Each element
of L receives a nonzero polynomial over K evaluated through that same α. Thus the
algebraicity condition uses the actual given embedding, not a potentially different
algebra instance. The disjunction preserves both stated alternatives. The conjunction
contains all three bijectivity assertions in the node's order, and none is replaced
by existence of an abstract isomorphism. No missing clause or additional hypothesis
was found, and no statement correction was made. The docstring gives each of the
node's three proof steps; the file contains just the one theorem with `sorry`.
