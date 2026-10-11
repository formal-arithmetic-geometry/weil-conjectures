## Worker report

The module states the Artin–Schreier assertion for an algebraically closed field.  The
binder `{k : Type*} [Field k] [IsAlgClosed k]` renders an algebraically closed field.  The
natural number `p` together with `[Fact p.Prime]` and `[CharP k p]` renders characteristic
`p > 0` (the positive characteristic is prime).  The first conjunct,
`Function.Surjective (fun x : k => x ^ p - x)`, renders surjectivity of
`x ↦ x^p-x`.  The second conjunct identifies its kernel,
`{x : k | x ^ p - x = 0}`, with the range of the canonical prime-field embedding
`ZMod.castHom (dvd_refl p) k`, rendering the stated kernel `F_p`.

The declaration is `IsAlgClosed.artinSchreier_surjective_and_kernel` in
`Sheaf.AlgebraicGeometry.ArtinSchreier`; its proof is `sorry` as required.  It imports
`WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic`, whose
`IsAlgClosed.surjective_pow_sub_self` gives the existing surjectivity statement, but that
declaration does not include the kernel clause and therefore is not an attachment of this
node.  The kernel is represented directly by the range of the canonical `ZMod p` map.
There are no statement dependencies in the node.

Edge cases checked: `p` is prime and hence nonzero; the `Fact p.Prime` hypothesis prevents
the characteristic-zero/`p = 0` case, and `Set.range (ZMod.castHom ...)` includes every
prime-field element.  The set comprehension includes exactly the zeroes of the map,
including the zero element.  No finiteness, separability, or extra hypothesis is added.

Searches: `rg` in Mathlib and `WeilConjectures` for `ArtinSchreier`,
`surjective_pow_sub_self`, and `pow_eq_self` found only
`IsAlgClosed.surjective_pow_sub_self` (the surjectivity-only declaration) and the generic
`Subfield.mem_bot_iff_pow_eq_self`; no declaration states the combined assertion.
`python3 /home/ubuntu/weil-launcher/msearch.py E1 lem-sc-artin-schreier-k leanfinder
"Artin Schreier map surjective kernel prime field"` and the corresponding `loogle`
search for `surjective_pow_sub_self, Subfield.mem_bot_iff_pow_eq_self` found those same
components but no combined theorem.  Repository grep for the node id found no Lean file.

## Earlier second reading (a previous round; superseded)

I read the node and module independently.  The field, algebraic-closure, prime-characteristic,
surjectivity, and kernel clauses match: the kernel set is exactly the zero set of `x ^ p - x`,
and `Set.range (ZMod.castHom (dvd_refl p) k)` is the canonical embedded `F_p`.  The prime
hypothesis faithfully formalizes the node's `p > 0` characteristic clause and excludes `p = 0`.
The theorem has no extra mathematical conclusion and its only proof term is `sorry`.

## Second reading by E1

I independently opened the repository node, sandbox node and Lean module, and read the
blueprint source on the server (the literature files are absent from this clone). I also
read Stacks `etale-cohomology.tex`, Tag 0A3J, lines 9599–9609: its opening sequence assumes
a prime `p` and characteristic `p`, and its map is `x ↦ x^p-x`. The blueprint field lemma
assumes only an algebraically closed field of positive characteristic. These agree here.

Object/hypothesis/conclusion checklist (H3):

- Field `k`: `{k : Type*} [Field k]`; exact, arbitrary universe, genuine nontrivial field.
- Algebraically closed: `[IsAlgClosed k]`; exact. I read Mathlib's class and root theorem
  in `FieldTheory/IsAlgClosed/Basic.lean`; no chosen algebraic closure or base field is
  required. This is the algebraically closed clause of `def-weil-algebraic-closure`.
- Characteristic `p > 0`: `(p : ℕ) [Fact p.Prime] [CharP k p]`; exact. Mathlib's `CharP`
  specifies `(n : k) = 0 ↔ p ∣ n`, as `def-pc-field-characteristic` states. Primality follows
  from positive field characteristic, so this instance adds no mathematical restriction;
  conversely prime `p` is positive. No finite-field or finite-dimensional instance is used.
- Map `k → k`, `x ↦ x^p-x`: `(fun x : k => x ^ p - x)`; exact source and target, same exponent.
- Surjective: `Function.Surjective (fun x : k => x ^ p - x)`; exact, every `a : k` has a
  preimage, with both clauses about the same field and characteristic.
- Kernel `𝔽_p`: `{x : k | x ^ p - x = 0} = Set.range (ZMod.castHom (dvd_refl p) k)`; exact.
  I read `ZMod.castHom` at `Data/ZMod/Basic.lean:331`: it is the canonical ring map from
  `ZMod p` into this characteristic-`p` field. Its injectivity makes its range the embedded
  prime field. This is a zero-fiber equality, the underlying set of the additive kernel,
  rather than a claim identifying `k` itself with a finite field. I read the proof dependency
  `lem-sc-field-artin-schreier-kernel`, Mathlib `Subfield.mem_bot_iff_pow_eq_self` and
  `ZMod.fieldRange_castHom_eq_bot`, including their signatures: the first identifies the
  Frobenius fixed points with the bottom subfield and the second that subfield with the
  canonical embedding's range. Neither alone states this node's two-clause conclusion.

Edge cases: `p = 0` and `p = 1` are excluded exactly as positive field characteristic
requires; `p = 2` is included. Zero is in both sides of the kernel equality. A zero ring
or empty carrier is not a field and is not covered by the source. Empty index sets,
empty schemes, and `n = 0` do not occur in this field statement. `Type*` generalizes the
field universe; the prime field is canonically mapped into any such universe. All variables
are bound explicitly (only `k` and `p`), with no hidden algebra, finiteness or Noetherian
hypotheses.

Independent searches (H4), using different queries from the worker:

- `msearch.py ... leansearch "In an algebraically closed field of prime characteristic the
  function x to x raised to p minus x is onto and its zero set is the embedded ZMod p"`:
  service unavailable (Internal Server Error), recorded, no mathematical verdict from it.
- `msearch.py ... loogle '"pow_eq_self"'`: nine hits, including
  `Subfield.mem_bot_iff_pow_eq_self`; none states the combined assertion.
- `msearch.py ... leanfinder "The map a ↦ a^p - a on an algebraically closed field is
  surjective with zero set the prime subfield"`: eight hits, including
  `Subfield.roots_X_pow_char_sub_X_bot` and generic Frobenius results, no combined theorem.
- `msearch.py ... grep 'fieldRange_castHom_eq_bot|mem_bot_iff_pow_eq_self|surjective.*sub_self'
  FieldTheory`: five hits, the prime-subfield components only. Direct `rg` of project
  `WeilConjectures`, repository `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  component names and delivered full name finds the existing surjectivity component but
  no combined declaration. I opened `IsAlgClosed.surjective_pow_sub_self` at line 193:
  its conclusion is surjectivity alone, despite its docstring mentioning the kernel.
  The semilinear Frobenius results are vector-space statements, not this set equality.

Repairs: no mathematical mismatch or node correction was needed, and the theorem signature
and `lean.statement` remain verbatim equal. H8: the original docstring omitted the degree
argument, primality reasoning, dependency-node names, and the identification of the bottom
subfield with the embedding's range. I expanded it to carry both node proof steps and their
references, and named the actual blueprint source alongside Stacks 0A3J. H9: added the
project's copyright/license header and replaced the unnecessary project theorem-module
import with the two Mathlib modules defining `IsAlgClosed` and `ZMod.castHom`. This supersedes
only the worker report's description of imports. There are no new nodes, dependency modules,
private definitions or hollow definitions, and the single theorem proof is still `sorry`.

Validation: compiled the delivery module with `scompile.py`; only the permitted
`declaration uses sorry` warning is acceptable. Delivery dry-run and preflight are run
before pushing.
