## Worker report

The module `Sheaf.FieldTheory.CommonExtensionFields` states
`Field.exists_common_extension`, with its sole proof left `sorry`. No definition,
extra node, dependency module, or statement correction is needed.

Hypothesis and conclusion correspondence:

- “Let k be a field”: `(k : Type u) [Field k]`.
- “E/k and F/k are field extensions”: `(E : Type v) (F : Type w)` with
  `[Field E] [Field F] [Algebra k E] [Algebra k F]`. These use precisely the
  Mathlib interpretation recorded on `def-pc-field-extension`.
- “There exists a field M”: `∃ (M : Type (max v w)) (_ : Field M)`.
- The common field is an extension of k: the existential `(_ : Algebra k M)`.
- “k-field embeddings E → M and F → M”: the existential
  `(i : E →ₐ[k] M) (j : F →ₐ[k] M)` and
  `Function.Injective i ∧ Function.Injective j`. `AlgHom.commutes'` makes both
  maps commute with the given maps from k. Thus the two copies of k agree.
  The explicit injectivity is exactly the embedding requirement, also automatic
  for unital maps between fields, rather than a restriction on the extensions.

Dependency declarations read and used:
`def-pc-field-extension` is a Mathlib leaf whose `mathlib_match` is `Algebra`
from `Mathlib.Algebra.Algebra.Defs`; its full class declaration and docstring
were read, together with `RingHom.toAlgebra` there. `Algebra` is imported through
`Mathlib.Algebra.Algebra.Hom`, which supplies `AlgHom` (its full structure and
commuting-square clause were read). `Field` comes from
`Mathlib.Algebra.Field.Defs`. The recorded injectivity explanation
`RingHom.injective` in `Mathlib.RingTheory.SimpleRing.Basic` was read; no import
of that proof lemma is needed to state this theorem.

Edge cases: trivial extensions E = k or F = k, E = F, arbitrary characteristic,
inseparable extensions, and transcendental extensions are all included. There
is no finite-dimensional, algebraic, separable, or linear-disjointness hypothesis.
A zero ring is not a field and is correctly excluded. All three input universes
are independent and explicit. The witness universe `max v w` is sufficient:
the tensor product E ⊗[k] F and its residue field have this universe, independently
of u, as also in Mathlib's `IntermediateField.LinearDisjoint.isField_of_forall`.
Hence the witness size does not exclude any pair of extensions. `autoImplicit`
is disabled explicitly. The docstring reproduces all four node proof steps
and their node references; no proof is implemented.

Source checked: https://stacks.math.columbia.edu/tag/0H7K, currently Lemma 9.6.9.
Its statement is exactly the common-extension statement, with no extra hypothesis.
The local literature checkout is absent on this machine, so the authoritative
Stacks page was opened directly. The node's older lemma numbering is harmless;
the stable tag identifies the same result. The node's tensor-product proof
matches the alternative argument discussed on that page.

Searches on 2026-10-11:

- `msearch.py ... leanfinder "any two extensions E and F of a field k embed as k
  algebras into a common extension field"`: eight hits, including
  `IntermediateField.Lifts` and results about algebraic embeddings, no exact
  common-overfield theorem.
- `msearch.py ... loogle "Field, Algebra, AlgHom"`: twelve hits about fraction
  rings, algebraic endomorphisms, and polynomial maps; no exact theorem.
- `msearch.py ... grep "common.*extension|exists.*field|exists.*Field"
  FieldTheory`: inspected the closest hit
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain` in
  `Mathlib.FieldTheory.LinearDisjoint` (full signature and docstring, lines
  652–664). It requires `IsDomain (A ⊗[F] B)` and also concludes linear
  disjointness, so is not the unconditional statement here.
- `msearch.py ... leansearch "any two field extensions embed into a common field
  extension"`: service unavailable, Internal Server Error; no verdict from
  this unavailable service.
- `rg -n "common.*extension|exists_common|exists_field"` over
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`:
  unrelated compactification, point-count, and sheaf results; no match.
- `grep -rn "lem-weil-common-extension-fields"` over the source library:
  no match.
- `rg -n "exists_common_extension|CommonExtensionFields"` over Mathlib, the
  source library, repository `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no name collision.

Server validation: `scompile.py H1 lem-weil-common-extension-fields` on the
module compiled cleanly in 1.0 seconds, exit code 0, with no warnings.
No statement fault or disputed claim was found.

## Second reading by H1

I independently read the sandbox node and the complete module, the dependency
`def-pc-field-extension`, and the source `fields.tex`, section `section-extensions`,
through `lemma-common-extension-field` (Stacks Tag 0H7K). The local Stacks checkout
is absent; I read the authoritative TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/fields.tex and
checked https://stacks.math.columbia.edu/tag/0H7K. The surrounding section defines
extensions as fields with a base-field ring map and extension morphisms as
base-field algebra morphisms. It imposes no standing finiteness, algebraicity,
separability, or characteristic assumption. The source proof first treats a
finitely generated extension, but explicitly asserts the unrestricted result;
that restriction is not a hypothesis of the statement.

Object/hypothesis/conclusion inventory and its Lean rendering:

- Base object: a field `k`. Rendered by `(k : Type u) [Field k]`; exact.
- First object and structure: a field extension `E/k`. Rendered by
  `(E : Type v) [Field E] [Algebra k E]`; exact, with its specified base map.
- Second object and structure: a field extension `F/k`. Rendered by
  `(F : Type w) [Field F] [Algebra k F]`; exact, independent of `E`.
- Conclusion object: some field `M`. Rendered by
  `∃ (M : Type (max v w)) (_ : Field M)`; exact up to the harmless size choice
  checked below.
- Conclusion structure: `M` is an extension of the same `k`. Rendered by the
  dependent existential `(_ : Algebra k M)`; exact. This structure precedes
  both maps, so one common base map is chosen for them.
- First conclusion map: a `k`-field embedding `E → M`. Rendered by
  `(i : E →ₐ[k] M)` and `Function.Injective i`; exact.
- Second conclusion map: a `k`-field embedding `F → M`. Rendered by
  `(j : F →ₐ[k] M)` and `Function.Injective j`; exact. The conjunction requires
  both embeddings simultaneously into the same field. No surjectivity,
  disjointness, generation condition, or identification of their images is added.

Dependency signatures checked directly: `Algebra` in
`Mathlib.Algebra.Algebra.Defs` extends scalar multiplication and supplies a
unital `algebraMap : k →+* E`, with the scalar action determined by that map.
`RingHom.toAlgebra` at line 197 constructs precisely this structure from any
ring map into a commutative ring, so the class introduces no extra hypothesis
for fields. This is the usable `mathlib_match` of `def-pc-field-extension`.
`Field` in `Mathlib.Algebra.Field.Defs` extends `CommRing` and `DivisionRing`.
`AlgHom` in `Mathlib.Algebra.Algebra.Hom`, lines 30–32, extends `RingHom` and
requires `i (algebraMap k E r) = algebraMap k M r` (and likewise for `j`).
Thus these are the node's extension morphisms, rather than arbitrary field
maps. `RingHom.injective` in `Mathlib.RingTheory.SimpleRing.Basic`, lines 67–70,
confirms that the explicit injectivity clauses do not strengthen the source's
extension-morphism formulation. The dependency's spectrum remark is not an
additional object needed to state this field-theoretic lemma. No dependency
module or new definition node is required.

Edge cases: identity extensions, `E = F`, and independently chosen base maps
are covered. Positive characteristic, characteristic zero, inseparable and
transcendental extensions, and extensions of arbitrary degree are covered.
An empty type or zero ring cannot be a field, agreeing with the source;
empty schemes, an index set, and an integer `n` are not objects of this node.
All input universes `u`, `v`, `w` are explicitly bound and independent.
The witness universe is sufficient because `E ⊗[k] F` and its ideal quotient
have universe `max v w`, even when `u` is larger. I checked the concrete
maximal-ideal quotient construction in
`IntermediateField.LinearDisjoint.isField_of_forall`,
`Mathlib.FieldTheory.LinearDisjoint`, lines 669–683: it uses exactly
`let K : Type (max v w) := A ⊗[F] B ⧸ M`, then its field and base-algebra
structures and both factor algebra maps. Thus this size choice does not
exclude an extension pair or demand a universe equality.

Independent searches, using different wording from the first reader:

- LeanFinder via `msearch.py`: “amalgamation of arbitrary fields over a common
  subfield into an overfield”. Eight hits, principally `IntermediateField.Lifts`
  and its extension results, not an unconditional common-overfield theorem.
- LeanSearch via `msearch.py`: “Two algebras which are fields over the same field
  admit injective algebra homomorphisms to some field”. The service returned
  Internal Server Error; recorded as unavailable, with no negative verdict.
- Loogle via `msearch.py`: `Algebra ?k ?E, Algebra ?k ?F, ∃ M, _`. Twelve hits
  about submodules, ranges, and localization representatives; no exact statement.
- `rg` of Mathlib FieldTheory, RingTheory/LinearDisjoint and
  RingTheory/TensorProduct for `amalgam`, `common.?overfield`,
  `common.?extension`, and `exists_field_of_isDomain`. The closest theorem is
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`; I opened its
  full signature at lines 656–659. It assumes `IsDomain (A ⊗[F] B)` and asserts
  linear disjointness, so cannot replace this unrestricted statement.
  The related `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`
  is also conditional on that tensor product being a domain.
- `rg` of the source `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the above concepts, the item id, and
  `Field.exists_common_extension`: only unrelated sheaf amalgamations appeared;
  no matching declaration or name collision.

Docstring review: the module and theorem carry the stable source tag and the
item's blueprint id. The theorem docstring follows the node's four steps in
order: injective tensor factor maps, nontrivial tensor product, maximal ideal
and field quotient, then the two induced unital maps with zero kernels. All
four non-elementary dependency ids are present. The alternative tensor proof
is the node's proof; it need not copy the source's simple-extension proof.
There is one theorem with proof `sorry`, no definitions or implemented proofs,
no unbound variables, no declaration prefix `Sheaf`, and no line over 100
characters. Both imports supply notions used in the signature.

No mismatch was found, so I changed neither the module nor the node record.
The recorded `lean.statement` is verbatim the theorem signature before `:=`.
The only addition is this independent reading. Server compilation and the
delivery preflight are run again by this reader before pushing.
