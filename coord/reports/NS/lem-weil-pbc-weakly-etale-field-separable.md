## Worker report

Record the exact existing lemma `Algebra.WeaklyEtale.isAlgebraic` in
`WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField`, lines 93–113.
No module is written and no proof is added. Its docstring states that any weakly
etale extension of fields is algebraic separable. The complete proof was read,
as was the current server source obtained with `scompile.py --source`.
The node already has a partial attachment record; this delivery supplies the
complete stage-2 existing-declaration record, without altering any other field.

Hypotheses and conclusion, clause by clause:

- The fields k and L are `{k : Type u} [Field k]` from the surrounding section
  and `{L : Type*} [Field L]` in the declaration. The extension is `[Algebra k L]`,
  with its specified map `algebraMap k L`.
- Weak etaleness is `[WeaklyEtale k L]`. The existing class has precisely
  `Module.Flat k L` and flatness of `Algebra.TensorProduct.lmul' k (S := L)`.
- Every element is separable: the conclusion `Algebra.IsSeparable k L` has
  the field `isSeparable' : ∀ x : L, IsSeparable k x`.
- Every element is algebraic: `IsSeparable k x` is separability of `minpoly k x`;
  the minimal polynomial of a nonintegral element is zero and is not separable.
  Thus `IsSeparable.isIntegral` and `Algebra.IsSeparable.isAlgebraic` give exactly
  the algebraicity clause, not an additional assumption.

Dependency declarations read and used by the existing lemma:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`;
  read the class signature and docstring. Between fields a ring homomorphism
  is equivalently this algebra structure.
- `def-weil-pbc-ind-etale-algebra`: its record is
  `Sheaf.RingTheory.IndPrincipalZariski`, whose public imports expose the listed
  `Algebra.WeaklyEtale` from `Mathlib.RingTheory.Etale.Weakly`.
  Read the complete node, owning module, and class. Only its weakly-etale clause
  occurs here; the node's ind-etale and principal ind-Zariski clauses do not.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`. Read the class, `IsSeparable` definition,
  docstrings and algebraicity instance at lines 533–572.

Source: Stacks Tag 092P, `more-algebra.tex`,
`lemma-absolutely-flat-fields`, read together with the following lemma's
explanation that all algebras over a field are flat. The source's single
multiplication-flatness assumption is equivalent to the node's weak-etaleness
assumption for fields. No statement correction is needed.

Edge cases checked: the identity extension; finite separable extensions;
infinite separable algebraic extensions (no finite-generation assumption);
positive characteristic imperfect base fields (no perfectness assumption);
transcendental and purely inseparable nontrivial extensions are correctly
excluded by weak etaleness. The two fields have independent universes in the
existing signature. No empty or zero-ring field is permitted by `Field`.
There is no statement dispute or missing dependency.

Searches:

- msearch leanfinder, “A weakly etale extension of fields is separable algebraic”:
  eight hits on formally etale/unramified field extensions, none giving this
  statement without an essential finite type assumption.
- msearch loogle, `Algebra.WeaklyEtale, Algebra.IsSeparable`: zero hits.
- msearch grep, `WeaklyEtale.*isSeparable|class WeaklyEtale|class Algebra.WeaklyEtale`,
  RingTheory: the existing class in Mathlib/RingTheory/Etale/Weakly.lean:37.
- rg in the upstream project for the blueprint id: no hits; rg/read of
  WeaklyEtaleField.lean finds the exact existing lemma at line 94.
- rg in lean/Sheaf for weakly-etale-field statements: no duplicate;
  the group clone's lean/WeilConjectures copy has the same existing lemma.

Validation: the delivery dry run checks the existing declaration with a real
server `#check` through scompile.py and runs the maintainer preflight.

## Second reading by NS

Independently read the full node, Stacks `more-algebra.tex`, Tag 092P
(`lemma-absolutely-flat-fields`, including its proof), the following lemma's
field-flatness explanation, all three statement-dependency nodes and their
recorded declarations, and the existing lemma with its surrounding variables
and complete proof. Read the exact group-clone upstream module and obtained
its current server source using `scompile.py --source`; the signatures agree.
Also read `coord/pefw-upstream-framework.md`; this attachment uses the existing
ring-theory module, not a replacement module-object definition.

Object/hypothesis/conclusion checklist, in node order:

1. Base field k: surrounding `{k : Type u} [Field k]`. Exact.
2. Extension field L: `{L : Type*} [Field L]`. Exact; its universe is independent.
3. Specified field extension k → L: `[Algebra k L]`, with map
   `algebraMap k L`. Exact. Read `Algebra` and `RingHom.toAlgebra` in
   `Mathlib.Algebra.Algebra.Defs`, the declaration recorded by
   `def-pc-field-extension`; every ring map of fields has this encoding.
4. Weak etaleness of that same extension: `[WeaklyEtale k L]`. Exact.
   The dependency `def-weil-pbc-ind-etale-algebra` lists `Algebra.WeaklyEtale`
   among its declarations. Read its owning module
   `Sheaf.RingTheory.IndPrincipalZariski` and the actual Mathlib class:
   `Module.Flat k L` and `(Algebra.TensorProduct.lmul' k (S := L)).Flat`.
   Its multiplication is the specified tensor multiplication, not an arbitrary
   map. The source assumes only its flatness; the other class field is automatic
   over a field, as the following Stacks lemma explicitly explains.
5. Every element is algebraic over k: the conclusion `Algebra.IsSeparable k L`
   implies this through `IsSeparable.isIntegral` and
   `Algebra.IsSeparable.isAlgebraic`. Exact, not a missing conjunct.
6. Every element is separable over k: the same conclusion has field
   `isSeparable' : ∀ x : L, IsSeparable k x`, and `IsSeparable k x` means
   `(minpoly k x).Separable`. Exact. Read these declarations in
   `Mathlib.FieldTheory.Separable`, as recorded by
   `def-weil-pbc-separable-algebraic-extension`. The minimal polynomial of a
   nonintegral element is zero and is not separable, so the conclusion agrees
   with the node's separable-algebraic convention, not transcendental separability.

There are no extra hypotheses: the surrounding `R`, `CommRing R`, and `Algebra k R`
variables do not occur in this declaration and are not generalized into it.
No finiteness, perfectness, characteristic, or universe equality is assumed.
The server delivery probe checks the fully explicit `@` signature as well.

Edge cases: identity extensions and infinite algebraic separable extensions are
included. Positive characteristic and imperfect base fields are included.
Nontrivial purely inseparable and transcendental extensions cannot satisfy the
hypothesis. Fields are nontrivial, so a zero ring or empty field is outside the
node as well as the Lean; empty schemes, empty index sets and n = 0 introduce no
objects or parameters here. No unbound variable is present in the read source.

Independent searches (different queries from the first reading):

- `msearch leanfinder`: "flat diagonal of a field extension implies every minimal
  polynomial is separable" returned eight Mathlib separability definitions and
  transfer lemmas, including `Algebra.IsSeparable`, but no alternative exact theorem.
- `msearch loogle`: `Algebra.WeaklyEtale, Algebra.IsAlgebraic` returned zero hits.
- `msearch grep`: `FormallyUnramified.isSeparable|isSeparable_iff|class WeaklyEtale`
  returned the actual weakly-etale class and separability equivalences.
- Direct `rg` in Mathlib's Etale directory, the upstream project's RingTheory
  directory and this project's `lean/Sheaf` for weakly-etale/separable wording
  and `isAlgebraic` located the exact upstream lemma and no duplicate statement
  in `lean/Sheaf`. Read it rather than relying on the misleading name
  `isAlgebraic`: its conclusion really is `Algebra.IsSeparable k L`.

Verdict: the existing-declaration attachment is exact, including both conclusion
clauses. No new definition nodes, dependency modules, hollow data or postponed
proofs are introduced. Existing upstream docstrings are not rewritten: H8's
new-module/proof-docstring obligations do not call for duplicating an existing
proved declaration, and the item's `proof` is empty. The module docstring cites
Stacks 092P and the lemma docstring states the result. No statement correction
or citer audit is necessary. No mathematical or record mismatch found; second
reading adds this audit only, preserving the worker report and Lean record.
