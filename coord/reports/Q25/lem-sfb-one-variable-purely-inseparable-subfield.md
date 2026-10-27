## Worker report

The module `Sheaf.FieldTheory.OneVariablePurelyInseparableSubfield` states
`IntermediateField.exists_pow_eq_of_purelyInseparable_of_trdeg_one`, with one
`sorry` and no new definitions. The node statement and all other node fields
apart from `lean` are unchanged. No new nodes or dependency repairs are needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `(k : Type u) [Field k]`; algebraic closedness is `[IsAlgClosed k]`.
- Positive characteristic p is `(p : ℕ) [CharP k p] (hp : 0 < p)`.
  Primality follows from these assumptions and is not an extra hypothesis.
- The ambient field is `(L : Type v) [Field L] [Algebra k L]`.
  `(E : IntermediateField k L)` supplies a field containing the specified image
  of k, its given inclusion into L, and the compatible k-algebra structures.
  This is the bundled form of the node's given field inclusions; it makes no
  assertion merely up to isomorphism and imposes no normality/separability condition.
- Finite generation of E/k as a FIELD extension is
  `hfgE : (⊤ : IntermediateField k E).FG`. Finite generation of L/k is
  `hfgL : (⊤ : IntermediateField k L).FG`. Mathlib's `IntermediateField.FG`
  means generation by a finite set under field operations, including inversion.
  Neither hypothesis uses finite generation as an algebra.
- Transcendence degree one for E/k is `htrdegE : Algebra.trdeg k E = 1`;
  for L/k it is `htrdegL : Algebra.trdeg k L = 1`.
- Finiteness of L/E is `[Module.Finite E L]`; pure inseparability is
  `[IsPurelyInseparable E L]`, along the canonical inclusion of E into L.
- A nonnegative integer r is `∃ r : ℕ`.
- The first conclusion is `FieldExtension.degree E L = ((p ^ r : ℕ) : WithTop ℕ)`.
  It uses the recorded definition of vector-space degree, with infinity for
  infinite extensions. Under the stated finiteness assumption it is the cast
  of `Module.finrank E L`.
- The second conclusion is
  `(E : Set L) = Set.range (fun x : L ↦ x ^ (p ^ r))`.
  Equality of the underlying sets of subfields is exactly equality inside L;
  `Set.range` is the literal set of powers specified by the node. This is
  stronger than a field isomorphism and does not replace the range by its
  generated subfield. No independent definition of a power subfield is needed.
- The conjunction uses the SAME existential r for both conclusions.
  Universes u and v are explicit and independent, and E inherits the universe
  of L. `set_option autoImplicit false` excludes auto-bound variables.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: the algebraically closed clause is `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, explicitly identified in mathlib_match.
  The theorem assumes algebraic closedness of k, not a chosen closure extension.
- `def-pc-field-characteristic`: `CharP`, `Mathlib.Algebra.CharP.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`;
  `IntermediateField` in `Mathlib.FieldTheory.IntermediateField.Basic` packages
  the inclusions and their compatibility without a private copy of the notion.
- `def-kun-transcendence-degree`: `Algebra.trdeg`,
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, and `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`. The former's equivalence with the
  p-power membership condition is `isPurelyInseparable_iff_pow_mem`.
- `def-pc-field-tower`: `FieldExtension.degree`, `Sheaf.FieldTheory.FieldTower`.
  Its full real definition was read; it is not replaced by a private degree.
- The auxiliary finite-field-generation predicate is Mathlib's
  `IntermediateField.FG`, `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`.

The statement dependencies have public imports. Already stated proof dependencies
are plain imports, following stage-2 rule 7: the upstream pth-root tower module,
Mathlib's transcendence-degree tower and algebraicity modules, degree
multiplicativity, and `Sheaf.AlgebraicGeometry.Curve.AlgClosedCurveModel`.
The latter's theorem and the upstream tower theorem were read with their signatures
and docstrings. `lem-sfb-smooth-curve-function-field-p-basis` has neither a `lean`
record nor a Mathlib match in the supplied DAG, so no unrecorded module name is
invented for this proof-only dependency. It remains named in the full proof-plan
docstring; it is not required to type this statement. The four proof steps are
included in that docstring, with their supporting DAG node names.

Source and edge cases:

Read `literature/stacks-project/curves.tex`, the full statements and proofs of
Tags 0CCX and 0CCY and their assembly in 0CCZ. Over algebraically closed k,
`k L^p = L^p` since every element of k has a pth root in k. The degree-p
calculation and iteration therefore give precisely the node's conclusion.
The empty root tower gives E = L, r = 0, p^0 = 1 and the identity power map;
this case is included. For L = k(t), E = k(t^(p^r)), the degree and subset
clauses have the stated exponent for r = 0, 1 and 2. Characteristic two is
included. p = 0 is excluded exactly by the source's positive-characteristic
assumption; p = 1 is inconsistent with `[Field k] [CharP k p]`, not an added
restriction. The case E = k cannot satisfy transcendence degree one and is
correctly excluded by the existing hypothesis. Arbitrary independent carrier
universes are allowed. No statement dispute or node fault was found.

Searches for an existing statement (all through the prescribed tools):

- LeanFinder query: "Finite purely inseparable intermediate subfield of a one
  variable function field over an algebraically closed field is a power subfield
  with degree p to the same exponent". Eight hits: root-membership criteria,
  `IsPurelyInseparable.finrank_eq_pow`, finite-exponent and perfect-closure results.
  None identifies the entire intermediate field with the exact power range.
- Loogle query: `IsPurelyInseparable.finrank_eq_pow`. One exact name hit; it
  only asserts that the degree is a power, with no subfield equality.
- LeanSearch query: "A finite purely inseparable intermediate field of a
  transcendence degree one function field over an algebraically closed field
  is the image of iterated Frobenius". Eight hits, including
  `IsPurelyInseparable.iterateFrobenius` and its scalar variants, and the
  intermediate-field pure-inseparability criteria. None gives the stated
  surjectivity onto E using the one-variable hypothesis.
- msearch grep query:
  `(trdeg|FG|finrank).*(frobenius|PurelyInseparable)|frobenius.*(trdeg|finrank)|power subfield`
  in Mathlib/FieldTheory: six hits, on finite-field Frobenius and perfect
  closures; no full match. Read the finrank theorem and the power-membership
  equivalence in Mathlib/PurelyInseparable/Basic after these hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `one.variable.*inseparable|inseparable.*subfield|trdeg.*frobenius|frobenius.*trdeg|power subfield`
  found only unrelated prose in SemilinearGaloisAlterationDomination.
- Direct search for this item's id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no declaration.
- Additional project/Mathlib name search for
  `purelyInseparable.*power|exists.*power.*subfield|exists_pow_subfield|one_variable_purely|oneVariablePurely`
  found only unrelated power-series subfield-family results.
- The chosen full declaration name was searched in Mathlib, WeilConjectures,
  Sheaf, and `dag/lean_names_upstream.json`; no existing occurrence.

Validation: the prescribed `scompile.py` compiled both its sandbox check and
`Sheaf.FieldTheory.OneVariablePurelyInseparableSubfield` against the live server
library, each in 1.5 seconds, with exit code 0 and no warnings or errors.
Every theorem proof is `sorry`; no proof or hollow definition was added.

## Second reading by Q25

A separate second reading by the same worker was performed with the original
node JSON and the final module open; the dispatcher expressly forbids starting
other agents, and the maintainer supplies the independent review of the delivery.
The field, algebraic-closedness and positive-characteristic binders match the
opening clause. `IntermediateField k L` preserves both given inclusions, while
its subtype carries the E/k and L/E instances. Both FG hypotheses and both
trdeg-one hypotheses are present separately. `Module.Finite E L` and
`IsPurelyInseparable E L` refer to this inclusion. The two conclusions share r;
`FieldExtension.degree` is the dependency's vector-space degree, and the set
equality identifies E with all powers, without an abstract isomorphism or an
adjoin operation. r = 0 is permitted and imposes no nontrivial-extension
assumption. All universes and variables are bound. The source's degree-p
iteration is reproduced in the docstring, and no theorem was proved. No
mismatch was found and no statement correction was made on this pass.
