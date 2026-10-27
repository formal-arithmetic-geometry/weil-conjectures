## Worker report

The module `Sheaf.RingTheory.IntegersClosedResidueModel` states
`Int.integers_closed_residue_model`, with one `sorry` and no new definitions.
The accepted node's mathematical statement, dependencies and proof are unchanged;
only its `lean` record is added. No missing dependency interface was encountered.

The source was read in `literature/stacks-project/more-algebra.tex`, the proof of
`proposition-ubiquity-J-2` (Tag 07PJ). At a maximal ideal the source takes the model
to be the extension field itself, finite over the base ring and regular. The
node's five proof steps expand this argument for an integer prime. All five are
included in the theorem docstring, including the explicit Bezout, kernel and
Frobenius calculations.

Hypothesis and clause correspondence:

- Rational prime: `(p : ℕ) [Fact p.Prime]`. The ideal is literally
  `Ideal.span {(p : ℤ)}` throughout. Its prime instance is supplied by Mathlib's
  `Int.ideal_span_isMaximal_of_prime` and maximal-implies-prime; no additional
  primality or localization hypothesis is assumed.
- The residue field is `(Ideal.span {(p : ℤ)}).ResidueField`, the recorded
  `Ideal.ResidueField`: definitionally the residue field of the localization at
  this prime, not a replacement by `ZMod p`.
- Surjectivity of the integer map is the first `Function.Surjective` conjunct.
- The kernel is precisely the ideal `(p)`, expressed by `RingHom.ker ... =
  Ideal.span {(p : ℤ)}`.
- The induced isomorphism is `∃ e : (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃+* ...` together
  with `∀ a : ℤ, e (Ideal.Quotient.mk ... a) = algebraMap ℤ ... a`. The
  compatibility equality ensures that it is the isomorphism induced by the
  specified integer map, not an unrelated abstract isomorphism.
- Every extension is quantified as `(L : Type u) [Field L] [Algebra k L]`, with
  `[Module.Finite k L]` and `[IsPurelyInseparable k L]`. Here `k` abbreviates the
  literal residue-field expression only in this report; there is no file-local
  notation or second field definition in the module. The map `j` is exactly
  `algebraMap k L`; an algebra structure encodes every unital field homomorphism.
  The universe `u` is arbitrary, independent of the small integer residue field.
- Surjectivity of `j` is `Function.Surjective (algebraMap k L)`.
- The named model is introduced as `∀ B : Subring L, B = (j.comp i).range → ...`,
  where `i` is the canonical integer-to-residue-field map. This equality merely
  names the exact prescribed image. It is not an assumption about an arbitrary
  substitute model: the range itself always instantiates this binder by reflexivity.
- Equality of the model with the whole field as a subring is `B = ⊤`.
- Noetherianity and module finiteness are `IsNoetherianRing B` and
  `Module.Finite ℤ B`. Every commutative ring, including the subtype ring `B`,
  has its unique canonical integer-algebra/module structure, so the prescribed
  induced integer action needs no arbitrary action or tower assumption.
- Generation by `1` is stated explicitly as
  `Submodule.span ℤ ({(1 : B)} : Set B) = ⊤`.
- The fraction clause is `∀ x : L, ∃ b c : B, (c : L) ≠ 0 ∧
  x = (b : L) / (c : L)`. The nonzero condition is in the ambient field.
- Nonemptiness of the actual affine scheme is
  `Nonempty (AlgebraicGeometry.Spec (CommRingCat.of B))`.
- Every prime localization being regular local is
  `∀ (q : Ideal B) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q)`.
- The final whole-spectrum regular-open assertion is rendered by the preceding
  nonemptiness together with `AlgebraicGeometry.IsRegularScheme (Spec (.of B))`.
  The whole space is always open, so no tautological `IsOpen Set.univ` conjunct
  is added. This is exactly the whole regular nonempty open in the node.

Dependency declarations used (the signatures and docstrings were read):

- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (used both for the
  extension hypothesis and the model's finiteness over the integers).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme`, the conjunction of local Noetherianity
  and the published stalkwise `AlgebraicGeometry.IsRegular`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, including its
  local and Noetherian superclass fields. The same module's field/Dedekind
  `IsRegularRing` instance supplies the recorded field-regular-ring proof input.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, visible through
  the regular-scheme dependency.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`.
- Proof import `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`:
  `iterateFrobeniusOfPrime`, `iterateFrobeniusOfPrime_apply`.
- Proof import `WeilConjectures.RingTheory.IntegerPrimeLocalizations`:
  `Int.prime_localizations_dvr`.

Edge cases checked before writing: `p = 2` is allowed; `p = 0,1` are correctly
excluded by primality. The identity extension `L = k` is allowed. The purely
inseparable exponent `n = 0` is covered (and is mentioned explicitly in the
proof docstring). The zero ring cannot occur as the extension field; this
exclusion comes from `Field`, exactly as in the node. `B` is always the exact
image range, contains `1`, and cannot be the zero ring in a field. Fractions
use denominator `1`, which is nonzero, after image surjectivity. No bound on
the extension field's universe or assumption of a chosen field structure on
`B` has been introduced. No statement dispute or source correction is needed.

Searches, run with the prescribed `msearch.py Q72` wrapper:

- LeanFinder: "The residue field of integers at a prime is Z modulo p and every
  finite purely inseparable extension has a finite regular integer image
  model". Eight hits, on quasi-finite and finite residue-field extensions;
  none states this integer image model.
- Loogle: `Ideal.ResidueField, IsPurelyInseparable, IsRegularRing`. Zero hits.
- Mathlib grep: `ResidueField.*(Int|ZMod)|IsPurelyInseparable.*surjective|integer.*residue`.
  Twenty-five hits, including `PadicInt.residueField` (a different local ring)
  and `IsPurelyInseparable.surjective_algebraMap_of_isSeparable` (a component,
  without this integer model or quotient compatibility).
- LeanSearch: "The residue field of integers modulo a prime and its finite
  purely inseparable extension give a finite regular image ring". Eight hits,
  including `Ideal.ResidueField` and `IsPurelyInseparable`, but no full statement.
- Local `rg` on `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for integer closed-residue and image-model names
  found no duplicate. `grep -rn` for the item id in `lean/WeilConjectures` found
  none. Wider `residue_model` searches found integral and weakly-etale finite
  residue models, which assert different hypotheses and different conclusions.
- Mathlib source searches found `Int.ideal_span_isMaximal_of_prime`, used through
  its instance to elaborate the literal prime ideal without a helper theorem.

Validation: prescribed `scompile.py` compiled both its sandbox and library module
probes cleanly (3.8 s and 2.6 s). The delivery dry run also passed preflight and
compilation. The final module additionally lists the spectrum and at-prime
localization statement dependencies as direct public imports. No errors or
unexpected warnings.

## Second reading by Q72

This is the worker's separate rereading of the completed node and module;
the dispatcher's brief forbids starting another agent, and the maintainer's
independent review follows delivery. No independent reviewer is claimed here.

On rereading I checked the original node's clauses in order against the
signature: prime `p`; literal ideal `(p)` and its localization residue field;
surjectivity and exact kernel of the integer map; compatible quotient ring
isomorphism; all finite purely inseparable extensions; surjectivity of their
structure map; exact range subring `B`; `B = ⊤`; Noetherianity; module finiteness
with explicit generator `1`; fractions with nonzero denominator; nonempty
scheme spectrum; every prime localization regular local; and regularity of
the whole spectrum using the existing regular-scheme definition. In particular,
the result is not merely existence of an arbitrary isomorphic regular model,
and the isomorphism is compatible with integer residue classes. All objects
are the recorded dependency objects. No mismatch was found or changed.
