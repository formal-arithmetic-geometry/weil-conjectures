## Worker report

The module `Sheaf.RingTheory.BaseIdealLocalizationCertificates` states
`Ideal.baseIdealLocalization_certificates`, with one `sorry` and no new definitions.
The node's mathematical statement, dependencies and proof are unchanged. There are no
new nodes, dependency repairs, or statement disputes.

I read Stacks `literature/stacks-project/algebra.tex`, Tag 00CT
(`proposition-localize-quotient`, especially the construction of the map from the
quotient to the quotient localization), and Tag 00CM (`section-localization`, the
fraction relation, operations, and zero criterion). The explicit denominator
calculation is the node's elementary expansion of these constructions, not a
separate assertion quoted verbatim from Tag 00CT. The theorem docstring gives all
six proof steps, including the generated-ideal finite-sum argument, the map and
its uniqueness, the inverse denominators, fraction representatives, the prescribed
product calculation, and the resulting kernel witness.

Hypotheses and notation, matched to Lean:

- Arbitrary commutative rings and their ring homomorphism are `{A : Type u}`,
  `{C : Type v}`, `[CommRing A]`, `[CommRing C]`, and `(f : A →+* C)`.
  The ring universes are independent and explicitly bound.
- The arbitrary base ideal is `(I : Ideal A)`. There is no finite generation,
  locality, Noetherianity, nontriviality, injectivity, or non-zero-divisor assumption.
- The multiplicative subset is `(W : Submonoid C)`, including its unit and
  multiplication closure. Denominator variables have type `W`, so membership
  and closure are supplied by this existing type rather than extra hypotheses.
- `B` is the actual fraction construction `Localization W`, and `c/1` and `1/w`
  are `Localization.mk c (1 : W)` and `Localization.mk 1 w`. This is
  definitionally the ring case `LocalizedModule W C` of the recorded dependency;
  Mathlib's LocalizedModule/Basic source explicitly checks this definitional equality.
- `IC` is `I.map f`, the span of the image of `I`, not just its set-theoretic image.
  `IB` is `I.map ((algebraMap C (Localization W)).comp f)`, using exactly the
  composite structure map into `B`.
- `D` and `R` are respectively `C ⧸ I.map f` and
  `Localization W ⧸ I.map ((algebraMap C (Localization W)).comp f)`.
  Residue classes use `Ideal.Quotient.mk` throughout. The named image `bar W`
  is rendered by these residue classes of `w : W`; it needs no new definition.

Clauses, matched to Lean:

- The first existential provides a ring homomorphism `φ : D →+* R`.
  Its first conjunct is `∀ c : C, φ (Ideal.Quotient.mk (I.map f) c) = ... (c/1)`.
  Its second conjunct quantifies over every ring map `ψ : D →+* R` with this
  representative formula and states `ψ = φ`. This explicitly renders
  “characterized by”, without assuming a choice of quotient map or adding data.
- Clause (a) is `∀ w : W, IsUnit (φ (bar w)) ∧ φ (bar w) * q(1/w) = 1`.
  In a commutative ring the displayed product states precisely that `q(1/w)`
  is the inverse. The other product is equal by commutativity, including in
  the zero ring. No inverse operation on arbitrary ring elements is introduced.
- Clause (b) is `∀ r : R, ∃ (c : C) (w : W), r = φ (bar c) * q(1/w)`.
  By clause (a), this is exactly the required fraction with inverse denominator.
- Clause (c) is `∀ c : C, φ (bar c) = 0 → ∃ v : W, ...`.
  Both `v*c ∈ I.map f` and `(bar v)*(bar c) = 0` are included.
- The additional certificate is the second outer conjunct. It quantifies over
  every finite type `ι : Type t`, with `[Fintype ι]` and `[DecidableEq ι]`,
  independently of the ring universes. These are finite-sum/product indexing
  data available for every finite family, including the empty family.
  Its variables `a : ι → I`, `d : ι → C`, `w : ι → W` enforce the stated
  memberships exactly. The relation is
  `Localization.mk c 1 = ∑ i, Localization.mk (f (a i) * d i) (w i)`.
- The named product and numerator are explicit variables `(p : W) (e : C)`
  under the equalities `p = ∏ i, w i` and
  `e = ∑ i, f (a i) * d i * ∏ j ∈ Finset.univ.erase i, (w j : C)`.
  These equalities are only the node's “setting w=... and e=...” notation;
  they do not restrict any family. This avoids a statement-level `let`.
- The conclusion provides `u : W` and all three requested assertions:
  `(u : C) * ((p : C) * c - e) = 0`,
  `((u * p : W) : C) * c = (u : C) * e`, and
  `(u : C) * e ∈ I.map f`. In particular the equality and membership
  together state `(up)c = ue ∈ IC`.

Dependency declarations read and used:

- `def-weil-pbc-module-localization` records
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`.
  I read its docstring, `mk`, `mk_eq`, and the explicit definitional identification
  with `Localization` in the same file. The delivered module publicly imports it.
  `Mathlib.RingTheory.Localization.Basic` supplies the ring fraction interface.
- `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf with no Lean record.
  I read `AlgHom` in `Mathlib.Algebra.Algebra.Hom`, `Ideal.Quotient.algebra`
  and `Ideal.Quotient.mkₐ` (including surjectivity and kernel signatures) in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, and the ring map
  `Ideal.Quotient.mk` in `Mathlib.RingTheory.Ideal.Quotient.Defs`.
  The quotient operations module is publicly imported. The recorded ideal
  operations are imported through these modules; no private replacement is used.
- `Ideal.map` in `Mathlib.RingTheory.Ideal.Maps` is explicitly the span of the
  image and is used for both extended ideals. The finite sums and products use
  `Mathlib.Algebra.BigOperators.Ring.Finset`.

Edge cases checked before and against the written signature:

- Empty index type: `p=1`, `e=0`, and `c/1=0` gives the ordinary zero criterion.
- `I=⊥`: all `a i` are zero, leaving the same annihilator criterion. `I=⊤`:
  both quotient rings are zero, where their unique element is a unit.
- `W={1}`: the localization is the original ring, the denominator products
  are 1, and the relation is the ordinary finite-sum equality.
- `0 ∈ W`: the localization and its quotient are zero. Taking multiplier 0
  supplies the kernel and denominator witnesses; no case is excluded.
- Zero ring `C`: allowed by `[CommRing C]`, with every clause interpreted normally.
- Zero divisors: in `C=Z/6Z`, with `W={1,3}`, `I=0`, the empty relation
  for `c=2` is valid in the localization; the witness `u=3` kills `c`.
  Thus the statement retains the necessary extra multiplier and does not
  silently infer `pc=e` in `C` from equality in the localization.
- Noninjective `f` and arbitrary, infinitely generated `I` are permitted.
  Each relation and ideal-membership expression uses only finitely many terms.

Searches performed on 2026-10-24:

- `msearch.py ... leanfinder`, query “Quotient of localization by extended base
  ideal has fraction representatives unit denominators kernel annihilator witnesses
  and explicit finite product denominator certificate”: eight hits, including
  `IsLocalizedModule.commonDenom`, `IsLocalization.commonDenom`, their Finset
  versions, `IsLocalization.surj₂`, `IsLocalization.integerMultiple`,
  `IsLocalization.mem_span_map`, and
  `IsLocalization.exist_integer_multiples_of_finite`. None states the node's
  combined result or its prescribed product and numerator certificate.
- `msearch.py ... loogle`, query `IsLocalization, RingHom.ker`: eight hits,
  including `IsLocalization.of_surjective`, `RingHom.toKerIsLocalization`,
  `AlgHom.toKerIsLocalization`, and `IsLocalization.ker_map`. I read
  `of_surjective` and the quotient localization instance immediately after it
  in `Mathlib/RingTheory/Localization/Ideal.lean`. They give an abstract
  localization criterion, not the prescribed denominator certificate.
- `msearch.py ... grep`, query
  `quotient.*[Ll]ocaliz|[Ll]ocaliz.*[Qq]uotient|mk_sum` in
  `RingTheory/Localization`: 16 hits. I read `Localization.mk_sum`; it handles
  a fixed common denominator and is not the node's assertion.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for quotient/localization,
  denominator certificates and the proposed declaration name found related
  localization material but no exact statement; searching for the node id in
  `lean/WeilConjectures` found no declaration. A focused search in both
  RingTheory directories and `dag/lean_names_upstream.json` found no name clash.
  The previously recorded searches in the node were read and left unchanged.

Validation: the prescribed `scompile.py Q13 lem-trf-base-ideal-localization-certificates`
compiled the module as both sandbox and library module on the server, cleanly
(1.2 seconds for each). All variables and all universes are explicitly bound.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
