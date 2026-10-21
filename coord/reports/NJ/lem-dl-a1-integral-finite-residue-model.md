## Worker report

Item: `lem-dl-a1-integral-finite-residue-model`, group NJ, stage 2, 2026-10-21.

The delivery states `Algebra.exists_integral_finite_residue_model` in
`Sheaf.RingTheory.IntegralFiniteResidueModel`. Its sole theorem has proof `sorry`.
There are no new definitions, additional nodes, dependency repairs, or statement changes.
Only the item's `lean` record is changed.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0BSR,
`lemma-etale-makes-integral-split`, statement and entire first proof (lines 12210 onward).
The node requests the fraction-numerator/denominator variant of the finite intermediate
algebra construction. The Lean states that variant without localizing A, assuming A -> D
injective, or assuming any full residue extension E/k finite.

Hypothesis-by-hypothesis correspondence:

- A -> D: `{A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]`.
  An algebra structure gives precisely a unital homomorphism of commutative rings,
  with no injectivity hypothesis. The universes u and v are independent and explicit.
- D integral over A: `[Algebra.IsIntegral A D]`, meaning every element of D is integral.
- Prime p: `(p : Ideal A) [p.IsPrime]`.
- k = Frac(A/p): `p.ResidueField`; the Mathlib source supplies
  `IsFractionRing (A ⧸ p) p.ResidueField`.
- The complete finite, repetition-free fibre, including t = 0:
  `(hfibre : (p.primesOver D).Finite)` and the index subtype `r : p.primesOver D`.
  `Ideal.primesOver` is exactly the set of prime ideals lying over p. Indexing by that
  set rather than an enumeration supplies each prime exactly once and does not choose
  or assume a nonempty index set.
- E_r = Frac(D/r): `r.1.ResidueField`. Its k-embedding is always the specific
  `Ideal.ResidueField.map p r.1 (algebraMap A D) (r.1.over_def p)`.
- The given subfields containing k: the family F of `IntermediateField`s, with the
  above canonical k-algebra structure explicitly passed. `IntermediateField` includes
  precisely a subfield and containment of the image of the base field.
- F_r/k finite-dimensional: `hfinite`, `FiniteDimensional p.ResidueField (F r)` with
  the canonical restricted scalar action `Subalgebra.algebra` written explicitly.
- F_r/k separable: `hseparable`, `Algebra.IsSeparable` for exactly that same action.
  Its definition requires every element's minimal polynomial to be separable.
- E_r/F_r purely inseparable: `hpure`, `IsPurelyInseparable (F r) r.1.ResidueField`;
  the algebra action here is the inclusion of the intermediate field.

Conclusion-by-conclusion correspondence:

- A subring C of D containing im(A): `∃ C : Subalgebra A D`. This is the same datum
  as that subring with its induced A-action, not an abstract algebra mapping to D.
- C is A-module-finite: `Module.Finite A C`.
- Contraction induces a bijection on the two entire prime fibres:
  `Set.BijOn (fun r : Ideal D ↦ r.comap C.val) (p.primesOver D) (p.primesOver C)`.
  `BijOn` includes mapping into the indicated fibre, injectivity there, and surjectivity
  onto that fibre. The map is actual ideal contraction along the subalgebra inclusion.
- s_r = C intersect r: `r.1.comap C.val`.
- Frac(C/s_r) viewed inside E_r is the family L, specified by the equality
  `(L r).toSubfield =
    (Ideal.ResidueField.map (r.1.comap C.val) r.1 C.val rfl).fieldRange`.
  Thus L is pinned to the image of the canonical residue-field embedding. It is not
  an arbitrary extension or a chosen substitute. An existential intermediate field
  with this exact equality simply states that this image contains k. The canonical
  map is injective because it is a unital map of fields. Mathlib's fraction-ring
  instance identifies its source with Frac(C/s_r).
- That image contains F_r: `(F r).toSubfield ≤ (L r).toSubfield` (the fully explicit
  `IntermediateField.toSubfield` applications in the file supply the canonical action).
- That image is finite-dimensional over k: `FiniteDimensional p.ResidueField (L r)`
  with the same explicit restricted canonical scalar action.
- E_r/Frac(C/s_r) is purely inseparable: `IsPurelyInseparable (L r) r.1.ResidueField`.
  The preceding image equality identifies this inclusion extension with the one in
  the node, so there is no independently chosen residue-field homomorphism.
- Finally D is integral over C: `Algebra.IsIntegral C D`, using the actual inclusion.

Dependency declarations used and inspected:

- The sole statement dependency `def-weil-pbc-finite-purely-inseparable-extension`
  records `Mathlib.FieldTheory.PurelyInseparable.Basic`, `IsPurelyInseparable` and
  `Module.Finite`. Its class and `isPurelyInseparable_iff_pow_mem` were read. Only pure
  inseparability, without module finiteness of E/F or E/L, is used: the node explicitly
  permits infinite purely inseparable residue extensions.
- Proof dependency `lem-weil-pbc-integral-incomparability`:
  `Mathlib.RingTheory.Ideal.GoingUp`, `Ideal.IsIntegral.comap_lt_comap`.
- Proof dependency `def-weil-finite-dimensional-subspace`:
  `FiniteDimensional`, defined as `Module.Finite` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, publicly available through
  `Mathlib.LinearAlgebra.FiniteDimensional.Basic`.
- Proof dependency `lem-sc-finite-generated-integral-subring`:
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`,
  `Algebra.finite_adjoin_of_finite_of_isIntegral`.
- Proof dependency `lem-weil-pbc-integral-injective-lying-over`:
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, `RingHom.IsIntegral.comap_surjective`.
- Proof dependency `lem-weil-pbc-finite-dimensional-domain-is-field`:
  `Mathlib.LinearAlgebra.FiniteDimensional.Basic`, `fieldOfFiniteDimensional` and
  `FiniteDimensional.exists_mul_eq_one`.
- Canonical notions reused directly: `Ideal.primesOver` and its prime/lying-over
  instances (`Mathlib.RingTheory.Ideal.Over`); `Ideal.ResidueField` and its canonical
  `map` and fraction-ring instance (`Mathlib.RingTheory.LocalRing.ResidueField.Ideal`);
  `IntermediateField`, its `toSubfield`, `toSubalgebra`, and induced algebra actions
  (`Mathlib.FieldTheory.IntermediateField.Basic`); `RingHom.fieldRange`
  (`Mathlib.Algebra.Field.Subfield.Basic`, transitively imported).

All proof dependency modules that have usable Mathlib records are imported. The module
retains the entire seven-step natural-language proof in its theorem docstring.

Edge cases checked mathematically before drafting:

- Empty fibre: the finite-set hypothesis allows it, the F/L families are empty, and
  `Set.BijOn` forces the C-fibre also empty. Take C = im(A), with no residue generators;
  integral lying over for C into D proves this fibre claim.
- D the zero ring: its prime fibre is empty; C is the image of A, hence the zero ring,
  finite as an A-module, and both fibres are empty. A the zero ring has no prime p,
  so the theorem correctly has no such instance.
- Noninjective A -> D and p outside its spectrum image: neither injectivity nor a
  chosen fibre point is imposed. The empty-fibre construction still applies.
- One fibre point, or F = k: no pairwise separators are needed; a finite spanning
  family and its fraction lifts suffice. No positivity or nonempty binder appears.
- Characteristic zero: pure inseparability means E = F, and containment forces L = E.
- Positive characteristic: arbitrarily large/infinite purely inseparable extensions
  E/F are allowed. Every exponent witness over F is also one over L.
- C need not be a domain; only its quotients by the relevant primes are domains.
- u and v may differ; the set of primes and all fraction-field constructions remain
  in their natural ring universes. No equality of universes or test-type restriction.

Searches made (wrapper outputs are retained in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder` query: "An integral algebra admits a finite subalgebra
  preserving a finite prime fibre and containing prescribed finite separable residue
  subfields". Eight hits: quasi-finite residue-field finiteness, algebraicity of integral
  residue extensions, and universal coprime factorization. None constructs C with all
  the required properties.
- `msearch.py ... loogle` query: `Algebra.IsIntegral, Subalgebra, Module.Finite`.
  Four hits: finite integral adjoin and linear-disjointness reductions, no exact match.
- `msearch.py ... grep` query: `exists.*subalgebra|finite.*adjoin|residueFieldMap`,
  subdirectory `RingTheory/IntegralClosure`. Ten hits about finite adjunction and
  powers in integrally closed subalgebras; no exact match.
- `msearch.py ... leansearch` query: "An integral algebra with finite prime fibre admits
  a finite subalgebra preserving the fibre and containing specified finite separable
  residue subfields". Eight hits: quasi-finite residue fields and finite integral
  adjunction. None gives fibre bijectivity and the prescribed containment together.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for finite residue models, the item id,
  and `exists.*finite.*[Ss]ubalgebra`: no existing exact statement. In particular,
  `WeaklyEtaleFiniteResidueModel` concerns normal finite residue models under weakly
  etale base changes; `FiniteSubalgebraFractionField` is a polynomial fraction-field
  construction; `QuasiFiniteAtFiniteSubalgebraAway` localizes a quasi-finite algebra.
  The existing `IntegralNormalResidueEtaleSplitting` cites this node only in its proof
  plan, and states the later etale splitting, not this finite intermediate model.
- `rg` of Mathlib and both project libraries for
  `exists_finite_subalgebra_residue|finite_subalgebra.*fibre|finite_subalgebra.*fiber`:
  no exact declaration. `dag/lean_names_upstream.json` has no attachment for this item.
- Additional source greps located and verified `Ideal.ResidueField.map`,
  `Ideal.primesOver`, `RingHom.fieldRange`, `IntermediateField`'s scalar structures,
  `Algebra.IsSeparable`, and the recorded Mathlib proof-dependency signatures.

No STATEMENT-DISPUTED flag or source fault found. The finite-dimensionality assumptions
on F and separability remain present even though parts of the elementary finite-model
construction use only finiteness and containment; no hypothesis was removed.

Validation: all compilation uses the prescribed server `scompile.py`, one file at a time.
Initial elaboration errors from missing inferred canonical scalar structures were repaired
by explicit instance arguments, without adding hypotheses or helper definitions. The
subsequent typecheck succeeded; its one long-line warning was repaired before the final
clean compile and delivery preflight.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
