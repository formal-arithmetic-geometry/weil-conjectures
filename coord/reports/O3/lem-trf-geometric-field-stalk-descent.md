## Worker report

The module `Sheaf.RingTheory.GeometricFieldStalkDescent` states the node verbatim in
mathematical content as `Algebra.geometric_field_stalk_descent`. Its only theorem has
proof `by sorry`. No definitions, auxiliary statements, new nodes, dependency repairs,
or statement corrections are needed. No statement dispute was found.

Hypothesis and clause correspondence:

- The field k is `(k : Type u) [Field k]`.
- The algebraic closure Ω is `(Ω : Type v) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. It is an arbitrary algebraic closure, not only the concrete
  `AlgebraicClosure k` construction.
- The finitely generated k-algebra is `(T : Type w) [CommRing T] [Algebra k T]
  [Algebra.FiniteType k T]`.
- The maximal ideal is `(p : Ideal T) [p.IsMaximal]`.
- F is the literal quotient `T ⧸ p`. Finiteness of F/k is
  `Module.Finite k (T ⧸ p)`. Since k is a field, this is finite dimensionality;
  since p is maximal, the quotient is a field. No finite-dimensionality hypothesis
  or separability hypothesis is imposed on F.
- S is the literal algebra tensor product `T ⊗[k] Ω`, with its standard ring
  multiplication. The map T → S is `algebraMap T (T ⊗[k] Ω)`, namely t ↦ t ⊗ 1.
- Existence of a prime over p is the second conjunct, `∃ q : PrimeSpectrum S,
  q.asIdeal.comap (algebraMap T S) = p`. A `PrimeSpectrum` object carries primality.
- The third conjunct quantifies over EVERY such prime q and concludes
  `q.asIdeal.IsMaximal` and bijectivity of the composite
  `(algebraMap S q.asIdeal.ResidueField).comp
  (Algebra.TensorProduct.includeRight : Ω →ₐ[k] S).toRingHom`.
  The second factor is a ↦ 1 ⊗ a, so this is precisely the STRUCTURAL map
  Ω → κ(q). Its bijectivity is equivalent to an Ω-algebra identification with Ω:
  the inverse of a bijective structural ring map preserves Ω-scalars automatically.
  This does not merely assert an unspecified abstract ring isomorphism.
- The antecedent of the fourth conjunct is existence of ONE such q for which the
  corresponding structural map Ω → `Localization.AtPrime q.asIdeal` is bijective.
  This is exactly that local ring being Ω as an Ω-algebra. It is not required for
  all primes, and no arbitrary algebra structure or choice of map is introduced.
- Its first conclusion is `Function.Bijective` of the composite from `T_p` to `T/p`:
  `(IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)).symm`
  after `IsLocalRing.residue (Localization.AtPrime p)`. The latter is the canonical
  quotient by the maximal ideal; the former is Mathlib's canonical identification
  of that quotient with `T/p`. In particular the map sends t/s to t̄/s̄. This is
  equality with F via the residue map, rather than existence of some unrelated iso.
- Its second conclusion is `Algebra.IsSeparable k (T ⧸ p)`, the recorded notion of
  separable algebraic extension. The unconditional first conjunct supplies its
  finiteness. The conclusion therefore says finite separable, exactly as required.
- The localization and residue-field objects are Mathlib's recorded
  `Localization.AtPrime` and `Ideal.ResidueField`, with no private copies.

The universes u, v, w are explicitly bound and independent. There is no restriction
on characteristic, no perfection assumption, and no constraint on relative sizes.
No local notation, local instance, let binder, hidden structure hypothesis, or new
canonical-map construction occurs in the signature.

Dependency declarations read and used:

- `def-weil-algebraic-closure`: `IsAlgClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (imported via
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`), with fields `isAlgClosed`
  and `isAlgebraic`; also read the concrete `AlgebraicClosure` interface.
- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType` in
  `Mathlib.RingTheory.FiniteType`, finite generation of the top subalgebra.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`; its docstring explicitly includes algebraicity.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` and `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`; the latter imports the former.
  Also read `IsLocalization.AtPrime.equivQuotMaximalIdeal` and its computation on
  quotient representatives in AtPrime.Basic:558–592. Its inverse composed with
  residue is exactly the residue map needed here.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; the ring/algebra structure and the
  structural inclusions are supplied by `Mathlib.RingTheory.TensorProduct.Basic`.
  Read `includeLeftRingHom`, `includeLeft`, `includeRight`, and `rightAlgebra`.
  Explicit use of `includeRight` avoids introducing a file-local Ω-algebra instance.

Proof-only imports follow the recorded proof dependencies: Jacobson.Ring (Zariski
lemma), Flat.FaithfullyFlat.Algebra (faithful flatness, spectrum surjectivity, ideal
contraction), FiniteDimensional.Basic (finite-dimensional domain is field),
Polynomial.Splits (linear factorization), Flat.Localization (localization flatness
and flatness over a localization), RingHom.Flat (composition), and
`Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced`.
The last module's complete signature/docstring were read from both the checkout and
`scompile.py --source`: it concludes `Algebra.IsSeparableExtension`, and the docstring
of the present theorem records the finite/algebraic passage to `Algebra.IsSeparable`.
The recorded `WeilConjectures.FieldTheory.SeparableExtension` source was read with
`scompile.py --source`; it gives the general separability definition. The existing
criterion imports its library-side defining module `Sheaf.FieldTheory.SeparableExtension`,
so the upstream module is not separately imported, avoiding duplicate definitions.
`lem-trf-geometric-reducedness-local-base-change` has no Lean declaration yet; its
proof-only module therefore cannot be imported and is left for the maintainer to
connect when it lands. It is not a statement prerequisite and no replacement is made.

Sources checked: Stacks varieties.tex, geometric reducedness at a point (Tag 035W)
and upstairs (Tag 0384), including the flat local descent argument; curves.tex:4220ff
(Tag 0C4D, arbitrary-field paragraph); algebra.tex, finite-type field lemma (Tag 00FY)
and separability/geometric reducedness (Tag 030W). These agree with the eight-step
proof supplied in the theorem docstring. Nothing in the source requires a perfect
base field or separability before the conditional conclusion.

Edge cases checked:

- T = 0: there is no maximal ideal, so the statement has no unintended existence
  claim for the empty spectrum.
- T = k and p = 0: S = Ω; the prime is zero and all conclusions give the identity
  field extension and residue map.
- A finite separable extension T/k, p = 0: S is a product of copies of Ω, and every
  prime gives the claimed geometric field stalk. The conclusion is T itself.
- A nontrivial purely inseparable finite extension in positive characteristic:
  the quotient over each geometric prime is still Ω, but the geometric local ring
  has nilpotents and the conditional antecedent is false. Thus the statement does
  not accidentally assert separability from the residue-field clause alone.
- T = k[x], p = (x): the residue-field clause holds while the geometric local ring
  is not Ω, so the field-stalk antecedent is a genuine condition.
- T = k[ε]/(ε²), p = (ε): again the geometric local ring is nonreduced, so the
  field-stalk antecedent does not collapse to the automatic residue-field clause.
- Ω in another universe, positive characteristic, and an imperfect k all remain
  admitted. Prime q is arbitrary, not a selected or unique prime.

Searches (all executed for this item through the prescribed tools):

- `msearch.py ... leanfinder "A finite type algebra over a field with a local ring
  over its algebraic closure isomorphic to that closure descends to a finite
  separable field local ring"`: 8 hits, led by
  `Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing` and its
  bijectivity counterpart. They assume formal unramifiedness, and do not state
  descent from a geometric field stalk or the combined clauses of this node.
- `msearch.py ... loogle "Algebra.IsSeparable, Localization.AtPrime"`: 9 hits,
  residue-field separability transfer and unramified criteria; none says this node.
- `msearch.py ... grep "geometric.*field.*stalk|field.*stalk.*descent|separable.*localization"
  RingTheory`: 4 hits, all unrelated Dedekind-domain fraction-field localization
  results, no match.
- `msearch.py ... leansearch "A field stalk after base change to an algebraic closure
  descends to a finite separable field stalk"`: 8 hits on separable closures,
  algebraic-geometry residue fields, and surjective-on-stalks stability; no match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `geometric.field|GeometricField|stalk.desc|stalk descent|Algebra.IsSeparable|IsAlgClosure|Algebra.FiniteType`:
  algebraic-closure binders, generic finite-type arguments, and unrelated geometric
  field pro-étale evaluation; no exact statement.
- `rg` in Mathlib, upstream and `lean/Sheaf` for
  `geometric_field_stalk_descent`: no existing declaration with this name.
- `rg` in upstream and `dag/lean_names_upstream.json` for the exact item id:
  no recorded upstream implementation.
- Read all five statement-dependency nodes including `lean`/`mathlib_match`, and
  all proof-dependency records to select the existing proof-plan imports.

Validation: scompile.py compiled both the sandbox and library forms successfully.
The initial compilation reported only one long-line style warning; after wrapping
the signature to 100 columns, deliver2.py --no-push returned OK: preflight passed
and both compile forms were clean (dry-run commit a4ea61872b). No proof was
attempted. The maintainer's independent delivery review is the external reading,
as specified in the worker brief; no second worker was started.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
