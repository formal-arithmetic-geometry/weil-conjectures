## Worker report

The module `Sheaf.RingTheory.HenselianValuationEtaleLocalFactors` states
`AlgebraicGeometry.henselian_valuation_etale_local_factors`, with its only proof `sorry`.
No definition, helper theorem, new node, dependency repair or statement correction is needed.
The source node is unchanged except for `lean`. The declaration docstring follows all nine
proof steps, naming their DAG dependencies and giving the elementary calculations.

Hypotheses and objects, checked against the node:

- A henselian valuation domain is `[CommRing R] [IsDomain R] [ValuationRing R]
  [HenselianLocalRing R]`. The domain instance is required to form Mathlib's valuation-ring
  class. Henselian locality supplies `IsLocalRing R`; the maximal ideal is
  `IsLocalRing.maximalIdeal R` and `k` is `IsLocalRing.ResidueField R`.
- `D` is `[CommRing D] [Algebra R D]`. The hypothesis is exactly the node's affine scheme
  etaleness, `[Etale (Spec.map (CommRingCat.ofHom (algebraMap R D)))]`, using the recorded
  `AlgebraicGeometry.Etale` definition, without replacing it by an extra assumption.
- The prime is `(n : Ideal D) [n.IsPrime]`. Its contraction is exactly the named maximal
  ideal: `hn : n.comap (algebraMap R D) = IsLocalRing.maximalIdeal R`.
- `S` is any localization model, `[Algebra D S] [IsLocalization.AtPrime S n]`.
  `[Algebra R S] [IsScalarTower R D S]` specifies the composite scalar action. This is
  precisely `S = D_n`, expressed using Mathlib's localization predicate instead of
  introducing a second construction. In particular it specializes to `Localization.AtPrime n`.
  Locality of `S` is inferred from this predicate, not assumed as a new restriction.
  Its universe `v` is independent of the common universe `u` of the affine rings `R, D`.
- `K` and `L` are Mathlib's concrete `FractionRing R` and `FractionRing S`. The conclusion
  first supplies `IsDomain S`, then `ValuationRing S`, and a local ring-map instance.
  It also supplies an `Algebra K L` structure and `IsScalarTower R K L`. This is the
  extension of the specified map `R → S → L`; the fraction-field universal property
  uniquely determines that map from the tower equation. There is no arbitrary embedding
  assumption, chosen unknown object, or definition made from a postponed existence proof.
  A ring map between these fields is injective; thus this also fixes the intended inclusion.
- `l` is `IsLocalRing.ResidueField S`, definitionally `S / maximalIdeal S`.
  Its `k`-algebra structure is Mathlib's canonical instance induced by the concluded local
  map. Together with the asserted maximal-ideal equality this is the node's `S / mS`.

Conclusions, in the order of the Lean conjunction:

- Direct factor: `∃ (T : CommAlgCat R) (e : D ≃ₐ[R] S × T),
  ∀ d, (e d).1 = algebraMap D S d`. Thus the projection agrees with the canonical
  localization map, not merely an unspecified isomorphism to a product. `T` may be zero.
- Finite etale: `Module.Finite R S ∧ Algebra.Etale R S`. Ring-map etaleness is equivalent
  to affine scheme etaleness by the recorded Mathlib comparison.
- Valuation domain: the existential `IsDomain S` and `ValuationRing S` above the conjunction.
- Finite separable fraction extension: `Module.Finite K L ∧ Algebra.IsSeparable K L`.
- Integral closure: `(integralClosure R L).toSubring = (algebraMap S L).range`.
  This uses the recorded `integralClosure`, with no substitute definition.
- Extending the original valuation: the comap along `algebraMap K L` of the image subring
  of `S` equals `(algebraMap R K).range`. This spells out `S ∩ K = R`.
- Uniqueness: for every `W : ValuationSubring L` with exactly that same comap, the theorem
  concludes `W.toSubring = (algebraMap S L).range`. This quantifies over every valuation
  ring of `L` extending `R`, without a height or discreteness restriction.
- Maximal ideal: `IsLocalRing.maximalIdeal S =
  (IsLocalRing.maximalIdeal R).map (algebraMap R S)`.
- Finite separable residue extension: `Module.Finite k l ∧ Algebra.IsSeparable k l`.
- Free of the asserted rank: `Module.Free R S`, `Module.finrank R S = Module.finrank K L`,
  and `Module.finrank K L = Module.finrank k l`. Module-finiteness was already asserted.
- Every residue generator: `∀ y : S, IntermediateField.adjoin k {residue S y} = ⊤ → ...`.
  There is no particular chosen generator or extra condition on its lift.
- Ring and field generation: `Algebra.adjoin R {y} = ⊤` and
  `IntermediateField.adjoin K {algebraMap S L y} = ⊤`, respectively `S = R[y]` and `L = K(y)`.
- Coefficients and monicity: `∃ g : Polynomial R, g.Monic ∧
  g.map (algebraMap R K) = minpoly K (algebraMap S L y) ∧ ...`.
  Thus the actual minimal polynomial over `K` has coefficients in `R`.
- Degree: `g.natDegree = Module.finrank k l`. Since `g` is monic and `R → K` is injective,
  this is also the degree of the displayed minimal polynomial over `K`.
- Reduction: `g.map (IsLocalRing.residue R) = minpoly k (IsLocalRing.residue S y)`.
- Unit derivative: `IsUnit (Polynomial.aeval y g.derivative)`. This evaluates the
  coefficient lift in `S`, exactly the meaning of the node's derivative-unit assertion.

Dependency declarations read and reused:

- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`,
  `Mathlib.RingTheory.Valuation.ValuationRing`; total divisibility equals the
  fraction-field element-or-inverse condition.
- `def-weil-pbc-henselian-terminology`: `HenselianLocalRing` from
  `Mathlib.RingTheory.Henselian`, publicly imported through the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian`. Its recorded accompanying strict
  henselian class is not imposed here. The node record lists all three declarations.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, used on both fraction and residue
  fields through Mathlib's existing instances.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` and `minpoly`,
  `Mathlib.FieldTheory.Separable` and `Mathlib.FieldTheory.Minpoly.Basic`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `def-weil-pbc-localization-at-prime`: `IsLocalization.AtPrime` and `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; the first is the existing predicate
  characterizing any model of the second. Residue fields use
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`.
- `def-weil-pbc-free-module`: `Module.Free`, `Mathlib.LinearAlgebra.FreeModule.Basic`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-simple-field-extension`: `IntermediateField.adjoin`,
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, imported via `.Adjoin.Basic`.

The recorded proof interfaces are imported with ordinary `import`:
`HenselianLocalRing.finiteType_exists_algEquiv_pi_prod` in
`Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`,
`Algebra.valuation_finite_type_module_presentation` in
`Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation`, and
`isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse` in
`Sheaf.RingTheory.ValuationRingNormal`. The recorded quasi-finiteness definition is
available through the first of these modules. Mathlib proof imports cover etale finite
presentation/base change and field products, quotient base change, smooth flatness,
flat torsion-free modules, local freeness and Nakayama, and Cayley--Hamilton.
`lem-trf-etale-localization-valuation-domain` has no Lean record or Mathlib match at the
read base. It is a proof dependency only: the statement requires no missing notion,
so no declaration for that independent lemma is introduced into this delivery.
The supplied brief requires importing proof dependencies that are already stated.
The residue power basis and separable-polynomial definitions are publicly available
through the statement imports.

Edge cases checked before writing:

- `R` a field: its maximal ideal is zero; the finite local factor is a finite separable
  field. The residue and fraction degrees agree, including degree one.
- `D = 0`, or no prime above the closed point: no admissible `n` exists, so the assertion
  has no case to prove. No nonempty closed fibre was added as a hypothesis.
- `D = R`, `n = maximalIdeal R`: the complement factor may be zero, the rank is one,
  and every `y` has a monic linear minimal polynomial with derivative one.
- `y = 0` is allowed whenever it generates the residue field (degree one); the polynomial
  is `X`, the reduction is `X`, and its derivative is a unit. No nonzero-generator
  assumption is present.
- Positive residue characteristic, nondiscrete valuations, arbitrary valuation height,
  and non-Noetherian henselian valuation domains are all allowed. Neither a DVR nor
  Noetherian hypothesis appears.
- `S` can be the actual quotient-type localization or an isomorphic localization in
  another universe. All conclusion instances are existentially supplied, not assumed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "An etale algebra over a henselian valuation domain localized
  at a prime above the maximal ideal is finite etale and generated by any lift of a residue
  field generator"`: 8 results, including `Algebra.exists_etale_of_isEtaleAt`,
  `Algebra.IsEtaleAt` and standard-etale constructions; no match to this statement.
- `msearch.py ... loogle "ValuationRing, HenselianLocalRing, Algebra.Etale"`: 0 hits.
- `msearch.py ... leansearch "local etale algebra over henselian valuation ring finite free
  generated by residue field generator"`: 8 results on etale finite presentation and
  formal etaleness; no match.
- `msearch.py ... grep "henselian.*valuation|valuation.*etale" RingTheory`: 0 hits.
- `rg` in the project and upstream source for henselian/valuation and etale/local-factor
  patterns, plus the exact item id in `WeilConjectures`, `Sheaf` and the upstream names
  index: no statement matching this item. The upstream `HenselianDVRExtension` requires
  a discrete valuation ring and algebraically closed residue field, and is different.
  `EtaleIdealLocalFactor` concerns ideal factorization, and `ValuationValueGroupTorsion`
  concerns the value group, so neither duplicates this statement.
- Source definitions and full signatures/docstrings were read from the pinned local
  Mathlib and the recorded source modules. Stacks 04GH, 04GJ and 04GK were read in
  `literature/stacks-project/algebra.tex`; their finite local-factor argument matches
  the node. No statement dispute or mathematical node fault was found.

Validation: the initial complete statement compiled through the prescribed `scompile.py`
server wrapper without errors or unexpected warnings. Explicit public imports were then
added for the recorded Mathlib statement-dependency modules; final compilation and
preflight are performed by the required dry-run/delivery wrappers. `autoImplicit` is false.
No proofs were supplied, no local notation or private construction was introduced, and no
live repository file or launcher script was edited.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
