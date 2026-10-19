## Worker report

The module `Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension` states
`AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField`, with one `sorry` proof.
It introduces no definition and changes only the item's `lean` field. The declaration
docstring gives all eight proof steps, including the finite-orbit argument, cofinal
coordinate kernels and the corrected inflation between different norm complexes.

The statement agrees with the current main-20261015 blueprint unit and the node:

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| The prime ℓ fixed in `sk-def-cd` | `(ℓ : ℕ) (hℓ : Nat.Prime ℓ)` |
| A field K | `(K : Type u) [Field K]`, with explicit arbitrary universe `u` |
| If K is algebraically closed | First conjunct, hypothesis `IsAlgClosed K →` |
| Its ℓ-cohomological dimension is zero | `cohomologicalDimension ℓ hℓ (Spec (.of K)) = 0` |
| If K is finite | Second conjunct, hypothesis `Finite K →` |
| Its ℓ-cohomological dimension is at most one | `cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ 1` |
| Both assertions | The conjunction of the two implications, for the same arbitrary K |

The field notation is exactly `cd_ℓ(K) = cd_ℓ(Spec K)` from the dependency. The
qcqs structure of `Spec K` is inferred from its affine structure; it is not an
extra assumption. Neither a chosen separable closure nor a chosen algebraic closure
is required as input. Finiteness is `Finite K`, without requiring a particular
enumeration. There is no invertibility or unequal-characteristic hypothesis.

Statement dependency used: `sk-def-cd`, module
`Sheaf.AlgebraicGeometry.CohomologicalDimension`, declaration
`AlgebraicGeometry.ProEtale.cohomologicalDimension`. The local shared snapshot had
no Lean record yet. A read of the published server DAG found the Q110 record dated
2026-10-17, and `scompile.py --source Sheaf.AlgebraicGeometry.CohomologicalDimension`
returned the current source. Its full signature is
`noncomputable def cohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (X : Scheme.{u})
[CompactSpace X] [QuasiSeparatedSpace X] : WithTop ℕ`.
I read its docstring and implementation: it is the supremum of natural degrees with
nonzero derived global-sections cohomology of classical locally ℓ-power torsion
abelian pro-étale sheaves. `IsEllPowerTorsion` uses the canonical colimit map of
the annihilator kernels, not a uniform annihilator. `IsClassicalAbelian` uses the
recorded underlying-set classicality predicate. The empty supremum is zero.
The already published dependency is used directly; no replacement module is needed.

The already stated proof dependencies are imported without `public`:

- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`:
  `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules`.
- `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`:
  `AlgebraicGeometry.Scheme.fieldSections_stalkInvariants`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`.
- `Sheaf.RepresentationTheory.BaseFieldContinuousCochains`:
  `Rep.exists_baseFieldContinuousCochains_universal`,
  `Rep.baseFieldContinuousCochains_directedUnion`, and
  `Rep.baseFieldContinuousCochains_finiteQuotients`.
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`.
- `Sheaf.FieldTheory.FiniteFieldAbsoluteGalois`:
  `finiteField_absoluteGaloisGroup`.
- `Sheaf.GroupTheory.CyclicInflation`: `groupCohomology.inflation_periodic`.

`det-cd-etale-comparison` has no Lean record in either the local snapshot or the
published server DAG when checked. It is a proof-only dependency, so its import is
left for the maintainer when it is stated, as prescribed by stage 2, rule 7.
The current dimension module already contains the absolute and relative equality
with the étale supremum. No additional statement dependency is missing.

Edge cases checked before writing:

- The case ℓ = char K is included in both clauses, including finite fields of
  characteristic ℓ; the proof uses torsion Galois cohomology with no inverted prime.
- Degree zero is retained in the supremum. The nonzero trivial module `ZMod ℓ`
  has nonzero invariants, including in characteristic ℓ. Positive-degree vanishing
  gives equality zero for algebraically closed fields in the dependency's
  `WithTop ℕ` convention.
- Finite fields are nontrivial by `Field`; there is no zero-ring or one-element
  field case inadvertently admitted. Arbitrary field universes are allowed.
- The zero coefficient module is allowed: choose exponent one in the finite-module
  argument. General torsion modules have no common exponent; the directed union
  reduction handles them elementwise. No finite coefficient-ring restriction enters.
- No empty-spectrum hypothesis is necessary: spectra of fields are nonempty. The
  imported invariant nevertheless retains its specified empty-supremum convention.

Searches for an existing statement:

- `msearch.py`, LeanFinder query: "The ell cohomological dimension of an algebraically
  closed field is zero and of a finite field is at most one". Eight hits concerned
  ring Krull dimension, model-theoretic algebraically closed fields and finite field
  extensions; none stated either cohomological-dimension clause.
- `msearch.py`, Loogle query: `groupCohomology, IsAlgClosed`. Zero hits.
- `msearch.py`, Mathlib grep query:
  `cohomologicalDimension|cohomological_dimension|finiteField.*cohom|cohom.*finiteField`.
  Zero hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for
  `cohomologicalDimension|ellCohomological|ℓ.*dimension|fieldCohomological` and related
  dimension names found other invariants and the continuous-cochain infrastructure,
  but no exact statement. The published `sk-def-cd` source was then read as above.
- `grep -rn sk-lem-base-field-cd` in upstream `WeilConjectures` had no hits.
  Project occurrences are source references in the cyclic-inflation, finite-Galois
  and continuous-cochain modules, not a statement of this node.
- Exact-name `rg` for `cohomologicalDimension_baseField` in Mathlib, upstream and
  `lean/Sheaf` had no hits. The published server item also had no Lean record.

Validation: `scompile.py NX sk-lem-base-field-cd` compiled the delivered module
cleanly, including an overlay compilation of the published dimension dependency.
Every variable and universe is explicit (`set_option autoImplicit false`).
There are no new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by NX

I independently opened the item node, its main-20261015 blueprint statement and
both proof texts, the `sk-def-cd` node and its actual
`Sheaf.AlgebraicGeometry.CohomologicalDimension` source, and the delivered module.
The source statement has exactly two clauses. Its object/hypothesis/conclusion
checklist, including conventions inherited from the definition, is:

| Source object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| A fixed prime ℓ, inherited from `sk-def-cd` | `(ℓ : ℕ) (hℓ : Nat.Prime ℓ)`: exact. |
| An arbitrary field K | `(K : Type u) [Field K]`, with explicit `universe u`: exact. |
| Field dimension means dimension of its spectrum | Both clauses use `cohomologicalDimension ℓ hℓ (Spec (.of K))`: exact field notation, using the recorded dependency. |
| Algebraically closed hypothesis for the first clause | `IsAlgClosed K →` in the first conjunct: exact; it is not imposed on the finite-field clause. |
| First conclusion is equality with zero | `cohomologicalDimension ℓ hℓ (Spec (.of K)) = 0`: exact equality. |
| Finite-field hypothesis for the second clause | `Finite K →` in the second conjunct: exact finiteness, without choosing an enumeration. |
| Second conclusion is an upper bound of one | `cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ 1`: exact bound. |
| Both assertions for all fields and the same prime | The conjunction of the two implications follows the common field and prime binders: exact. |
| No characteristic exclusion or coefficient restriction | No invertibility, characteristic inequality, finite coefficient ring, uniform exponent, or extra field instance is assumed: exact. |

The dimension dependency is the correct invariant, not just a similarly named
dimension: its `sSup` is in `WithTop ℕ`, over all natural degrees, and its witnesses
are abelian pro-étale sheaves valued in `AddCommGrpCat.{u+1}` satisfying
`IsClassicalAbelian`, `IsEllPowerTorsion`, and `IsNonzeroProEtaleCohomology`.
I read these definitions: classicality is the recorded underlying-set predicate;
prime-power torsion is `IsIso` of the canonical map from the colimit of the actual
kernels of `(ℓ^r) • 𝟙 F`; nonvanishing uses derived global sections on the sheaf
in degree zero. Thus there is no private definition or uniform annihilator.
Its `CompactSpace` and `QuasiSeparatedSpace` inputs are inferred for the affine
spectrum; they add no hypothesis on K. The degree-zero convention and empty
supremum agree with the dependency node.

I read the source places in `etale-cohomology.tex`: Tag 03QQ is the section
"Cohomology of a point"; 04JQ gives the equivalence for all abelian sheaves on a
field spectrum, 04JM gives sections as invariants, and 03QU gives derived sections
and cohomology as Galois cohomology. These do not impose a characteristic
restriction. In `homology.tex`, Tag 010T is the effaceability criterion for
universal delta-functors on abelian categories; it contributes no restriction on
the field. The blueprint finite-field proof supplies the cyclic quotient and
inflation arguments rather than attributing the finite-field bound to 010T itself.

I also opened the actual signatures and docstrings of the imported proof
dependencies: `Scheme.abelianSheaves_equiv_discreteGModules`,
`Scheme.fieldSections_stalkInvariants`, `Etale.rightDerivedGlobalSections`,
`Etale.cohomology`, the three `Rep.baseFieldContinuousCochains` theorem clauses,
`Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`,
`finiteField_absoluteGaloisGroup`, and `groupCohomology.inflation_periodic`.
Their closure choices and equivalent presentations are proof inputs that can be
chosen, not assumptions smuggled into this theorem. The dimension coefficient
universe `u+1` is covered by the stalk equivalence's `max (u+1) v`; there is no
extra universe equality. The finite Galois theorem's `Fintype K` can be chosen
from `Finite K`. The inflation theorem includes the needed final vanishing
clause and distinguishes the two norm complexes. The only unrecorded proof-only
dependency is `det-cd-etale-comparison`, already listed in the worker report;
the dimension module itself supplies the absolute étale-supremum equality.

Edge cases: ℓ equal to the characteristic is included, as are all other primes;
ℓ = 0 and ℓ = 1 are correctly excluded by primality. Degree zero is included,
and the trivial nonzero `ZMod ℓ` is available in every characteristic. Zero
coefficient sheaves cause no nonvanishing witness and remain allowed. The empty
scheme and zero ring are not field cases, since `Field` requires nontriviality.
There is no external index set in the statement; the proof's finite stable
subgroups include zero, ensuring a nonempty directed family. Arbitrary `u` is
retained and no closure, cardinality, or chosen finite-field model is a binder.

Independent searches (2026-10-17):

- `msearch.py ... leansearch` with "The cohomological dimension of a finite field
  is at most one, and an algebraically closed field has cohomological dimension
  zero": eight hits, including Krull dimension, Hilbert 90, and basic field
  results; no match.
- `msearch.py ... leanfinder` with "Galois cohomological dimension finite field
  algebraically closed field higher torsion cohomology vanishes": eight hits,
  including Hilbert 90 and cyclic finite Galois groups; no match.
- `msearch.py ... loogle` with `IsAlgClosed, groupCohomology`: zero hits.
  An initial `IsAlgClosed, IsZero` query reported an unknown short identifier;
  I replaced it with the valid query above and did not count it as evidence.
- `msearch.py ... grep` with
  `(finite|closed|procyclic).*[Cc]ohom|[Cc]ohom.*(finite|closed|procyclic)`:
  fourteen Mathlib hits, concerning finite cyclic cohomology, Hilbert 90, Tate
  cohomology and spectral sequences; no match.
- Independent `rg` in Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` for dimension declaration names and finite/closed-field cohomology
  found no exact theorem. I opened the closest project result,
  `torsionEtaleCohomologicalDimension_eq_zero_of_isSepClosed`: it states the
  all-torsion étale invariant and only the separably closed clause, so does not
  duplicate this two-clause prime-specific statement. Upstream
  `HasUniformCohomologicalDimensionLE` instead bounds a relative direct image
  uniformly after base change; its actual definition is also not this invariant.

No mismatch was found. I retained the Lean module and node record verbatim and
added this independent reading only. There are no new definition nodes,
dependency modules, or statement corrections to audit. The module has one named
theorem with `sorry`, no definitions, source/blueprint module and declaration
docstrings, and all eight proof steps. `autoImplicit false` and explicit `u`
leave no unbound variables. I checked that `lean.statement` equals the source
signature verbatim and that only the item's `lean` field differs from the base.
The required `scompile.py NX sk-lem-base-field-cd` invocation compiled the
delivered file cleanly (library pass 2.4 seconds), without errors or unexpected
warnings.
