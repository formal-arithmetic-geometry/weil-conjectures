## Worker report

This repairs the H3/H4 return at immutable head `60bb633390b3`. The retained packet
already contains the substantive repair, and its first dry run on this retry passed:
`OK (dry run): commit 2813c6e8ad passes the preflight and compiles; nothing pushed`.
The Lean sources are retained. This report replaces stale descriptions of the
returned self-defined power-square operator with the actual delivered statement.

`Sheaf.Paper.WeilConstantExtensionFrobenius` states
`WeilConjectures.weil_constant_extension_frobenius`. Its proof is `sorry` and its
docstring gives the complete finite-field, transport, local-stalk and purity proof.
`Sheaf.Paper.ConstantExtensionCompactComparison` defines the canonical comparison;
its definitions contain real constructions and no sorry data. The only postponed
theorem in the delivered files is `weil_constant_extension_frobenius`.

Source read: blueprint main-20261015,
`sec-deligne-laumon-general/sk-p-dl-general-relative-line/lem-zl-affine-curve-hc2-purity.proof.md`,
second paragraph. It uses local residue-degree powers, preservation of punctual
purity under constant extension, and the compact-cohomology operator F^e.

Each hypothesis and clause is rendered as follows:

- `D : FiniteFieldDatum.{u}` fixes the finite base field and its chosen closure,
  including p, a, q=p^a and the closure embedding.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` give the distinct coefficient prime.
  `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`
  give its algebraic closure; `iota : Ω ≃+* ℂ` is the specified isomorphism.
  The scheme and coefficient universes u and v are independent.
- `X₀ : Over (Spec (.of D.k₀))` is the model. `LocallyOfFiniteType X₀.hom`
  and `QuasiCompact X₀.hom` together say finite type, and `IsSeparated X₀.hom`
  says separated. Its geometric fibre is `D.geometricFiber X₀`.
- `e : ℕ`, `he : 1 ≤ e` quantify over exactly the positive extension degrees.
  `constantExtensionDatum D e he` uses the actual subfield of D.k of size q^e;
  `constantExtensionModel D e he X₀` is the actual base change to that field.
- The first conjunct intertwines extended geometric Frobenius and
  `localPositivePower (D.geometricFrobenius X₀).hom (e - 1)` through
  `constantExtensionFiberIso`. This positive-power convention has exponent e.
- The existential `R` is a functor between the actual common-stage Weil hearts.
  `hR : ConstantExtensionRestrictionSpec ... R` specifies its carrier isomorphism
  with canonical fibre pullback and its return equation with theta^[e]. This
  records the iterated Weil structure and its action on morphisms.
- `F : sfCommonStageWeilSheaf ...` is any constructible Weil heart object.
  `HasCommonStageLisseLattice ... F.obj.carrier` is exactly its lissity criterion;
  the first conclusion gives that criterion for `(R.obj F).obj.carrier`. No stable
  lattice, constant rank, geometric connectedness or semisimplicity is imposed.
- For each retained compactification `c`, the theorem asserts existence of a
  `ConstantExtensionCompactComparison ... c`. This is a conclusion, not an added
  hypothesis. Its arrow is fixed at each finite integral representative by actual
  proper/open adjunction mates, reduction and total inverse limit, then rational
  localization, the specified point fibre and coefficient extension to Ω.
  Its normalization has no Frobenius equation and no free comparison-map choice.
- For every `r : ℤ`, the cohomology clause uses the published
  `globalGeometricFrobeniusQbarOnCohomology` on BOTH sides. The extended operator
  takes `constantExtensionDatum`, `constantExtensionModel`, the actual base-changed
  compactification and `(R.obj F).obj`, with `compact = true`. The original
  operator takes `D`, `X₀`, `c`, and `F.obj`, also with `compact = true`, and is
  raised to e. The equation is `I.hom ≫ F_extended = F_original^e ≫ I.hom`.
  Here `I = constantExtensionCompactCohomologyComparison ... C R hR F r` is H^r
  of the canonical fibre comparison followed by the compact-cohomology functor
  applied to the inverse carrier isomorphism retained in hR. Thus the two actual
  coefficient modules are compared by the prescribed identification. There is
  no self-defined substitute Frobenius operator in the delivered module.
- For every closed z of the extended model, `constantExtensionClosedImage ... z`
  is its actual closed image x; `constantExtensionResidueDegree ... z.val`
  computes the finrank of its induced residue-field extension.
  `ConstantExtensionLocalConjugacy` says that all finite Weil presentations and
  compatible residue embeddings yield Ω-stalk operators conjugate by an Ω-linear
  isomorphism, with the operator at z equal to the indicated power at x.
- `∀ w : ℝ, SfIsPunctuallyPureOfWeight ... iota F w → ... (R.obj F) w`
  is preservation of every real punctual weight, using residue cardinalities
  relative to the appropriate model.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber` and
  `extensionSubfield`; `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilStageObject`, `sfWeilPrimeInvertible`;
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the common-stage category.
- `Sheaf.Paper.CommonStageLisse`: `HasCommonStageLisseLattice`, the completed
  integral-lattice realization of the lisse-adic convention.
- `Sheaf.Paper.GlobalGeometricFrobenius`: `globalGeometricFrobeniusQbar`,
  `globalGeometricFrobeniusQbarOnCohomology`,
  `globalGeometricFrobeniusQbarCohomology`; its recorded compact-cohomology functor
  is `frobeniusCohomologyQbarFunctor` from
  `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: `constantExtensionDatum`,
  `constantExtensionModel`, `constantExtensionFiberIso`, owned by the landed
  `def-dl-a1-constant-extension-data`; and `constantExtensionWeilIterate`,
  `constantExtensionFiberPull`, `constantExtensionRestrictionComparison`,
  `ConstantExtensionRestrictionSpec`, `ConstantExtensionLocalConjugacy`,
  `constantExtensionClosedImage`, `constantExtensionResidueDegree`, owned by the
  new existing-declaration definition node below. The theorem node
  `lem-zl-constant-extension-weil-heart-equivalence` is not a statement dependency.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower` and the local stalk
  operator convention; `Sheaf.Paper.AdicPunctualWeights`:
  `SfIsPunctuallyPureOfWeight`. Mathlib supplies `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `closedPoints` and residue fields.
- The comparison module uses the published system pullback compositors,
  `systemDerivedOpenAdjunction`, `systemAdjunction`, `integralComparisonPullbackCounit`,
  `compactRealization`, `sfCompactSupportFiniteIntegralFunctor`,
  `sfRationalConstructibleLocalization`, `pointRationalFibre` and
  `frobeniusCohomologyCoefficientExtension`, without private replacements.
- Proof imports retain the transport-composition, transport-power, iterated-cocycle,
  local-conjugacy and finite residue-field statements. The returned review's PASS
  for `LocalFrobeniusTransport.positivePower_eq` is preserved; the replacement
  cohomology clause now directly uses the recorded Qbar operators.

Edge cases checked: e=1 gives positive index zero and exponent one, whereas e=0
is excluded. Zero sheaves, zero and varying finite local ranks, empty schemes,
empty closed-point sets, disconnected schemes, Jordan blocks, every integer
cohomology degree and every real weight remain included. Compactifications are
presentations of compact support, not properness hypotheses on X₀. The comparison
acts on `ModuleCat.{max u v} Ω`, with no equality imposed on u and v.

Searches retained in `searches.jsonl` and the node records: LeanFinder queried
constant extension of a lisse Weil sheaf, compact Frobenius powers and residue
powers (eight unrelated arithmetic-Frobenius/isocrystal hits); Loogle queried
`WeilSheaf, Frobenius` (unknown identifier and zero hits); Mathlib grep queried
`WeilSheaf|constantExtension.*Frobenius` (zero hits); LeanSearch queried finite
constant extension and compact cohomology powers (finite-field Frobenius and
isocrystal hits only). Project searches found the existing constant-extension
field/model, restriction and local interfaces, but no matching compact comparison
or theorem. DAG and blueprint-reference searches found no definition owner for
the restriction/local helpers and no existing compact-comparison node.

The item differs from the current shared node only in `lean` and by adding four
statement dependencies: `def-dl-a1-constant-extension-data`,
`def-zl-constant-extension-restriction-local-data`,
`def-zl-constant-extension-compact-comparison` and
`def-a1-common-stage-lisse-lattice`. No mathematical statement correction or
STATEMENT-DISPUTED issue is needed.

## New nodes

`def-zl-constant-extension-restriction-local-data` owns the seven existing helpers
listed above, including all four named by the return. It records `existing: true`
on `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`, copying no declaration.
It defines the normalized restriction specification, closed image and residue
degree, and local conjugacy predicate. Its source is the cited blueprint paragraph.
The retained LeanSearch, Loogle and Mathlib/project/DAG grep searches found those
landed definitions but no owning definition node. It cites
`def-dl-a1-constant-extension-data` for the actual field/model/fibre constructions.

`def-zl-constant-extension-compact-comparison` owns the canonical integral
proper/open comparison, its prescribed coefficient realization, the normalized
natural-isomorphism package and its restriction-induced cohomology comparison.
Its source is the same blueprint paragraph and the recorded exchange and
realization conventions. Its LeanSearch, Loogle and Mathlib/project/DAG searches
found no existing constant-extension compact comparison. All helper declarations
are listed in `lean.declarations`; no auxiliary theorem is postponed in this module.

## Second reading by Q124

The dispatcher forbids subagents; this is a second reading by the same worker,
followed by the maintainer's independent review. On this retry I opened both
modules, all three delivered nodes, the blueprint paragraph, and the published
Qbar Frobenius and restriction signatures. I checked the finite field, distinct
prime, algebraic closure and iota, separated finite type, e≥1, fibre identity,
theta^[e], lissity, both actual compact Frobenius operators, all integer degrees,
residue-degree conjugacy and all real weights against the node.

The H3/H4 defect is repaired in the retained source: R.obj F, the extended datum
and model, and the canonical comparison now occur in the cohomology clause. The
comparison's normalization fixes its arrow before cohomology, without putting the
Frobenius identity in its data. The four unowned definitions now have their own
existing-declaration node, and the item cites that owner and the field/model owner
instead of the heart-equivalence theorem. Local conjugacy, purity, lissity, e≥1
and independent universes are preserved. The stale report paragraphs were corrected;
the already passing Lean sources were retained as instructed.

Validation on 2026-10-19: the initial `deliver2.py --no-push` on the saved packet
passed server preflight and per-file compilation, including the comparison module
and the importing theorem module. The item's `lean.statement` was independently
checked to be verbatim from the theorem signature. No direct Git command, global
build, live-source edit or launcher-script edit was used.
