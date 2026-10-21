## Worker report

Item: lem-zl-classical-weil-filtration-heart-transport. Module:
`Sheaf.Paper.ClassicalWeilFiltrationHeartTransport`, main declaration
`WeilConjectures.zl_classical_weil_filtration_heart_transport`.
The theorem is postponed by `sorry`. Every auxiliary definition has real data;
the normalized input data are owned by the new definition module
`Sheaf.Paper.NormalizedClassicalWeilRealization`, and the remaining structures
describe filtration-output witnesses. No definition chooses
objects from its postponed existence assertion. The node's mathematical statement is
unchanged. Additional statement dependencies name the recorded interfaces and the two new
definition nodes used in the signature; the canonical normalization is the one
already required by the mathematical input identification.

Hypotheses and their Lean rendering:

- The prime-power finite field, its characteristic and algebraic closure are
  `D : FiniteFieldDatum.{u}`. The coefficient prime is `l : ℕ`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`. The algebraic closure is `Ω : Type (u + 1)`, `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`; the given complex isomorphism is
  `iota : Ω ≃+* ℂ`, with precisely its ring homomorphism passed to the weight predicates.
- `Y₀ : Over (Spec (.of D.k₀))` with `LocallyOfFiniteType Y₀.hom`,
  `QuasiCompact Y₀.hom`, and `IsSeparated Y₀.hom` is the separated finite-type model.
  `D.geometricFiber Y₀` is its actual geometric base change. The two inherited
  noetherian/separated instances construct the inherited structures. The coefficient
  prime unit comes from the already recorded `sfWeilPrimeInvertible`.
  `zlClassicalStalkInvertible` transports it to the stalk-unit convention; the classical
  category uses the recorded `adicCalculusPrimeInvertible` for that same unit.
  The main proposition installs the stalk-unit witness itself, so there is no
  additional prime-unit hypothesis.
- `ZlClassicalWeil` is an abbreviation for the recorded `EtaleLisseWeilSheaf`:
  `IsoAlgebra (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω)`.
  This is the classical coefficient-localized adic category, not a category of discrete
  non-torsion coefficient sheaves and not a Frobenius-stable lattice category.
- `ZlClassicalRealization` uses the existing `AdicLisseCalculusModels` on the geometric
  fibre. Its `normalization` identifies its functor with `models.realization` followed
  by `models.comparison.functor`. The recorded model bundle fixes inverse-limit integral
  realization, rational maps on `a ⊗ f`, actual completed fibres, and coefficient
  presentation transport. Its finite-dimension witness is a conclusion in the realization data; the
  stalk-unit witness is canonically inherited as above. Neither is an extra hypothesis. `heart` states degree-zero
  membership, and `pullback` transports the actual Frobenius pullback. The repair below pins that
  comparison on normalized finite stages. The `weil` functor
  is defined by `IsoAlgebra.mapOfNatIso`, retaining descent and its inverse.
- A given length `r` filtration is `F : ZlClassicalFiltration ... r`.
  Its `terms : Fin (r+1) → ...` and `quotients : Fin r → ...` are prescribed classical
  Weil objects; `inclusion` and `quotient` are their actual prescribed Weil morphisms.
  `zero` says the fibre of the initial term is zero as a module (`Subsingleton`).
  `exact` says injective, functionally exact, and surjective on every geometric adic
  fibre, using the recorded `lisseAlgebraicFiberFunctor` and its maps. No connectedness,
  positive rank, nonempty scheme, or strict-growth assumption is imposed.
- The constructible Weil sheaf is `G : sfCommonStageWeilSheaf ...` and its given
  identification including the Weil isomorphism is
  `e : (R.weil ...).obj (F.terms (Fin.last r)) ≅ G`.
  The theorem quantifies universally over the normalized realization R as well as every
  such filtration, sheaf and identification; R is not chosen ahead of e by the theorem.

Conclusions and their Lean rendering:

- `Nonempty (ZlFiltrationTransport ... R r F G e iota)` supplies the whole diagram,
  without making a noncanonical definition out of a mere existence result.
- `field : Padic.FiniteCoefficientFields l Ω` is one common finite field for the entire
  diagram. `model : ZlFiniteFiltration ... r field` consists of raw rational
  `sfWeilComplex` terms and quotients at that field. `terms_heart` and `quotients_heart`
  put their carriers in the actual standard heart, rather than merely asking for
  degree-zero abstract vector spaces. Its two arrow families are Weil morphisms;
  every `sfWeilComplex` stores a genuine isomorphism, hence both Weil directions.
- `ZlFiniteFiltration.zero` is `IsZero` of the initial raw object. Its `exact` says
  `ShortComplex.ShortExact` on the lifted arrows in the finite raw rational heart,
  with the actual composite-zero proof existentially recorded. Thus finite-stage
  exactness is part of the assertion, not inferred informally from a diagram elsewhere.
- `terms` and `quotients` identify the staged finite objects with the realization of
  precisely the given classical terms and quotients. These are isomorphisms of Weil
  objects. `inclusion` and `quotient` are commuting squares for the prescribed arrows.
  `top` is the resulting identification with `G`, and `top_identification` fixes it to
  the given `e`; it is not an unrelated top isomorphism.
- `zero` and `exact` assert the initial zero and each short exact sequence in the
  actual common-stage abelian Weil heart. Their maps are literally the realization
  functor's images of the given arrows. In particular every inclusion is a mono and
  its prescribed `S_j` is the quotient in that heart.
- `terms_fibres` and `quotient_fibres` give `ZlClassicalFibreComparison` for every term
  and quotient, all at the same finite field. Its finite side is `H⁰` of the recorded
  `localPointComplex`, lifted in size and extended along the actual finite-field
  embedding into Ω. Its classical side is the recorded actual adic fibre.
  `zlFiniteFibreMap` uses the same derived pullback, point fibre, cohomology and
  scalar-extension functors on maps. `inclusion_fibres` and
  `quotient_fibres_natural` require the comparison squares for all prescribed
  arrows, so the fibre identifications compare the entire filtration diagram.
- `local_operator` quantifies over every point, every positive exponent `n+1`, and
  every semilinear return equality `x ≫ Φ^(n+1) = γ^(n+1) ≫ x`. It identifies the
  recorded `localFrobeniusCohomology` with the classical operator. The latter is
  explicitly composed from the recorded pullback-fibre comparison and the actual
  Weil map for each step. The return path is constrained on every finite étale cover
  by `(β.hom.app P z).left = γ^(n+1) ≫ z.left`, so it cannot be an arbitrary chosen
  automorphism giving a coincidental conjugacy. The same `fibre x` works for every
  exponent. No minimal-period condition discards a constant-extension case.
- `purity` is an equivalence, for each prescribed quotient and each real weight,
  between the recorded `SfIsPunctuallyPureOfWeight` and the classical eigenvalue
  condition. `ZlClassicalPure` uses the actual closed-point degree and residue-field
  cardinality, the same normalized finite-cover return path, `Module.End.HasEigenvalue`,
  and `‖iota α‖ = (#κ(y))^(w/2)`. It does not assert that the given quotients are pure:
  it says purity and its weight agree whenever either side has it.
- Finite constant extensions are covered both by the arbitrary finite-field datum
  in the theorem and by the all-positive-period operator comparison: the iterated
  Weil structure groups the same successive factors, with exponent multiplied by
  the extension degree. There is no prime-to-degree or minimal-orbit restriction.
- At `r = 0`, `Fin r` is empty. The sole term is the initial/top zero object and the
  given top identification. No quotient, exact-sequence, or purity witness is required.

Dependency declarations read and used:

- `Sheaf.Paper.AdicPunctualWeights`: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, and the actual mixed-filtration convention.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfCommonStageWeilSheaf`,
  `sfWeilStageObject`, `sfCommonStageWeilForget` and their Frobenius pullbacks.
- `Sheaf.Paper.LisseIntegralSmallCoefficients` / `LisseAdicSheaves`:
  `AlgebraicGeometry.Scheme.LisseAlgebraicSheaf` and its coefficient-model construction.
- `Sheaf.Paper.LisseRationalRealization`:
  `WeilConjectures.LisseRealization.lisse_rational_realization`; its point normalization
  and pullback-compatible fully faithful comparison are used in the proof plan.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`, `localPointComplex`,
  `localFrobeniusCohomology`, `localClosedPoint`, and `localClosedPointDegree`.
- `Sheaf.Paper.EtaleWeilFundamentalRepresentation`: `EtaleLisseWeilSheaf`,
  `etaleAlgebraicFiberMap`, `etaleAlgebraicPathIso`. Only its general adic-category
  and normalized finite-cover fibre interfaces are used; no geometric connectedness
  assumption from its fundamental-representation theorem is imported.
- `Sheaf.Paper.LisseAdicFiberFunctors`: `lisseAlgebraicFiberFunctor` and its maps.
- `Sheaf.Paper.LisseAdicAutomorphismPullback`:
  `lisseAlgebraicAutomorphismPullback`, `lisseAlgebraicAutomorphismFiberIso`.
- `Sheaf.Paper.AdicLisseCohomologyCalculus`, owned by the new definition node
  `def-zl-adic-lisse-calculus-models`: `AdicLisseCalculusModels`, including
  `realization_integral`, `realization_map`, `comparison_integral`, `fiber_integral`,
  and `fiber_lisse`. This reuses the existing normalized realization data.
- Mathlib: `ShortComplex.ShortExact`, `Function.Exact`, `ModuleCat.uliftFunctor`,
  `ModuleCat.extendScalars`, `Module.End.HasEigenvalue`.
  All already-recorded proof-dependency modules are imported for the eleven-step proof
  in the theorem docstring; the proof follows the node and retains the separate sf and
  PBC point-fibre comparisons in Step 5.

Source and edge-case reading: opened the current blueprint proof
`main-20261015/.../sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraphs 1 and 4, and read the complete node's eleven proof steps. Checked the empty
scheme, the zero sheaf, `r=0`, zero/repeated quotients, disconnected schemes with different
ranks, rational Weil arrows with no stable integral lattice, nonminimal return periods,
and arbitrary positive constant-extension degrees. The formulation keeps all these cases.
No counterexample or statement correction was found.

Searches actually made before defining the statement:

- `msearch.py`, LeanFinder, query “Transport a finite filtration of classical lisse adic
  Weil sheaves to the constructible heart preserving normalized Frobenius fibres”:
  eight unrelated algebraic-filtration/local-cohomology hits; no match.
- `msearch.py`, Loogle, query `CategoryTheory.ShortComplex.ShortExact,
  CategoryTheory.Functor.FullyFaithful`: zero hits. Short exactness itself is nevertheless
  reused from Mathlib; there is no existing assertion of the full transport.
- `msearch.py`, grep, query `WeilSheaf|lisse.*realization`, subdirectory AlgebraicGeometry:
  zero hits in Mathlib.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `ClassicalWeilFiltration`: no existing declaration of this statement. Conceptual searches
  for lisse realization, classical adic fibres, and Weil filtrations found the existing
  modules listed above. The upstream `WeilSheaf.LisseFiltration` belongs to another,
  discrete-coefficient category and is not a substitute for this statement.
- Read the source-based interfaces before composing them; in particular reused
  `AdicLisseCalculusModels` instead of introducing a second scalar-localization model.

## Second reading by Q18

The dispatcher explicitly forbids starting other agents. This is a separate self-reading,
not a claim of an independent reader. Reopened the node and compared its clauses to the
module as detailed above. The key checks were: the given arrows and quotients are retained;
`e` is a Weil isomorphism; neither Weil-stable lattices nor connectedness are assumed;
finite-stage and common-stage exactness are both required; all finite inverse Weil maps
are stored at one field; normalized return transport is constrained on finite-cover germs;
and `r=0` has no spurious quotient index. The definitions are data constructions or witness
structures, and the sole postponed theorem carries the node's full natural-language proof.
The maintainer's independent statement review remains the independent review.

Elaboration repairs: used the normalized model bundle's canonical residue-prime
inverse throughout the classical category, rather than casting functors across
two different instances of the same inverse data. On the sf side, used the exact
`AlgebraicallyClosedCoefficients.Coefficient` presentation expected by
`sfWeilStageObject`; its pbc alias caused repeated, expensive reductions through
the localized categories. These changes do not restrict universes or alter any
mathematical assumption.

## Repair of return L, immutable head 7824c8832548

1. **H3/H4: pin the Weil realization and preserve a given identification.**
   Replaced the existential quantifier on R with a universal quantifier in
   `ZlClassicalFiltrationHeartTransport`. Added `pullback_pinning` to R. For every
   finite field E this requires the proposition `ZlClassicalPullbackStage`,
   with normalized data `ZlClassicalPullbackModels` and the following equations. `realization`, `along` and `normalized` are the recorded
   `LisseRealization.At`, `Along`, and `PullNormalized`, at the actual geometric
   Frobenius map, with no k-linearity assumption. `completed` and `operation` use
   the recorded `CompletedLisse.Comparison` and `Operation` on the same scheme
   and the identity coefficient map. Their existing reduction, reconstruction
   and rational section normalizations remain part of those types.

   The coefficient isomorphism is pinned on EVERY continuous section value by
   `coefficient_values`, using the actual `Shrink.algEquiv`; it cannot introduce
   a coefficient automorphism. The finite raw realization and its ordinary
   sheaf comparison are natural functors/isomorphisms. `sheaf_linear` requires
   this underlying abelian-sheaf isomorphism to be linear through exactly the
   specified coefficient isomorphism. The `sections` equation
   starts with an arbitrary section s, applies the actual ordinary module
   pullback adjunction unit, the inverse of `along.comparison`, the finite raw
   pullback comparison and the sheaf comparison. It equates this with the
   completed-system rational adjunction unit followed by `operation.rational`.
   `PullNormalized` pins the former comparison to ordinary completion, while
   `Operation.rational_normalization` pins the latter to finite-level pullback
   and inverse-limit projections. This equation determines the finite raw
   comparison by adjunction and full faithfulness; it is not a freely chosen
   NatIso. `classical_units` also fixes the completed operation at EVERY finite
   reduction level: its etale unit followed by rawIntegral inverse is the
   canonical etale adjunction unit into literal automorphism reindexing. That
   latter unit is defined from the existing upperStar/localization-restriction
   comparison, with no chosen map or new existence theorem. This prevents a
   scalar twist hidden in either `EtaleOperation.level` or `rawIntegral`.
   `classical_objects` and `stage_pullback_objects` are equality proofs
   identifying the actual prescribed object formulas, so their transports are
   `eqToHom`, with no arbitrary isomorphism at either endpoint.

   Finally the pinning equation equates the actual component of R.pullback with the image
   of that finite comparison through the finite-stage natural realization
   isomorphism. The same `stage` natural isomorphism occurs before and after
   Frobenius, hence changing a presentation conjugates the entire realization
   coherently. The universal R quantifier lets a caller supply its existing
   canonical realization and its given e. It cannot require replacing e by an
   identification through a theorem-chosen transport. No objects or maps are
   chosen from the postponed theorem. These normalization witnesses exist by
   composing the two cited normalized comparisons; restricting to finite-free
   systems loses no rational lisse object, since the proof replaces only its
   underlying integral model by a stable lattice, not its Weil maps.

2. **Theorem dependency used only for definitions.** Added the definition node
   `def-zl-adic-lisse-calculus-models` with `existing:true` on the UNCHANGED
   `Sheaf.Paper.AdicLisseCohomologyCalculus` module. Replaced the spurious
   `lem-per-adic-lisse-cohomology-calculus` statement edge by that definition
   edge. The item uses model data and inherited invertibility, and assumes no
   tensor/cohomology-calculus conclusion. Added the existing definition edges
   `def-per-lisse-completed-system-data`, `def-real-lisse-realization-data` and
   `def-real-lisse-pullback-normalization` for the interfaces in the pinning.

3. **Advisory on hUnits.** The main proposition installs hUnits with the same
   inherited stalk-unit proof as before. The final theorem type is checked
   explicitly below. The first printed type exposed Lean automatic section-instance
   inclusion; `omit hUnits in` on the proposition and theorem removes that
   extraneous binder. The subsequent full compile confirms it is absent.

The mathematical node statement and its eleven proof steps are unchanged.
The existing filtration, exactness, common finite stage, normalized local
operator with pinned beta, purity equivalence and r=0 clauses are retained.

## New nodes

`def-zl-adic-lisse-calculus-models` owns precisely the already existing normalized
model structure `AlgebraicGeometry.Scheme.AdicLisseCalculusModels` and its integral
inclusion, realization, coefficient-presentation, cohomology and fibre helpers,
including `adicCalculusPrimeInvertible`. It introduces no Lean copy and asserts
no existence/calculus theorem. Source: Bhatt--Scholze §6.8, especially 6.8.4(1),(4),
6.8.14(2), 6.8.15, used in the blueprint proof paragraph 1. LeanSearch and LeanFinder
found ordinary adic completion/profinite-limit results; Mathlib grep found no
`AdicLisseCalculusModels` or `adicCalculusIntegralRealization`. Project grep found
the exact declarations in the reused module, and DAG grep plus
`blueprint_refs.py search 'adic lisse calculus'` found no definition-node owner.
The new node stores the complete search responses and cites the existing
coefficient, classical lisse, cohomology, geometric point and presentation notions.

`def-zl-normalized-classical-weil-realization` owns the complete normalized
realization interface in `Sheaf.Paper.NormalizedClassicalWeilRealization`. Its
statement lists the same bases, models, heart, coefficient, section-unit,
classical-unit and common-stage equations as the Lean. This is the notion
required to interpret the input identification canonically, separated from the
filtration theorem. The main module imports it and remains universal in its
`ZlClassicalRealization`. Search of the live DAG, project sources and blueprint
found no other owner; LeanSearch/LeanFinder found only general categorical or
isocrystal material, and Mathlib grep found no match. Complete search responses
are in the node. Every moved declaration's blueprint docstring names this owner.


## Second reading by Q18 (repair)

Reopened the repaired file, the unchanged mathematical node, both new definition nodes, `PullNormalized`, `Along`, and
`Operation`, including their unit/projection normalizations. Checked that the
same geometric Frobenius appears in both comparisons and in `R.pullback`; the
coefficient arrow is the identity, coefficient presentation is pointwise fixed,
and the classical finite units fix rawIntegral as well as the etale levels,
and the final pinning equation uses a single natural finite-stage comparison on
both sides. The theorem is universal in R and e, so no chosen R precedes the
caller's identification. Checked the new node against all fields of
`AdicLisseCalculusModels`: comparison_integral, realization_integral,
realization_map, cohomology_integral, degree-zero/nonzero-degree clauses,
fiber_integral and fiber_lisse. The type is reused unchanged and no theorem
conclusion is named as model data. The original clause-by-clause reading above
continues to apply to the unchanged filtration and output structures. No
statement correction or disputed mathematical statement is needed.

The pinning predicate uses existential witnesses only for its internally normalized
comparison data; R itself remains universally quantified. Its section, classical-unit
and common-stage equations are unchanged when expressed as a proposition. This
avoids unnecessary constructor machinery for proof witnesses and keeps the interface
small and reusable.

## Validation of the repaired packet

The prescribed `scompile.py` compiled both delivered modules separately, in dependency
order, against the live server library, with no errors or extra warnings. The
normalized-realization module compiled in 20.8/22.4 seconds; the final main theorem
compiled in 35.4/39.1 seconds. No heartbeat or time limit was raised. A temporary
`#check @zl_classical_weil_filtration_heart_transport` printed exactly the finite-field,
prime, algebraic-closure, separated finite-type and complex-identification parameters;
there is NO hUnits instance argument. The diagnostic command has been removed.
All moved declarations carry their new owning node's blueprint docstring; source
line widths are at most 92, and the main theorem is the only sorry in the delivery.
The mathematical statement is unchanged, and all three returned points are repaired.
The prescribed `deliver2.py --no-push` passed preflight and all file compiles:
`OK (dry run): commit 666fb898a27 passes the preflight and compiles; nothing pushed`.
The final report update records this result; the push wrapper checks the packet again.
