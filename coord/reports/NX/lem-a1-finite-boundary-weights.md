## Worker report

This packet supersedes the retained, unvalidated `existing: true` binding.
The old upstream theorem is on AlgebraicGeometry.WeilSheaf; current punctual
weights are on sfCommonStageWeilSheaf. A successful check of the former does
not compare these categories. The delivery now states the node on the actual
common-stage heart in Sheaf.Paper.FiniteBoundaryWeights. The sole postponed
proof is WeilConjectures.sf_finiteBoundary_hasWeightsAtMost, with the complete
four-step DAG proof in its docstring. Definitions contain actual data.
The previous attempt's report is retained in scratchpad/previous-report.md.

Hypotheses and conclusion, clause by clause:

- The ambient finite field, its chosen algebraic closure and q=p^a are the
  recorded FiniteFieldDatum D. The prime coefficient characteristic and its
  inequality to p are `[Fact l.Prime]` and `hl : l ≠ D.p`.
- The specified algebraic closure of Q_l is Qbar with Field, Algebra and
  IsAlgClosure instances. `iota : Qbar ≃+* ℂ` is the fixed field isomorphism,
  with no continuity assumption. Scheme universe u and coefficient universe v
  remain independent.
- “Z₀ finite over k₀” is `Z₀ : Over (Spec (.of D.k₀))` and `[IsFinite Z₀.hom]`.
  Finite type, quasi-compactness, separatedness and properness are consequences
  of this hypothesis. No such extra geometric assumption is bound.
- “constructible Weil sheaf” is `G : sfCommonStageWeilSheaf D l hl Z₀ Qbar`.
  This is the recorded full heart of the actual common-stage fixed-pair category.
- “whose stalks have weights at most w” is hG: at every closed point y and for
  every actual local Frobenius eigenvalue α, `‖iota α‖ ≤ (#κ(y))^(w/2)`.
  SfPunctualEigenvalue computes these eigenvalues after genuine scalar extension
  from a finite Weil stage, so no eigenvalues outside that stage are omitted.
  For a single stalk, this spectral bound is equivalent to its finite stable
  mixed filtration by lem-a1-punctual-bound-module-mixed. It imposes no global
  mixed-filtration hypothesis on G.
- “H_c^0(Z,G)” is commonStageCompactWeilCohomology with n=0 and the explicit
  compactification Compactification.ofIsProper Z₀.hom (identity open part).
  It is zlWeilHigherShriek of the structure map to Spec(k₀), and retains the
  canonical induced Weil structure. Its geometric fibre is exactly the
  coefficient H_c^0: this is the specialization to the base point of the
  recorded zlWeilHigherShriek_compactSupportComparison, followed by the
  recorded geometric-point fibre equivalence. This uses geometric cohomology,
  with no arithmetic invariants.
- “has weights at most w” is SfIsMixedOfWeightsAtMost for that canonical
  cohomology Weil sheaf on Spec(k₀). The point's sole closed point has residue
  field k₀, so its local operator is global q-Frobenius and its base is q.
  A finite mono filtration in this point heart, with pure cokernels, is exactly
  the stable-subspace filtration of its coefficient Frobenius module from
  FrobeniusModule.IsMixedOfWeightsAtMost. Both allow length zero. This is the
  same cohomology and mixedness expressed before applying the point-fibre
  equivalence; no substitute linear action is supplied.

Dependency declarations read and used:

- Sheaf.Paper.AdicPunctualWeights:
  WeilConjectures.SfPunctualEigenvalue and SfIsMixedOfWeightsAtMost; the former
  uses localClosedFrobeniusCohomology and sfAdicCoefficientEmbedding.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite;
  Integral.lean was also read for the dependency's IsIntegralHom clause.
- Sheaf.Paper.OrdinaryCompactWeilCohomology and its public predecessor
  OrdinaryCompactCohomology: all previous ordinary/compact coefficient
  constructions, including qbarWeilSheafCohomology, remain public in the
  dependency repair module. The older WeilSheaf specialization is retained
  but is not used to identify G with a different category.
- Sheaf.Paper.WeilCompactSupportCohomology:
  WeilConjectures.zlWeilHigherShriek and its complete construction and
  compact-support comparison were read. The existing landed node
  def-zl-weil-compact-support-cohomology is added to stmt_deps.
- Sheaf.LinearAlgebra.FrobeniusModuleWeights:
  FrobeniusModule.IsMixedOfWeightsAtMost, and its proof-use theorem in
  Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed, are retained through a
  proof import. They give the final spectral-bound-to-filtration step.
- WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic:
  LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ is a proof import.
- lem-a1-finite-weil-sections-decomposition has no recorded Lean module;
  no fictional import is introduced. Its use is explained in the proof
  docstring. No new object from that proof-only node is needed by this signature.

Edge cases checked before writing: empty Z₀ and zero G give the zero image and
length-zero filtration; arbitrary real w is allowed. A point of degree d>1 uses
q_y=q^d, so the return identity involves F^d, not F on a single stalk.
A nonreduced finite scheme is allowed, as the canonical site construction is
unchanged by nilpotents. Jordan blocks and eigenvalues outside a finite field
of definition are included. No reducedness, lissity, semisimplicity or
connectedness assumptions appear. A finite scheme with points of different
residue degrees is covered by the independently normalized hG at each point.

Searches (2026-10-18; full machine logs are in searches.jsonl):

- LeanFinder via msearch.py: “A finite scheme over a finite field has compactly
  supported degree zero Weil cohomology of weights bounded by the weights of
  its stalks”. Eight hits, including IsArtinianScheme.finite and finiteness of
  finite-morphism fibres, but no cohomological weight theorem.
- LeanSearch via msearch.py: “Weights at most w on stalks of a Weil sheaf on a
  finite scheme imply weights at most w on compactly supported cohomology in
  degree zero”. Eight polynomial-weight hits, no relevant theorem.
- Loogle via msearch.py: `"Frobenius", "cohomology"`: zero hits.
- Mathlib grep via msearch.py: `WeilSheaf|FrobeniusModule|compactlySupportedCohomology`:
  zero hits. Mathlib has the finite/integral scheme morphism definitions used.
- rg in upstream WeilConjectures and side lean/Sheaf for the item id,
  finite-boundary names and the old theorem name: upstream Cohomology has
  finite-boundary vanishing, but no common-stage weight result; the published
  AffineCurveUpper source obtained through scompile.py --source contains the
  old WeilSheaf theorem, which is inapplicable to the recorded heart.
  The side library supplies the canonical higher compact-support image used
  here, not the current node's weight theorem. No duplicate theorem is stated
  on the older category.

No source/node statement correction and no new independent node are needed.
The item keeps its original statement, proof and proof_deps. The only added
statement dependency is the already landed canonical higher-image definition.

## Dependency modules

`def-weil-ordinary-compact-cohomology`: the previous Frobenius-retaining
specialization takes the older WeilSheaf category, and its actual common-stage
coefficient construction forgets Frobenius. Section 1(B) permits the module
Sheaf.Paper.CommonStageCompactWeilCohomology. It publicly imports the entire
old interface and supplies commonStageCompactWeilCohomology as the existing
canonical compact-support higher image on Spec(k₀). It retains the actual
common-stage heart, its canonical action and its coefficient comparison.
The identity base point and its inherited IsFinite instance merely expose the
structure map to typeclass inference. Their data are literal identity data
and inferInstanceAs of the identity's existing Mathlib instance. There is no
new postponed theorem and no existence-choice of an operator. Only this
node's lean field changes. All integer-degree and all four coefficient cases
remain public from the original module.

## Second reading by NX

The dispatcher forbids sub-agents and specifies the maintainer's independent
review after delivery. This is an author re-reading, not a claimed independent
review. Read the item, the source node and unit, each dependency declaration,
and both generated files together. The old category mismatch is repaired:
G, punctual spectra and the compact-support image now belong to the same
common-stage heart. The compactification is canonical for the finite map,
so no new hypothesis is added. The conclusion is mixedness of the canonical
cohomology object at the base point; geometric coefficient fibres identify
its filtration with precisely the module filtration, normalized by q.
Neither a global sheaf-mixedness hypothesis nor arithmetic stalk invariants
have been inserted. Both universes are explicit and independent. Source
statements are unchanged. The previously reported tool-generated long-line
fault concerned only the now-withdrawn old existing-record probe.

## Validation

The required initial unchanged dry run reproduced the previous wrapper-generated
long #check warning. The packet was then repaired mathematically, rather than
reasserting that older-category binding. All compilation uses prescribed
scompile.py, per file in dependency order, with the private overlay and the
unchanged 60-second limit. Compiler and dry-run results are appended below.

Both delivered modules passed scompile.py together in dependency order, exit 0,
with no errors or warnings in either context. Dependency module: 3.8 s sandbox,
4.0 s library; item module: 3.6 s sandbox, 3.9 s library. The dependency was
also separately compiled in the overlay/preliminary passes (3.9 s/3.6 s).

The required deliver2.py --no-push dry run passed preflight and per-file
compilation: OK, temporary commit 5ea5b49995. It staged exactly the item node,
the lean-only ordinary/compact dependency repair, both owned Lean modules and
this report. No source statement or proof field changed.
