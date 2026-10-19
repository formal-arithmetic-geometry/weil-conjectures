## Worker report

The module states both clauses of lem-kun-0f10 in one conjunction, using the numerical torsion étale dimensions recorded by def-kun-cd. The K-morphism clarification is recorded below; no extra node, dependency module or disputed statement is needed.

Hypothesis and clause correspondence:
- The field is `(K : Type u) [Field K]`.
- The schemes are `(X Y : Scheme.{u})`, with `[X.Over (Spec (.of K))]` and `[Y.Over (Spec (.of K))]` recording their structure morphisms.
- Finite type of each structure morphism is exactly the pair `[LocallyOfFiniteType (...)] [QuasiCompact (...)]`.
- The morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of K))]`, commuting with the structure morphisms. No additional finite-type or separatedness hypothesis on f is added.
- Clause (1) is `Scheme.Hom.torsionEtaleCohomologicalDimension f < ⊤`, with its implicit qcqs proofs supplied explicitly. Finite type over the Noetherian field implies local Noetherianity; quasi-compactness of the structure map implies compactness of X. Thus X is Noetherian, every f is quasi-compact, and X is quasi-separated, hence so is f. These are derived instance arguments, not new hypotheses.
- Clause (2) is `IsSepClosed K → Scheme.torsionEtaleCohomologicalDimension X < ⊤`, again with compactness and quasi-separatedness derived explicitly. Since X is arbitrary among finite-type K-schemes, this gives the universal claim. The prose following the numbered clauses records provenance and other occurrences, rather than extra mathematical conclusions.

Statement dependency declarations read and used:
- Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension: AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension and AlgebraicGeometry.Scheme.Hom.torsionEtaleCohomologicalDimension. Their full definitions are infima of the nonnegative torsion bounds in ℕ∞.
- Mathlib.FieldTheory.IsSepClosed: IsSepClosed (every separable polynomial splits).
- Mathlib.AlgebraicGeometry.Over: AlgebraicGeometry.Scheme.Over (structure map X ↘ S).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: AlgebraicGeometry.LocallyOfFiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: AlgebraicGeometry.QuasiCompact.
- def-weil-pbc-scheme-conventions is a convention record, with no own declaration. Its qcqs meanings are the Mathlib classes used by the numerical dimensions.

All recorded proof-dependency modules are imported as ordinary imports unless already public statement imports. Proof dependencies without recorded Lean modules are not invented. The docstring gives all six recorded proof steps: Noetherian qcqs geometry, relative Mayer–Vietoris by localization and sheafification, affine support vanishing, open induction, finite target-cover locality, and absolute induction over a separably closed field. The source was read at literature/stacks-project/etale-cohomology.tex, lemma-finite-cd (Tag 0F10); its second assertion applies after the recorded separably closed point calculation.

Edge cases: X may be empty (dimension zero), Y may be empty (then X is empty), and there is no nonemptiness, affine, smooth, proper, separated, positive-dimensional or characteristic restriction. A single universe u for the field and schemes permits every such input after universe lifting; sheaf coefficients use the recorded u+1 encoding. The finite bound includes zero; `< ⊤` in ℕ∞ means precisely finiteness. Arbitrary torsion abelian sheaves, rather than only sheaves killed by one fixed integer, remain quantified inside the shared definitions.

Searches for an existing statement:
- msearch.py leanfinder: “A morphism between schemes of finite type over a field has finite torsion etale cohomological dimension”: 8 hits concerning algebraic étaleness; no match.
- msearch.py loogle: `"cohomologicalDimension"`: 0 hits.
- msearch.py grep: `cohomologicalDimension|torsionEtaleCohomologicalDimension`: 0 Mathlib hits.
- msearch.py leansearch: “finite cohomological dimension of etale direct image of a finite type morphism”: service unavailable (Internal Server Error).
- rg in WeilConjectures and lean/Sheaf: `torsionEtaleCohomologicalDimension|finite.*[Cc]ohomological|[Cc]ohomological.*finite`: found the shared dimension definitions and absolute dimension-bound theorems, but no theorem giving both clauses or the finite relative dimension assertion. In particular upstream AlgebraicGeometry/Sites/CohomologicalDimension.lean gives an absolute numerical bound with explicit dimension/field-bound assumptions; it is not this statement.
- rg for `lem-kun-0f10` in upstream WeilConjectures: no hits. The proposed full declaration name is new.

Validation: every delivered module is compiled on the server through scompile.py (nice 19, two threads, 60 seconds per file). The final dry run is run through deliver2.py --no-push; the independent second reading is intentionally left to the second reader.

## Statement corrected

The original statement began: Let $K$ be a field and let $f:X\to Y$ be a morphism between
schemes of finite type over $K$.

The rest of the old statement is unchanged; its complete verbatim text is in statement_change.old_statement. The correction makes f explicitly a K-morphism, citing def-weil-scheme-over-base. Stacks Tag 0F10 uses Tag 0F0X; the first diagram of the proof of 0F0X factors the affine K-morphism through a projection of affine K-spaces. This requires compatibility with the K-structure maps. The original worker report incorrectly said compatibility was unnecessary; this replacement corrects that sentence, and the Lean includes [f.IsOver (Spec (.of K))]. No unit statement or proof route changes.

- lem-sf-integral-direct-image-constructible: holds: true. The statement explicitly assumes f is a K_0-morphism; its use of clause (1) remains valid.
- lem-kun-kunneth-map-agrees: holds: true. The relative map in (b) is the fibre-product projection over k; absolute finiteness uses unchanged clause (2).
- lem-kun-0f0g: holds: true. Uses only unchanged clause (2) for the proper geometric fibre over the algebraically closed field Omega.
- lem-kun-0f1n: holds: true. The commutative diagram is over Spec K; g and h commute with the induced K-structure maps.
- thm-kun-0f1p: holds: true. The product projection is a k-morphism, and the absolute clause is unchanged.
- lem-kun-0f14b: holds: true. The product projection is a k-morphism; absolute finiteness for Y is unchanged.
- lem-pur-ordinary-kunneth-finite-ring: holds: true. Uses unchanged clause (2) on X, Y and their product over the algebraically closed field k.

## Second reading by NM

Independent second reader: read the node, its statement dependencies, the complete delivered
module, and Stacks etale-cohomology.tex at lemma-finite-cd (0F10), together with
lemma-interlude-I (0F0X). The source first states relative finiteness, and then absolute
finiteness assuming finite cd(K). The node intentionally specializes the latter to a
separably closed field, using the separately recorded zero-dimensional point calculation.
The source's 0F0X proof starts with a commutative closed-immersion diagram over K. Thus its
morphism is over K, a condition the first worker omitted. The node now makes this explicit.

Object, hypothesis, and conclusion checklist against the corrected source reading:

- A field K: `(K : Type u) [Field K]`. Exact; no characteristic or perfectness condition.
- Schemes X and Y over K: `(X Y : Scheme.{u})`, `[X.Over (Spec (.of K))]` and
  `[Y.Over (Spec (.of K))]`. Exact data: opened Mathlib.AlgebraicGeometry.Over,
  where Scheme.Over is OverClass, supplying the structure morphism `X ↘ Spec K`.
- Finite type of X over K: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`. Exact conjunction from
  def-weil-finite-type-morphism. Opened Mathlib's FiniteType and QuasiCompact definitions:
  finite generation on affine pairs and compact inverse images of compact opens.
- Finite type of Y over K: the corresponding two Y instances. Exact, with no separatedness.
- A morphism over K: `(f : X ⟶ Y) [f.IsOver (Spec (.of K))]`. REPAIRED: the first
  worker used only the bare arrow. Opened Scheme.Hom.IsOver and Hom.isOver_iff: this is
  precisely `f ≫ (Y ↘ Spec K) = X ↘ Spec K`, not a finite-type or finiteness assumption.
- Clause (1): `@Scheme.Hom.torsionEtaleCohomologicalDimension ... < ⊤`. Exact uniform
  finite torsion bound, with the quantifier over all torsion sheaves inside the definition.
  Opened the dependency module: sInf of natural bounds in ENat, empty set giving infinity;
  higher direct image is Plus.homologyFunctor of rightDerivedLowerStarPlus of the sheaf
  in degree zero. Opened the latter functor: it is the derived ordinary etale pushforward.
- Required qcqs evidence is supplied by explicit applications of existing Mathlib declarations, not by extra binders or local proofs.
  Checked LocallyOfFiniteType.isLocallyNoetherian, quasiCompact_iff_compactSpace,
  IsLocallyNoetherian.quasiSeparatedSpace, quasiCompact_of_noetherianSpace_source,
  and the source-quasi-separated instance. These derive the evidence from finite type.
- Clause (2): `IsSepClosed K → @Scheme.torsionEtaleCohomologicalDimension X ... < ⊤`.
  Exact. Opened IsSepClosed: every separable polynomial splits, equivalent to the recorded
  no-nontrivial-finite-separable-extension condition. Opened the absolute numerical
  definition and HasTorsionEtaleCohomologicalDimensionLE: all torsion abelian etale sheaves,
  ordinary derived sections, Subsingleton in degrees above the bound. Natural positive
  degrees suffice for every integer above a nonnegative bound. No fixed annihilator is
  imposed. Universal finiteness for every X follows from this universally quantified
  theorem by taking Y = X and f = identity; hence the conjunction adds no restriction
  to the separate absolute assertion.
- The remaining prose of the node records provenance and other occurrences; it asserts
  no further bound to be included in the conclusion. Exact.

The convention dependency def-weil-pbc-scheme-conventions intentionally defines no object.
All notions use its referenced Mathlib classes. No sibling, extra definition node, dependency
module, private definition, local notation, or hollow construction is present. The only
sorry is the named theorem's whole proof. The instance arguments reuse existing Mathlib declarations.
The docstring gives the source and blueprint id and all six proof steps: Noetherian geometry,
relative Mayer–Vietoris by localization/sheafification, affine support, open induction,
finite-cover locality, and absolute induction after the separably closed point calculation.
I clarified that the affine map in step 3 is over K; the other correct text is preserved.

Edge cases: X can be empty; if Y is empty then X is empty; the dimensions have finite bound
zero there. The empty finite affine cover uses maximum zero. There is no nonemptiness,
positive dimension, separatedness, smoothness, properness, or invertibility restriction.
Bound zero is allowed and includes vanishing in every positive degree. There is no separate
n in the statement and no index-type binder. `universe u` is bound explicitly, the common
scheme/field universe is the recorded Scheme.Over convention, and the dependency fixes
coefficient universe u+1. There is no test object quantified in a smaller universe or extra
smallness assumption. All variables and instance arguments are bound.

Independent searches with words different from the worker's first query:

- msearch.py leanfinder: “higher direct image torsion sheaf vanishes above a finite bound
  for a morphism over a field”: 8 hits, general derived-category vanishing and injective
  acyclicity, no relative etale finiteness theorem.
- msearch.py loogle: `"HasTorsionEtaleCohomologicalDimensionLE"`: 0 hits.
- msearch.py grep: `cohomological.*[Dd]imension|[Dd]imension.*cohomological`: 0 hits.
- msearch.py leansearch: “A finite type morphism of schemes over a field has finite
  cohomological dimension for torsion etale sheaves”: service unavailable, recorded as such.
- rg in upstream WeilConjectures and repository lean/Sheaf for finite/cohomological/etale
  dimension phrases: no existing relative assertion. Opened upstream
  AlgebraicGeometry/Sites/CohomologicalDimension.lean: its statements bound absolute Sheaf.H
  by 2*d+c, with explicit dimension and field bounds. These are useful proof inputs, not
  this two-clause statement. Opened the project's CohomologicalDimensionGroundField.lean:
  it descends a given geometric bound and is likewise a different statement.
- rg in dag/lean_names_upstream.json and both source trees for the full proposed declaration
  name and blueprint id found no existing declaration. Shared numerical definitions are
  reused without duplication.

Mismatch and repair: omitted compatibility with K, also incorrectly described as unnecessary
in the worker report. Added IsOver, clarified the node's ambiguous wording under brief §1(C),
and recorded the source and all seven citer verdicts in statement_change and the preceding
section. Independently checked especially lem-sf-integral-direct-image-constructible (it
explicitly assumes a K_0-morphism) and lem-kun-0f0g (only the unchanged absolute assertion on
its proper geometric fibre); also read the other five uses. No citer or unit was edited.

Validation: corrected module compiled cleanly via scompile.py on the server, nice 19,
two threads, limit 60 seconds per file. It also compiled the necessary side-only imported
modules in the private overlay. The node lean.statement is copied verbatim from the final
signature. Delivery dry run and final delivery are performed after this report.

The first dry run rejected two inherited bracketed theorem mentions in the provenance paragraph as missing statement dependencies. Rendered those same theorem names with TeX texttt instead: the mathematical content and all dependencies are unchanged. They describe other occurrences and the proof specialization, not new notions in the signature.

## Maintainer review fixes

The immutable signature contained three local `by` proofs with `have` declarations for
qcqs instances. For the pilot no-local-proof gate (H6), the complete replacement uses
`quasiCompact_of_compactSpace`, `IsLocallyNoetherian.quasiSeparatedSpace`, and
`QuasiSeparated.of_quasiSeparatedSpace` explicitly. Local Noetherianity is the existing
`LocallyOfFiniteType.isLocallyNoetherian` theorem; compactness is the existing
`quasiCompact_iff_compactSpace`. This changes only proof arguments in Prop, with exactly
the same field, schemes, finite-type structure maps, K-morphism compatibility and two
conclusions. No theorem, definition, instance, assumption or import was added. The
lean.statement record is updated verbatim. The earlier worker compatibility sentence and
second-reader description of local instance proofs have been corrected in this replacement
report; the statement-correction history remains recorded above.

Independent maintainer reproduction: scompile.py compiled the immutable module in 1.6 s
and the final replacement in 1.6 s, both with no diagnostics. Each run compiled the
side-only CohomologicalDimension, TorsionEtaleCohomologicalDimension and
FiniteTypeDimensionFormula dependencies separately in its private overlay. All invocations
reported nice 19, two threads and a 60 second per-file limit. No local Lean, lake build,
project mutation, live-library write or delivery command was run by this reviewer.
