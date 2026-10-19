## Worker report

The module `lean/Sheaf/FieldTheory/ValuedCurveEtaleParameter.lean` states
`ValuationSubring.exists_etale_parameter_of_smooth_centre`, with one postponed proof and
no new definitions. The module docstring and theorem docstring cite Temkin's Theorem 2.1.8,
its finite-height proof, and the parameter paragraph of Proposition 4.3.3. The theorem
contains the complete fourteen-step proof plan from the reviewed DAG split.

The preceding stale-assignment report confused stages: Q30's 2026-10-19 accepted work is
stage 1, with eight new proof inputs. The current item has `reviewed` but no `lean` or
`reviewed_lean` field. This packet preserves the accepted statement and split and supplies
its stage-2 statement; it neither repeats that split nor re-pushes Q30's branch. The
sandbox initially contained only four dispatcher marker files, so there was no interrupted
Q115 delivery to repeat or recover. There is no repair note or Q115 return for this item.

Hypothesis and clause audit:

- The fields are `(K L : Type u) [Field K] [Field L] [Algebra K L]`, with the canonical
  injective field map `algebraMap K L`. `[IsSepClosed K]` is separable closure of the base,
  without imposing perfectness or algebraic closure.
- `R : ValuationSubring K` and `W : ValuationSubring L` implement the given valuation
  subrings. Their defining alternative is `x ∈ A ∨ x⁻¹ ∈ A`; their existing
  `IsFractionRing` instances supply the respective fraction fields. No DVR, nontriviality,
  rank-one or Noetherian assumption is added.
- `[Finite (PrimeSpectrum R)]` says that the prime ideals form a finite set. They form a
  chain automatically for a valuation ring, so this is exactly the finite-chain condition.
- `hrestrict : W.comap (algebraMap K L) = R` expresses `W ∩ K = R` under the given embedding.
- `hfg : (⊤ : IntermediateField K L).FG` means finite generation as a FIELD extension;
  it does not incorrectly require the field `L` to be finite type as a `K`-algebra.
- `htrdeg : Algebra.trdeg K L = 1` is transcendence degree one.
- `C : Scheme.{u}` with `[IsIntegral C]` is the smooth integral curve, and
  `[C.Over (Spec (.of K))]` gives its structure morphism.
- `[Smooth (C ↘ Spec (.of K))]` expresses smoothness of that structure morphism.
  `[LocallyOfFiniteType ...]` and `[QuasiCompact ...]` express finite type exactly as
  the dependency record specifies. `hdim : topologicalKrullDim C = 1` supplies dimension.
- `e : C.functionField ≃+* L` identifies the actual generic stalk with `L`.
  `C.functionField` is the stalk at `genericPoint C`, and is a field by integrality.
- `Algebra.adjoin K (W : Set L)` is the ring `KW` INSIDE `L`, not an arbitrary localization
  with an unspecified map. Indeed every element of `K` is a quotient of elements of `R`,
  so this generated subring is contained in `(R\{0})⁻¹W`; conversely it contains `W` and
  inverses of every nonzero element of `R` since it contains `K`. These inclusions identify
  the two subrings canonically. The existing `Subalgebra.val` is its inclusion in `L`.
- `centre` is the specified morphism from this ring's spectrum to `C`. `hcentre` says it
  is over `K`. `hgeneric` identifies its composite with `Spec L → Spec KW` with
  `Spec e ≫ C.fromSpecStalk (genericPoint C)`. Thus the generic field identification is
  enforced on morphisms, not merely on the image of the generic point. Together the two
  equalities also enforce compatibility of `e` with the `K` structure: the maps to
  `Spec K` agree after this restriction. No unrelated `Algebra K C.functionField` is chosen.
  Passing these existential witnesses as universally quantified binders is equivalent
  because the conclusion depends only on the initial fields and valuation rings.
- `∃ t : L, t ∈ W ∧ Transcendental K t` renders the integral transcendental parameter.
  `IntermediateField.adjoin K {t}` is exactly `K(t)` as a subfield of `L`.
- `Module.Finite (IntermediateField.adjoin K {t}) L` renders finiteness of `L/K(t)`.
- `W.comapInclusion (algebraMap (IntermediateField.adjoin K {t}) L)` is the already
  defined canonical inclusion from the restricted valuation ring to `W`.
  `Etale (Spec.map (CommRingCat.ofHom ...))` is EXACTLY the scheme-étale assertion
  in the node; no finite-map or separability conclusion was added.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (def-kun-separably-closed).
  The recorded `IsSepClosure` is the other notion in that dependency and is not needed here.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`
  (def-kun-topological-krull-dimension).
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`
  (def-kun-transcendence-degree).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (def-pc-integral-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`
  (def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (def-weil-etale-morphism).
- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field, a Mathlib match with no Lean record).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism).
- Existing ancillary API: `Scheme.functionField` in `Mathlib.AlgebraicGeometry.FunctionField`,
  `Scheme.fromSpecStalk` in `Mathlib.AlgebraicGeometry.Stalk`, `ValuationSubring` and
  `ValuationSubring.comap` in `Mathlib.RingTheory.Valuation.ValuationSubring`,
  `Algebra.adjoin`, `IntermediateField.adjoin`, `IntermediateField.FG`, `Transcendental`.
- `Sheaf.FieldTheory.AbhyankarInequality`: `ValuationSubring.comapInclusion` supplies the
  actual restriction map, and `ValuationSubring.abhyankar_inequality` is a proof input.
- The stated proof inputs are imported, without `public` when only the proof uses them:
  `Sheaf.RingTheory.HeightOneRealAbsoluteValue`, `Sheaf.RingTheory.ValuationAlgebraicHeight`,
  and `WeilConjectures.Mathlib.RingTheory.Etale.Field`.
  The generic scheme etale-composition/base-change tools and the Mathlib product-of-fields
  theorem are already available through the imported etale modules. Eight other proof
  inputs in Q30's split currently have neither a Lean record nor a Mathlib match; there
  are no modules to import for those yet. They are proof inputs, not notions needed to
  state this item, so no substitute definitions or extra assumptions are introduced.

Edge cases checked before writing:

- Trivial `R = K` and `W = L` are permitted: prime spectra have one element, and a
  separating parameter gives the finite separable field extension in the proof's base case.
- `KW ≠ L` is permitted. The centre condition is essential; it is not replaced by an
  arbitrary smooth model with no valuation centre.
- Positive characteristic and imperfect separably closed bases are allowed. In particular
  no assumption that closed-point residues equal `K` is imposed, and the proof plan uses
  an actual etale coordinate rather than Temkin's erroneous arbitrary-uniformizer claim.
- A nonseparated curve is not excluded; there is no properness or separatedness binder.
  Empty curves are already excluded by the node's integrality and dimension hypotheses.
- Parameter inversion preserves `K(t)` and the restricted ring; `t = 0` and constants are
  excluded by `Transcendental`, as required.
- There is one common ambient universe and no imposed equality between independently
  supplied universes. All the original fields, subrings and curve can be placed in a
  common universe. Every variable and universe is explicitly bound (`autoImplicit false`).

Searches made (the actual msearch outputs are retained in `searches.jsonl`):

- `msearch.py ... leanfinder`: "Over a separably closed valued field every valued smooth
  function field of transcendence degree one admits a transcendental parameter inducing
  an etale extension of valuation rings"; also "etale rational parameter for valued smooth
  function field". The returned standard-smooth and standard-etale-presentation statements
  do not supply the valued function-field theorem.
- `msearch.py ... loogle`: "ValuationSubring, AlgebraicGeometry.Scheme.functionField";
  zero matches, twice (the first batched tool output was omitted by the tool renderer,
  so the short query was repeated explicitly).
- `msearch.py ... grep`: "etale.*parameter|parameter.*etale|exists.*[Vv]aluation.*[Ee]tale";
  zero Mathlib hits.
- `msearch.py ... leansearch`: "transcendental parameter etale extension valuation rings
  smooth curve"; eight results about smooth/etale algebra and valuation torsion-freeness,
  no matching statement.
- `rg` of the upstream `WeilConjectures` tree by the blueprint id returned no match.
  Concept searches of upstream and `lean/Sheaf` by valued curves, valuation subrings,
  etale parameters and function fields found existing constituents and the stage-1
  parent's strict-semistable-uniformization module, but no statement of this theorem.
  The valuation-curve preparation and finite-normalization declarations concern models,
  not the rational parameter and etale restricted valuation-ring inclusion.

Source check: read https://arxiv.org/pdf/0707.3953v3, Theorem 2.1.8 and the finite-height
proof on printed pp. 12--13; the supplied Q30 report records its correction of the source's
arbitrary-uniformizer step, and this delivery keeps that correction in the proof plan.
No node statement fault or STATEMENT-DISPUTED issue is introduced by this interface.

## Second reading by Q115

This is the dispatcher's single-worker delivery, whose independent review is performed by
the maintainer as specified in the brief. I performed a further in-thread reading of the
node and complete module; this section does not claim a second independent agent.
I checked every binder and conjunct against the audit above and the generic-map triangle
against the actual Mathlib signatures. The initial compiler found that the intermediate
field's `.subtype` selected an inherited subsemiring interface; I replaced it with the
canonical `algebraMap (IntermediateField.adjoin K {t}) L`, which has exactly the field
structure required by the existing `comapInclusion`. No mathematical statement changed.
The node copy changes only `lean`; all fourteen proof steps and both dependency lists
remain identical to the base. No dependency module, extra node or statement correction
was needed. All definitions used have real existing data; the sole new theorem has `sorry`.

## Validation

Validation is through the prescribed `scompile.py` wrapper and `deliver2.py --no-push`;
no global build or direct git command is used. The expected postponed-proof warning is
allowed, and every other compiler diagnostic is repaired before delivery.

`scompile.py` compiled both the isolated sandbox module and its final library module
without diagnostics (2.7 s and 2.8 s). The first `deliver2.py --no-push` completed with
`OK (dry run)` at commit `57e6491b8e`, passing preflight and compilation. A report-only
correction changes the count of unstated proof inputs from nine to eight, matching the
fifteen-entry dependency list; the final dry run validates that report as well.
