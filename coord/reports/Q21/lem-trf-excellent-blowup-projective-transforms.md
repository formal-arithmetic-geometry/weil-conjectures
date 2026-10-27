## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.ExcellentBlowupProjectiveTransforms`.
Its sole declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.excellent_blowup_projective_transforms`.
It is a theorem with the whole proof `sorry`. This repair adds two existing-definition
node records and cites the previously missing definition owners. No new Lean
data definitions, auxiliary postponed theorems, dependency replacements, or
mathematical statement corrections are needed. The existing accepted five-step proof is reproduced in the docstring.

Read the item, every statement dependency and its Lean/audit/Mathlib record, and
the corresponding source declarations and docstrings. The sheaf-Rees dependency
has no `lean` field but is closed upstream: its audit names `reesData` in
`WeilConjectures.AlgebraicGeometry.RelativeProj.Rees`, which is used directly.
Read Stacks `divisors.tex`, `lemma-blowing-up-affine` (0804), lines 8321–8352,
and `lemma-blowing-up-projective` (02NS), lines 8622–8658; and
`more-algebra.tex`, `lemma-finite-type-over-excellent` (07QU), lines 13372–13385.
The first source gives the actual homogeneous standard charts; the second gives
the multiplication quotient and its induced immersion into P(I); the third
supplies the excellence step. This is an auxiliary node, not a blueprint unit's
own statement. Its mathematical statement is unchanged.

Hypotheses and objects, clause by clause:

- Excellent integral Noetherian base S: `{S : Scheme.{u}}`, `[IsIntegral S]`,
  `[IsNoetherian S]`, and `hexc : ∀ V : S.affineOpens, IsExcellent Γ(S, V.1)`.
  The latter is precisely excellence on every affine coordinate ring. No
  separatedness, characteristic, dimension, or field hypothesis is imposed.
- Quasi-coherent finite-type ideal I: `I : S.IdealSheafData` and
  `hfinite : I.toModules.IsQuasiCoherentFiniteType`. The latter is the recorded
  conjunction `IsQuasicoherent ∧ IsFiniteType`, not a coherence or local-freeness
  hypothesis. `toModules` is the actual ideal sheaf, with its canonical inclusion
  `toModulesι` into O_S and affine section-image theorem `range_toModulesι_app`.
- The specified nonempty open U: `(U : S.Opens) (hU : Nonempty U)`.
  Being the unit ideal there is `hunit : Disjoint (U : Set S) (I.support : Set S)`:
  the ideal's support is V(I), so this says every stalk on U is the unit ideal.
- T and v are the dependency's actual `I.blowup` and `I.blowupMap`, not arbitrary
  witnesses. `I.reesData` is its canonical sheaf Rees graded algebra, and
  `I.relProjReesIso.inv` is the actual comparison from this blowup to its relative
  Proj. The immersion is composed with this particular comparison.

Conclusions, clause by clause:

- T excellent: `∀ V : I.blowup.affineOpens, IsExcellent Γ(I.blowup, V.1)`.
- T integral and Noetherian: `IsIntegral I.blowup ∧ IsNoetherian I.blowup`.
- v proper: `IsProper I.blowupMap`, using the recorded properness convention.
- v is an isomorphism over S minus V(I):
  `IsIso (I.blowupMap ∣_ I.support.compl)`.
- v birational: `Dense (I.support.compl : Set S)` and
  `Dense (I.blowupMap ⁻¹ᵁ I.support.compl : Set I.blowup)`, together with the
  immediately preceding isomorphism. These are dense open subsets on both sides
  and the restriction of this very morphism identifies them. Integrality makes
  both ambient schemes nonempty; their dense opens are therefore nonempty.
- The degreewise multiplication surjection: the existential `hqc` is a proof of
  quasi-coherence, and `q` is a morphism from the canonical
  `SymmetricAlgebraSheaf.gradedAlgebraData S I.toModules` to `I.reesData`.
  `Function.Surjective ((q.app V).gradedAddHom n)` asserts surjectivity in EVERY
  degree, including zero, on EVERY affine open. The displayed product equation
  says q takes a symmetric monomial in n ideal sections to their product times
  the degree-n Rees monomial. `q.app_algebraMap` fixes scalars, and its naturality
  field gives affine restriction compatibility. Thus q is determined by the
  degree-one inclusion; it is not an arbitrary surjection. The n=0 equation and
  the algebra-map field retain the unit and the degree-zero identification.
- Its induced closed immersion into P_S(I): the existential `hq` is only a proof
  of the irrelevant-ideal condition for this q. The specific morphism
  `I.relProjReesIso.inv ≫ GradedAlgebraData.relProjMap q hq` is required to be
  `IsClosedImmersion`, and its composite with the canonical symmetric relative
  Proj structural morphism is required to equal `I.blowupMap`. No arbitrary
  immersion or projective bundle is substituted for the induced one.
- Projectivity of v in the projective-bundle sense:
  `IsProjectiveBundle I.blowupMap`. This uses the recorded finite-type
  quasi-coherent-module convention; no vector-bundle hypothesis is added.
- Arbitrary H-projective X over S and arbitrary closed Y in its base change:
  `∀ (X : Scheme.{u}) (f : X ⟶ S), IsHProjective f → ...` quantifies over the
  finite-projective-space convention. For every scheme Y and every
  `i : Y ⟶ pullback f I.blowupMap` with `IsClosedImmersion i`, the conclusion is
  `IsHProjective (i ≫ pullback.snd f I.blowupMap)`. This is exactly Y to T,
  including an empty Y and any closed subscheme, without flatness assumptions.
- On every affine V = Spec A and every finite generating list, the binders are
  `(V : S.affineOpens) (r : ℕ) (a : Fin r → I.ideal V)` and
  `Ideal.span (Set.range (fun j ↦ (a j : Γ(S,V.1)))) = I.ideal V`.
  Subtype-valued generators record membership without choosing extra proofs.
  The supremum of their `Proj.basicOpen ... (reesX ... (a j).1 (a j).2)` equals
  top, so these ARE the standard charts and they cover the affine blowup.
  The global construction's `blowupι V` identifies that affine blowup with the
  inverse image of V (`isPullback_blowupι`, `blowupMap_preimage`).
- Each zero generator has `IsEmpty` for its standard open.
  Each nonzero generator has `IsDomain (AffineBlowup.chartRing ...)` and a
  specified isomorphism `e` from this actual standard open to the spectrum of
  that ring: `e.hom` is required to equal `Proj.basicOpenIsoSpec.hom` composed
  with `Spec.map` of the inverse of `homogeneousAwayEquivChart`. Its inverse
  followed by the open inclusion and `I.blowupι V` is required to equal
  `Spec.map homogeneousAwayToChart` followed by the standard `Proj.awayι` and
  the same `I.blowupι V`. Thus its ring and global-blowup embedding are pinned.
  The existing chart-ring definition is the A-subalgebra of A_a generated by
  x/a, x in I, rather than an invented quotient. The existential A-algebra map
  `ρ : Localization.Away (a j).1 →ₐ[A] FractionRing A` is injective.
  Localization's universal property uniquely determines ρ by its scalar equation;
  consequently restricting ρ to the existing chart subalgebra is precisely the
  inclusion A[I/a_j] into Frac A. The fraction field and localization use Mathlib.

Dependency declarations used (all reused; no private copies):

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`. Its finite coordinate type is equivalent to
  the finite projective-space convention, including the empty source case.
- `def-nagata-blowup-chart-ring`: `WeilConjectures.Blowup.Affine.ChartAlgebra`,
  `AlgebraicGeometry.AffineBlowup.chartRing`; also read its uniquely specified
  `homogeneousAwayEquivChart` comparison with the homogeneous standard chart.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `Scheme.IdealSheafData.blowup`, `blowupMap`, `blowupι`, `isPullback_blowupι`.
- `def-nagata-relative-proj`: `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`,
  `Scheme.GradedAlgebraData.relProj`, `relProjHom`, `relProjRestrictIso`.
  The canonical affine-basis construction is used, as the dependency's lean.note
  directs, without selecting an independent gluing realization.
- `def-nagata-sheaf-rees-algebra`: its closed upstream audit record,
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Rees`,
  `Scheme.IdealSheafData.reesData`, `relProjReesIso`, and the recorded homogeneous
  multiplication and degree-zero structure.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.snd`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-trf-projective-bundle-morphism`:
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, `AlgebraicGeometry.IsProjectiveBundle`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, used through `Mathlib.AlgebraicGeometry.Noetherian`'s
  `AlgebraicGeometry.IsNoetherian` and `IsLocallyNoetherian`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `Scheme.Modules.IsQuasiCoherentFiniteType`; Mathlib's `IsQuasicoherent` and
  `IsFiniteType` are exposed through this recorded module.

Further construction imports give the canonical symmetric graded algebra,
`GradedAlgebraData.relProjMap` and `IrrelevantLE`, the ideal module, chart rings,
and the fraction field. The statement imports publicly expose the dependency
modules. Proof-only imports retain the currently stated approved proof plan:
`IsExcellentFiniteTypeLocalization`, `ExcellentSchemeAffineCover`,
`WeilConjectures.Blowup.Proper`, `WeilConjectures.Blowup.Complement`, and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace` (its `isPullback_map`).
The three sfb proof lemmas currently have no Lean record; no nonexistent modules
are imported and none are needed just to type this statement. Closed-immersion
base change/composition and finite-type Noetherianity are already available from
Mathlib; their DAG leaves have no separate project module.

Edge cases checked before writing and again after elaboration:

- The empty base is excluded by the node's integral hypothesis, not a new binder.
- The zero ideal cannot be the unit on a nonempty open of an integral scheme;
  the theorem does not silently substitute the stronger hypothesis I nonzero.
- I = O_S is allowed, and the complement is all S. The blowup is S itself.
- Empty affine opens ARE included in the chart quantifier: their section rings
  are zero, so every generator is zero and every standard chart is empty.
- Zero and redundant generators are allowed. A zero generator's chart is empty;
  no nonzero-generator hypothesis is imposed on the entire generating list.
- r = 0 is allowed. On an empty affine the supremum is bottom = top in the empty
  Proj; on a nonempty affine it cannot generate this nonzero ideal. There is no
  Nonempty or positive-length binder excluding either situation.
- Degree n = 0 retains the unit and fixes base scalars; positive degrees retain
  multiplication in the same Rees algebra, not merely existence of a quotient.
- X and Y may be empty, and i may be any closed immersion. No integrality,
  strict-transform condition, finite-presentation, or flatness is added for them.
- Arbitrary scheme universe u is explicit. All variables are explicitly bound;
  `autoImplicit` and `relaxedAutoImplicit` are false.

Searches actually run with msearch.py, recorded in searches.jsonl:

- LeanFinder: “The blowup of an excellent integral Noetherian scheme is excellent
  integral proper birational projective and has standard fraction charts”:
  eight hits, primarily normalization and affine Proj properness. None states
  this conjunction or the canonical symmetric immersion plus transform clause.
- Loogle: `"blowup", "projective"`: zero hits.
- Mathlib grep: `IsExcellent|[Bb]lowup|[Bb]lowUp`, AlgebraicGeometry: zero hits.
- LeanSearch: “Blowup of an excellent integral scheme is excellent integral and
  projective”: eight hits, integral-scheme and properness definitions, not this lemma.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for excellence, blowup,
  Sym-to-Rees and the full proposed declaration name; grep of the upstream root
  for this node id: no existing exact statement. The existing
  `isIntegral_blowup_and_isProjectiveBundle` proves only two of the clauses and
  assumes a nonzero ideal. `blowup_rees_symmetric_presentation` supplies a related
  normalized quotient but not excellence, the immersion, birationality or the
  closed-transform result. Both were read and not duplicated as definitions.

No STATEMENT-DISPUTED issue or node fault was found. Server scompile.py compiled
this file cleanly (2.4 seconds); its attempted local compile reported ENOSPC,
then the wrapper's server fallback succeeded. Final delivery checks follow below.

## Second reading by Q21

This is a separate rereading by the same dispatcher worker; no independent worker
or agent was started, as the assignment prohibits delegation. The maintainer's
independent review is still required. I reopened the node and complete Lean file
and compared the individual binders and conjuncts listed above.

The rereading found that a preliminary chart quantifier unnecessarily requested
nonempty affine opens. I removed that binder: empty affine opens now occur in
exactly the same quantifier, and their zero rings have only the empty-chart case.
The initial compile also caught the incorrect prefix `AffineBlowup.reesX`;
`reesX` belongs directly to `AlgebraicGeometry`, and all occurrences were fixed.
The final statement includes BOTH density clauses with the restriction of v,
so birationality is a property of v, not an unrelated isomorphism of function
fields. It uses the actual q-induced map, retains surjectivity separately in each
degree, fixes q on all monomials including the empty product, and keeps the
structural composite equal to v. The transformed projectivity quantifier has no
nonempty/flat/strict-transform restriction. The standard-chart cover, zero charts,
domain rings and their uniquely determined embedding into Frac A all remain.
No correction of the mathematical statement or extra hypothesis was required.
The returned metadata repair adds the two definition-owner records described below.

Validation: `deliver2.py Q21 lem-trf-excellent-blowup-projective-transforms --no-push`
returned `OK (dry run): commit c4dfd2eb153 passes the preflight and compiles;
nothing pushed`. Its staged set contains exactly this report, the item's node
with its lean-only change, and the sole Lean module. The final module compiles
in both sandbox and library positions under the standard per-file limit.


## Repair of return on 3ae79de01e41

1. **H2, missing statement dependencies.** Compared the retained sandbox module
   and node with the returned head described by the maintainer and with current
   main's node and declarations (read-only; no direct Git operation). Current
   main has no Lean record for the item. The retained mathematical statement
   and five proof steps are preserved. Added the landed definition nodes
   `def-trf-canonical-symmetric-graded-algebra` and `def-nagata-rees-piece` to
   `stmt_deps`, for `gradedAlgebraData` and `reesGrading`, respectively. Their
   modules now have explicit public imports. Added the two existing-definition
   records described under New nodes for `relProjMap`/`IrrelevantLE` and `reesX`.
   Also cited landed `def-nagata-homogeneous-away-to-chart` and
   `def-nagata-affine-proj`, which supply the canonical homogeneous-fraction map
   and the standard-open comparison used to repair H3. No theorem node was
   passed off as a definition owner. The owner records reuse existing upstream
   data definitions without rewriting them. Only `lean` and the permitted
   additions to `stmt_deps` change on the existing item; the delivery wrapper
   rebases these sandbox changes onto current main.
2. **H3, chart comparison not pinned.** Removed the bare
   `Nonempty (basicOpen ≅ Spec chartRing)` clause. It is now an existential
   isomorphism with an explicit equation for its forward morphism:
   `e.hom = Proj.basicOpenIsoSpec.hom ≫ Spec.map θ.symm`, where θ is the
   existing `homogeneousAwayEquivChart`. This is the canonical fraction
   comparison, not merely an abstract ring isomorphism. Added the equation
   `e.inv ≫ D₊(at).ι ≫ I.blowupι V = Spec.map θ ≫ Proj.awayι ≫ I.blowupι V`,
   using the underlying `homogeneousAwayToChart` ring homomorphism on the
   right. It identifies the same chart inside the actual global T. The
   equation's direction is checked: θ maps Away to chartRing, hence Spec θ
   maps Spec chartRing into Spec Away. All other clauses and hypotheses are
   unchanged. The existent isomorphism is now fully determined by its hom.

The revised theorem signature is copied verbatim into `lean.statement`.
The mathematical node statement remains unchanged; this is a repair of its
formal rendering and ownership metadata, not a source-based statement correction.

## New nodes

`def-trf-relative-proj-induced-morphism` records the existing upstream
`AlgebraicGeometry.Scheme.GradedAlgebraData.relProjMap` and its
`IrrelevantLE` condition, in
`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality` (lines 43–45,
59, 77–95). Source: Stacks `constructions.tex`, Tag 07ZG,
`lemma-morphism-relative-proj`, with the affine chart construction in
`lemma-morphism-proj`. It defines the actual glued map, using inverse images
of homogeneous primes and the induced equal-degree fraction maps, in the
case the irrelevant condition makes it defined everywhere. The node cites
`def-nagata-relative-proj` for its inputs. `prop-nagata-relative-proj-functoriality`
records its properties, but there was no definition node owning this map.
Blueprint search `induced relative Proj` returned zero; the fuller
`relative-proj-functoriality` search returned the theorem and two specialized
base-change/restriction constructions, not this definition. Exhaustive scans
of definition-node JSONs for relProjMap and IrrelevantLE returned no owner.
The new record is `existing: true`; it creates no Lean file.

`def-trf-rees-degree-one-element` records the existing upstream
`AlgebraicGeometry.reesX`, in
`WeilConjectures.Blowup.Affine.ReesGrading` (lines 51 and 204–215).
Source: Stacks `divisors.tex`, Tag 0804, `lemma-blowing-up-affine`, proof,
which explicitly denotes a viewed in Rees degree one by a^(1). The definition
is the polynomial at, applies also to a = 0, and cites the existing Rees
algebra and Rees-piece definition nodes. The theorem node
`lemma-nagata-rees-degree-one-element` is recorded in `blueprint.same_as`:
it asserts the degree and simp properties but is not a definition owner.
The maintainer expressly requested this definition owner despite that theorem
node, and no new construction or duplicate Lean constant is introduced.
Blueprint search `Rees degree one` returned zero; the general `Rees` search
found that theorem and the already reused algebra/piece definitions. Exhaustive
scans of definition-node JSONs found no reesX owner. This record is also
`existing: true`, with no new Lean file.

Both definition nodes have the item's current chapter and unit, its nearest
blueprint ancestor `lem-trf-local-term-locality`, and the item's via path with
the item prepended. Their statement dependencies are exactly their bracketed
citations; proof lists are empty. The source declarations, full signatures,
ambient variables and defining formulas were read, rather than reconstructed.

Additional searches actually run for these records via msearch.py:

- LeanSearch `A graded algebra morphism satisfying the irrelevant ideal
  condition induces a morphism of relative Proj schemes`: eight results,
  affine Proj.fromOfGlobalSections and related maps; no relative-Proj map.
- Loogle `"relProjMap"`: zero results. Mathlib grep `relProjMap|IrrelevantLE`:
  five results, all containing affineOpenCoverOfIrrelevantLESpan, not either
  searched definition. Upstream rg finds the exact Functoriality declaration;
  Sheaf rg finds consumers, which reuse it rather than defining another map.
- LeanSearch `The degree one element a times t in the Rees algebra of an
  ideal`: eight results, including reesAlgebra, its monomial-membership and
  generation theorems. Loogle `"reesX"`: zero; Mathlib grep `reesX`: zero.
  Upstream rg finds exactly the recorded ReesGrading construction, and Sheaf
  rg finds its consumers. No new definition is written over those results.

The exact executed queries, result lists, digests and dates are copied from
this item's searches.jsonl into each new node's mathlib_searches.

## Second reading of repair by Q21

Reread the complete revised file, all three delivered node records, and both
source definitions against the two returned points. The owner gap is closed:
all four declarations named in H2 have cited definition owners, with both
new owners attaching only existing upstream definitions. The extra chart APIs
are now cited through the existing affine-Proj and homogeneous-away definition
nodes. In H3 the comparison's forward map is the existing canonical map, and
its inverse is pinned inside T via blowupι. No arbitrary choice of chart-ring
isomorphism remains. Checked the direction of Spec on θ and θ inverse, all
bound variables and universes, and the zero generator/empty affine/r=0 cases.
The new equations are inside the nonzero-generator branch; the zero charts
remain empty and impose no nonexistent domain hypothesis. The other clauses
are exactly those accepted by the returned independent reading. As required
by the dispatcher brief, no other agent was started; this is a separate pass
by the same worker, with the maintainer's independent reading still to follow.

Repair validation: the revised module passed standalone scompile.py in sandbox
and library positions (library invocation 3.8 seconds). The required repaired
`deliver2.py ... --no-push` completed with
`OK (dry run): commit 440bf74834f passes the preflight and compiles; nothing pushed`.
It also checked the existing declaration names of both new definition records.
The staged set is exactly the report, the repaired item node, the two new
existing-definition nodes, and the single revised module.
