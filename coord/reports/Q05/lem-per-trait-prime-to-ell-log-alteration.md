# Q05 stage-2 statement: prime-to-ell trait alteration

## Worker report

The live item already has the independently accepted Q108 stage-1 reconstruction
(2026-10-24, reviewer NT-cc-Q108-42bb887c4) and its repair note is resolved. The appended
Q108 handoff's claim that it remains unsplit is stale against the current node and
ledger 10:51 entry. This delivery performs the original assigned stage-2 task, which
remains in the stage-2 queue. It preserves that accepted proof, statement, source,
Mathlib searches, blueprint provenance and all maintainer metadata. It does not
resubmit stage 1, restore any withdrawn geometric theorem, or certify their proofs.

Files written: lean/Sheaf/AlgebraicGeometry/TraitPrimeToEllLogAlteration.lean; the item's
node copy; this report. The module states only
AlgebraicGeometry.exists_trait_primeToEll_log_alteration, with proof `sorry`.
Its docstring includes the complete current ten-step proof and each step's used node ids.
No definitions, auxiliary theorems, new nodes or dependency repairs are introduced.
The one library module has compiled cleanly with scompile.py in both sandbox and
library modes. All universes and variables are explicit; autoImplicit is false.

Hypothesis and conclusion audit (Lean expressions are from the delivered signature):

| Node clause | Lean rendering |
| --- | --- |
| Fix a prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| S is Spec of a DVR, including dimension one and not a field | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`, with structure morphism `s : X ⟶ Spec (.of R)` |
| Complete for the maximal-ideal topology | `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]` |
| Henselian, in the simple-monic-root sense | `[HenselianLocalRing R]`; its actual field is the monic simple-root lifting condition |
| Strict henselianity | `[IsSepClosed (IsLocalRing.ResidueField R)]` together with henselianity |
| Fraction field characteristic zero | `[CharZero (FractionRing R)]` |
| Positive residue characteristic | `(p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]` |
| ell invertible on S | `hell : IsUnit (ell : R)` |
| X integral | `[IsIntegral X]` (nonempty, reduced, irreducible) |
| X regular with locally Noetherian convention | `hregular : IsRegularScheme X` |
| X flat over S | `[Flat s]` |
| X finite type over S | `[LocallyOfFiniteType s] [QuasiCompact s]` |
| X quasi-projective, using a finite-dimensional projective-space immersion | `hqp : GabberModification.QuasiProjective s` |
| Finite dominant extension of traits T/S | existential `A`, its commutative-ring/domain/DVR structures, `t : Spec (.of A) ⟶ Spec (.of R)`, `IsFinite t ∧ IsDominant t` |
| Canonical trait log structure | existential uniformizer `π` with `maximalIdeal A = Ideal.span {π}`, and `M` identified with `divisorialLogPresheaf D(π).ι`, commuting with `divisorialStructuralMap` |
| fs log structures and log morphisms as in the specified dependency | `M : EtaleLogStructure ...`, `hfs : M.IsFineSaturated`, `Y : FineSaturatedLogScheme`, `g : EtaleLogHom Y ⟨Spec (.of A), inferInstance, M, hfs⟩` |
| Y integral and regular | existential `IsIntegral Y.scheme`, followed by `IsRegularScheme Y.scheme` |
| Y finite type over T and S | `LocallyOfFiniteType g.base ∧ QuasiCompact g.base`, and the same two predicates on `g.base ≫ t` |
| Y quasi-projective over T and S | `GabberModification.QuasiProjective g.base` and `GabberModification.QuasiProjective (g.base ≫ t)` |
| Charts N to P of the specified trait kind | the `FSLogChart g` covering every `y`, with `c.P ≃* Multiplicative (ULift ℕ)` and structural images the powers of the pulled-back uniformizer |
| Injective group map | `Function.Injective c.groupMap` |
| Finite torsion in the cokernel | `Finite (CommGroup.torsion c.cokernel)` |
| That torsion's order invertible on the chart source | `∀ v : c.V.left, IsUnit (Nat.card (CommGroup.torsion c.cokernel) : c.V.left.presheaf.stalk v)` |
| Smooth induced map to the monoid-ring fibre product | `Smooth c.comparison`; comparison is the canonical pullback lift from the chart-to-Spec maps, not an arbitrary arrow |
| An S-morphism f:Y to X | `f : Y.scheme ⟶ X` and `f ≫ s = g.base ≫ t` |
| Projective, in the finite-projective-space convention | `IsHProjective f` |
| Dominant | `IsDominant f` |
| Generically finite etale on a nonempty open of X | `∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) ∧ ...` |
| Positive function-field degree d prime to ell | `∃ d : ℕ, ... 0 < d ∧ ¬ ell ∣ d ∧ f.residueDegree (genericPoint Y.scheme) = d` |
| No purity conclusion | The conclusion ends with the degree condition. |

The prime residue-characteristic parameter introduces no new assumption: every
positive characteristic of a field is prime, and conversely `[Fact p.Prime]` excludes
zero. All mixed-characteristic traits in the node are covered. The DVR class is
Mathlib's local PID that is not a field; the standard DVR equivalence is precisely
the node's Noetherian local dimension-one domain with principal maximal ideal.
Adic completeness is expressed algebraically, without choosing a second topology.
The field at the source generic point maps canonically from the field at its image.
Dominance between integral schemes makes that image the target generic point;
residue fields there are their function fields. Thus `residueDegree` is exactly
[k(Y):k(X)], not the degree of an arbitrary selected field embedding. The finite
etale restriction already ensures this extension is finite and separable.

The canonical trait log structure is specified up to an isomorphism over its
structural map to regular functions. D(π) is exactly the generic open of a DVR.
The isomorphism identifies its sections, restrictions and structural inclusion
with the given divisorial construction; no object is selected from a mere
existence theorem. A uniformizer is existential data, equivalent to its availability
in every DVR, not an added input hypothesis. Its chart is fixed in all FSLogChart
neighbourhoods. This is the trait chart convention of the node; the existing
exists_uniformizer_chart and regular_logSmooth_monomial_chart interfaces confirm
that fixed-uniformizer presentations are available. We did not replace it by the
general log-smooth definition with possibly noninjective group maps.

Dependency declarations read and used:

- def-trf-fs-log-blowup: Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup,
  EtaleLogStructure, EtaleLogStructure.IsChart, EtaleLogStructure.IsFineSaturated,
  FineSaturatedLogScheme and EtaleLogHom. Their complete definitions were read.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.Smooth, applied to the canonical comparison.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  AlgebraicGeometry.Etale, applied to the actual restriction f|U.
- def-pc-integral-scheme: Mathlib.AlgebraicGeometry.Properties,
  AlgebraicGeometry.IsIntegral; its fields include nonemptiness.
- def-weil-regular-scheme: Sheaf.AlgebraicGeometry.IsRegularScheme,
  AlgebraicGeometry.IsRegularScheme = IsLocallyNoetherian and IsRegular.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  AlgebraicGeometry.Flat, equivalent to stalkwise flatness.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and QuasiCompact, LocallyOfFiniteType and QuasiCompact for each named structure map.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  IsClosedImmersion, used inside the projectivity and immersion definitions.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, Spec and Spec.map;
  the generic-open formula uses Scheme.ΓSpecIso.

Four already landed definition nodes are added to stmt_deps:

- def-trf-log-regular-pair: Sheaf.AlgebraicGeometry.LogRegularPair,
  AlgebraicGeometry.divisorialLogPresheaf and AlgebraicGeometry.divisorialStructuralMap.
  These prescribe the actual divisorial functions and their structural inclusion
  used to identify the canonical log structure on the trait. The module is now
  explicitly publicly imported, and the owning landed node is in stmt_deps.
- def-per-gabber-modification-data: Sheaf.AlgebraicGeometry.GabberModificationData,
  AlgebraicGeometry.GabberModification.QuasiProjective (lines 197--202). This is
  exactly the finite-projective-space relative definition over an arbitrary base.
  Its helper is already listed in the node's lean.declarations. The field-only
  upstream IsQuasiProjective would not apply to a trait, and is not substituted.
- def-per-fs-log-smooth-etale: Sheaf.AlgebraicGeometry.FSLogSmoothEtale,
  FSLogChart, groupMap, cokernel, comparison and EtaleLogStructure.chartToSpec.
  We use the existing chart construction, adding the node's literal injectivity
  and base N requirements inline, not defining a second log-smooth predicate.
- def-kun-projective: WeilConjectures.AlgebraicGeometry.Morphisms.Projective,
  AlgebraicGeometry.IsHProjective, exactly the closed finite-projective-space
  embedding convention (not the different projective-bundle convention).

The theorem's available recorded proof dependencies are private imports; the five
Q108 geometric inputs and the characteristic-zero Dedekind input have no Lean
attachments and none is fabricated. Statements, proof steps, proof_deps and their
accepted source route are unchanged. No SGA 4/4.5 or adic-duality source is used.

Searches performed using the prescribed msearch.py wrapper:

- LeanFinder: "Projective prime to ell generically etale alteration of regular schemes
  over complete strictly henselian mixed characteristic trait log smooth after finite
  trait extension". Eight hits concern ordinary standard smooth / etale ring maps
  and smoothness; no alteration assertion. The pinned Smooth/Etale definitions were read.
- Loogle: "IsDiscreteValuationRing, IsAdicComplete, HenselianLocalRing". Zero hits.
  The corresponding pinned class definitions were opened directly.
- Mathlib grep: "logSmooth|LogSmooth|semistable|Semistable|IsStrictHenselian|HenselianLocalRing"
  in AlgebraicGeometry. Zero hits. Existing HenselianLocalRing is in RingTheory,
  not an alteration theorem.
- LeanSearch: "Projective prime to ell log smooth alteration of a regular scheme over
  a complete strictly henselian mixed characteristic trait". Eight ordinary smooth,
  etale and formally smooth results, no matching statement.
- Project source searches for the exact item tag found no declaration. Concept searches
  found FSLogSmoothEtale, LogSmoothLogRegular (its InjectiveFSLogChart demands a
  torsion-free cokernel, which is too restrictive), LogSmoothInvertibleTorsionLogRegular,
  TraitLogSmoothUniformizerChart and RegularLogSmoothMonomialChart. These were opened;
  none states existence of the geometric alteration. Relative quasi-projectivity search
  found GabberModification.QuasiProjective and the field-only upstream definition.
- DAG search found def-sc-quasi-projective, restricted to curves over a field, and
  the already landed general helper in def-per-gabber-modification-data. Reuse of the
  latter avoids both a private copy and a new alias node.

Edge cases checked: ell prime excludes 0 and 1; X integral excludes the empty scheme;
X with empty closed fibre is allowed (no closed-fibre surjectivity condition is added).
There is no geometric-integrality hypothesis on X's generic fibre. Degree one is
allowed, and the target finite trait extension has no prime-to-ell degree condition.
Nonzero finite invertible torsion in the chart cokernel is allowed. The base chart
is N in the same universe using ULift. The nonempty open U is an arbitrary open,
not a preselected generic fibre or all of X. Integral Y is existential, with its
instance bound before genericPoint Y is used. The conclusion does not demand
semistability, a group action, Galoisness, purity, or a smooth underlying morphism.
No statement fault or STATEMENT-DISPUTED correction was found.

## Second reading by Q05

Self-review (the maintainer supplies the independent review): reread the live node,
its nine original statement dependencies, the added four landed interfaces and the
entire delivered signature. The table above pairs every hypothesis and clause.
The canonical log structure condition identifies its structural map, not just support;
the chart group map is injective with finite invertible torsion, not necessarily a
torsion-free cokernel. The projectivity predicate has the specified finite-space
meaning. Source and target structure maps commute over S, both finite-type and
quasi-projective conclusions are present, and the actual restriction to a nonempty
open is finite etale. The generic degree uses the canonical field map. All theorem
proof is sorry, and no definition is added. The node delta is only lean and the
four additional landed statement dependencies. The accepted Q108 proof remains
verbatim. Nothing in the five withdrawn Lean modules has been recreated or imported.

Validation: scompile.py clean in sandbox and library module modes; the final
prescribed deliver2.py dry run and push follow below in the tool transcript.

## Returned delivery repair, 2026-10-24

Repaired the sole H2 return on immutable head cd238e76631f: added the landed
`def-trf-log-regular-pair` node to the item's `stmt_deps` and added
`public import Sheaf.AlgebraicGeometry.LogRegularPair`. Its recorded declarations
`AlgebraicGeometry.divisorialLogPresheaf` and `divisorialStructuralMap` are precisely
the functions already used by the theorem's canonical-log-structure clause. Their
source, full signatures and implementations were reread. The dependency audit above
now names their owner. No copy of these constructions is introduced.

The retained returned packet differs from current main only in `lean` and
`stmt_deps`. The repair adds just the explicit import and missing dependency to that
packet, plus this report correction; the theorem signature and the ten-step proof
are unchanged. Current main still has the accepted Q108 split and no Lean record.
The prescribed wrappers will base the repaired delivery on current origin/sheaf-dag.
The reviewer accepted every other hypothesis, clause and edge case; all are retained.
