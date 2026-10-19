## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves` defines
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHomOfPreserves`
and its fixed-first-variable inclusion comparison
`boundedConstructibleHomOfPreservesObjCompatibility`. Both definitions have real
construction data and contain no sorry. The additional prerequisite module states the
finite-extension preservation cases with a single named theorem proof left as sorry. The natural statement is unchanged.

The main-20261015 blueprint source `sk-def-sfb-dc-restricted-functors/def-sfb-dc-hom.md`
and the parent unit's restriction paragraph were read. The construction is the ambient
bifunctor restricted in both arguments, with exactly the supplied preservation hypothesis.

Hypothesis and clause correspondence:

- Distinct primes ell and p: `(ℓ : ℕ) [Fact ℓ.Prime]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.
  Here p is the characteristic `ringChar k`, rather than an extra name for the same integer.
  Primality implies positive characteristic.
- The field is `{k : Type u} [Field k]`. The separated finite-type k-scheme is
  `(X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]`. Finite type is locally finite type plus quasi-compactness.
- The commutative condensed ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`.
  This is the ring-object presentation in the dependency. No topological presentation of
  the arbitrary Λ is required. The inverse image ring Λ_X is the existing
  `AlgebraicGeometry.ProEtale.condensedRingObj Λ X.left`.
- D is the ordinary unbounded derived category of internal module objects over this ring,
  the domain/codomain of the recorded `derivedHom Λ X.left`. The objects of C are the
  recorded `BoundedConstructible (condensedRingObj Λ X.left)`; its inclusion is
  `(boundedConstructible (condensedRingObj Λ X.left)).ι`. These reuse the existing finite
  stratification, locally finitely presented cohomology and boundedness predicates, with
  no derived completeness condition.
- The assumed preservation is the parameter `h : ∀ K L : BoundedConstructible ...,
  boundedConstructible ... (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)`.
  Quantifying over C is precisely quantifying over ambient objects with proofs of
  bounded constructibility. It neither demands preservation for arbitrary Λ without h
  nor restricts Λ to the ell-adic cases.
- The curried result type `Cᵒᵖ ⥤ C ⥤ C` expresses the bifunctor `Cᵒᵖ × C ⥤ C`.
  `Functor.uncurry` and `Functor.curry` are the canonical conversion between these forms.
  The first inclusion is `.ι.op` and the second is `.ι`, so the first argument is
  contravariant and the second covariant.
- The object assignment is the ambient value, lifted with `fun KL ↦ h KL.1.unop KL.2`.
  `ObjectProperty.lift` stores this value with its proof, without choosing a replacement
  object or deriving another operation.
- The morphism assignment is the ambient bifunctor map after the product of inclusions.
  Thus u:K'→K and v:L→L' induce H(u,v). Full-subcategory maps are `homMk` of the
  ambient map, and identity/composition laws are inherited from Mathlib's existing
  functors. No arbitrary map or extra functoriality assumption occurs.
- For every fixed K, `boundedConstructibleHomOfPreservesObjCompatibility` has type
  `(H_C.obj (op K)) ⋙ ι ≅ ι ⋙ ((derivedHom Λ X.left).obj (op K.obj))`.
  This is the comparison for the stated equality of composites: both act by the same
  ambient value and map, with the canonical unit/identity normalizations from currying.
  It is built by `Functor.curryObjProdComp` and the inverse unit of `Functor.currying`,
  whiskered by inclusion. Each constituent has identity components, hence so does the
  comparison and its inverse. Full-subcategory proof fields carry no mathematical data.
- The three coefficient examples are the imported preservation prerequisite, now bound
  to the generalized finite-extension theorem and the existing algebraic-closure
  instance as described below. The definition itself
  uses h, so it is independent of the proof of this finiteness theorem.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the published module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  Its over-field setting uses the displayed prime/field/Over/finite-type/separated
  binders. Its compactification choice is not used by an internal Hom construction.
- `sk-def-sfb-condensed-ring`: the current `Sheaf.Topology.ProfiniteCondensedRing`
  reexports `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, which
  exports `Profinite.continuousCoefficientRingObj` and
  `Profinite.isCommMonObj_continuousCoefficientRingObj`; these constructors provide the
  examples, while the arbitrary ring is kept as its sheaf/MonObj/IsCommMonObj data.
  The recorded source and its universe-generalized constructor were read.
- `sk-def-sfb-bounded-constructible`: the current recorded
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly retains
  `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible` and the
  existing `boundedConstructible`, `BoundedConstructible`, and
  `mem_boundedConstructible_iff`. Its weak-Serre triangulatedness theorem is not needed
  to restrict a bifunctor to a full subcategory.
- `sk-def-sfb-derived-tensor-hom`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`. Its full signature and docstring
  define exactly the internal Hom of the ambient derived relative tensor structure.
- `lem-sfb-dc-hom-preserves`: `Sheaf.Paper.BoundedConstructibleHomFiniteness`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHom_finiteExtension`,
  together with the imported published `isMonoidalClosed_boundedConstructible` for qlbar.
  The existing instance, its finiteness coefficient class and
  `ObjectProperty.IsMonoidalClosed` were read, including the single field `prop_ihom`.
  See the dependency binding below.
- `sk-def-sfb-qlbar-condensed`: its closed upstream audit names
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
  Their docstrings and definitions were read: sections are continuous maps into a
  finite subextension, identified pointwise, and not all maps into the algebraic
  closure with its valuation topology. These are also the algebraic-closure case of
  the imported finiteness coefficient class. No duplicate qlbar definition is needed.

Edge cases checked before writing: the empty scheme is allowed by all binders; the
zero complex and zero maps use the same lift, without an assumed nonzero object;
noetherianity, regularity, smoothness, tensor preservation and a monoidal structure
on C are not required as extra hypotheses. For Λ=Z/4 on a geometric point of
characteristic 3, the unbounded Ext of Z/2 shows why the preservation hypothesis
cannot be omitted; this conditional definition makes no such omission. Other
coefficient rings satisfying preservation remain allowed. The identity and composite
maps are inherited for arbitrary u,v, not only for identity morphisms. The small
pro-etale site and ambient module category keep their existing universes; no equality
of site object and morphism universes is imposed. The characteristic-p field and
scheme both live in their common scheme universe, as the imported framework does.

Searches actually run:

- `msearch.py` LeanFinder: "Restriction of derived internal Hom to bounded constructible
  complexes with condensed coefficients" returned eight light-condensed/internal-Hom
  hits, including `LightCondensed.ihomPoints`; none is the required restriction.
- `msearch.py` Loogle: "CategoryTheory.ObjectProperty.lift,
  CategoryTheory.MonoidalClosed.internalHom" returned zero hits. This combined query
  is not evidence that the individual declarations are absent: both were read locally.
- `msearch.py` grep: "boundedConstructibleHom|boundedConstructible.*derivedHom|
  derivedHom.*boundedConstructible" returned zero Mathlib hits.
- `msearch.py` LeanSearch: "Restrict a bifunctor to a full subcategory assuming preservation
  of its object property" returned `ObjectProperty.lift`, `.ι`, and related general
  full-subcategory APIs; these are reused.
- Direct rg in the slopmaster2 source for the item ID returned no match; the same source,
  the side framework, and `lean/Sheaf` were searched for bounded-constructible Hom and
  derived Hom restrictions. The side framework contains the named upstream restriction.
  Current server source was read with `scompile.py --source`: unlike its stale local
  version, it only permits `IsEllAdicFinitenessCoefficient`. It does not provide this
  arbitrary-coefficient conditional interface. The older local source also cannot be
  attached: it uses a sorried preservation theorem for every condensed ring.
- Direct rg in the source, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `boundedConstructibleHomOfPreserves` / `restrictedBoundedConstructibleHom` returned
  no existing declaration. The chosen name therefore does not duplicate a declaration.

No new notions or DAG nodes are introduced, and there is no statement correction or
STATEMENT-DISPUTED flag. The difference between local and published upstream sources
was resolved by reading the published source through the authorized wrapper.

## Dependency modules

`lem-sfb-dc-hom-preserves` now records the published
`Sheaf.AlgebraicGeometry.BoundedConstructibleHomPreservation.boundedConstructible_hom_closure`
(the declaration namespace is `AlgebraicGeometry.ProEtale.CondensedRing`). The published `isMonoidalClosed_boundedConstructible` could supply the three
cases only in its own coefficient encoding: the `IsEllAdicFinitenessCoefficient`
constructors accept finite-extension coefficient carriers only in Type 0. This is
insufficient for the universe-generalized `continuousCoefficientRingObj` recorded by
the condensed-ring node, so attaching that instance alone would exclude coefficients.

The module `Sheaf.Paper.BoundedConstructibleHomFiniteness` supplies the missing
finite-extension interface as `boundedConstructibleHom_finiteExtension`. It has exactly
the same prime-characteristic, finite-type separated k-scheme setting as the item.
`E : Type u`, `NormedField E`, `NormedAlgebra ℚ_[ℓ] E`, and `FiniteDimensional ℚ_[ℓ] E`
specify a finite extension with the extending absolute value and topology.
`O : Subring E` and `hO : ∀ x, x ∈ O ↔ ‖x‖ ≤ 1` name exactly O_E by its definition,
not an additional regularity hypothesis or an arbitrary coefficient subring.
The two conjuncts state internal-Hom preservation for the existing condensed rings
of E and O respectively, pulled back by the same `condensedRingObj` as the main item.
`ObjectProperty.IsMonoidalClosed` has just the preservation field and does not impose
monoidal closure of the subcategory. Thus the result says exactly the two
finite-extension clauses. It is a theorem with sorry, not hollow construction data.
Its docstring carries the current DAG finite-truncation proof, with an explicit
coefficient-isomorphism transport for carriers in the scheme universe.

The qlbar clause uses the existing published `isMonoidalClosed_boundedConstructible`
with its `IsEllAdicFinitenessCoefficient.algebraicClosure` instance and the recorded
finite-subextension-valued `Profinite.padicAlgClRingObj`. That case has no coefficient
carrier size defect and is not restated. The dependency record lists both the new
finite-extension declaration and this imported existing declaration. Only its lean
field changes. There are no new DAG nodes. All four currently recorded proof-dependency modules are imported without public
visibility. Their role stays in the postponed proof; no prerequisite is added to the
theorem signature.

The initial preflight found that its signature reader starts with `def`, dropping
the `noncomputable` modifier. The main metadata was corrected to its parser's exact
signature from `def` to `:=`, without changing the definition.

The added prerequisite declaration name was searched in slopmaster2, `lean/Sheaf`,
and `dag/lean_names_upstream.json`; no existing declaration matched. The exact
blueprint source of `lem-sfb-dc-hom-preserves` was also reread against the new statement.

## Repair of the returned immutable head

The saved packet's first `deliver2.py Q35 def-sfb-dc-hom --no-push` reproduced the
return: the obsolete proof import `Sheaf.Paper.IntegralHomReduction` fails with universe
constraints and cascading missing identifiers. No delivery was pushed.

The current main DAG has meanwhile replaced the integral-reduction proof of
`lem-sfb-dc-hom-preserves` with finite truncation devissage. The repair removes the old
proof imports, including `IntegralHomReduction`, and imports exactly the four current
recorded proof modules: `Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle`,
`Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage`,
`Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated`, and `Sheaf.Paper.SfHomTriangulated`.
The prerequisite docstring now gives that proof and explicitly explains transport from
universe-generalized finite extensions to small isomorphic coefficient fields and back.
The prerequisite node copy was refreshed from current main, keeping its current proof,
proof dependencies, proof-origin and review metadata verbatim; only `lean` changes.
Its updated `lean.note` describes the current recorded interface's Type 0 limitation.
The main two definitions and both natural statements are unchanged.

The initial compile after this repair passed the `SfHomTriangulated` private overlay,
then returned infrastructure retry (exit 75): the published live library lacks
`Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle.olean`. The compile diagnostic
explicitly says this is a stale live build, not a delivery fault. Validation is retried
through the prescribed wrappers; no live file, artifact, launcher tool or timeout is edited.

## Repair self-check

Read the retained module and its two declarations against every clause of
`def-sfb-dc-hom` and the current blueprint unit. The preserved construction uses the
ambient bifunctor's actual object and map data through `ObjectProperty.lift`; its comparison
uses the standard currying isomorphisms, whose components are identities. No coefficient
restriction was added to the main definition, and no preservation theorem is used as
construction data. The prerequisite still has one named sorried theorem and no hollow
definition. Read current coefficient constructors through `scompile.py --source`:
`IsEllAdicFinitenessCoefficient.continuous` and `.unitBall` still accept only Type 0,
whereas `continuousCoefficientRingObj` accepts Type u. The new prerequisite remains a
needed interface generalization, and qlbar retains the existing finite-subextension
coefficient construction. No independent second-reader claim is made by this worker;
the maintainer independently reviews the delivery.

Final validation in this repair turn: the second prescribed dry run reproduced the same
missing published `BoundedConstructibleHomSingle.olean` infrastructure diagnostic and
pushed nothing. Both node copies were compared against current main: each changes only
`lean`. Both recorded signatures match their files verbatim, all Lean lines are at most
100 characters, the main module contains no sorry and the prerequisite contains exactly
one named theorem with a whole-proof sorry. The compiler cannot reach final validation
of either delivered file until the missing live build artifact is published.

## Resumed repair validation, 2026-10-18

Inspected the saved report and both delivered modules before the prescribed first
dry run. `deliver2.py Q35 def-sfb-dc-hom --no-push` again stopped before checking
the delivered declarations: the published live build lacks
`Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle.olean`. The independent
`scompile.py Q35 def-sfb-dc-hom` invocation with both files reproduced this same
`INFRASTRUCTURE RETRY (stale live olean)` diagnostic and exited 75.

Compared both saved node copies with the current shared main DAG: each differs
only in `lean`, and the prerequisite still has the four finite-truncation proof
dependencies imported in its module. Read the resolved stage-1 repair note for
`lem-sfb-dc-hom-preserves` and the main-20261015 definition source; neither asks
for an additional change to this conditional restriction. The earlier universe
errors were in the removed obsolete proof import. No Lean statement was changed
in this retry and no successful compilation or delivery is claimed. The missing
published artifact is outside this worker's writable sandbox.

## Infrastructure retry, 2026-10-18 10:43 UTC

The prescribed first dry run of this resumed turn again failed before checking the
saved declarations: `deliver2.py Q35 def-sfb-dc-hom --no-push` reported
`INFRASTRUCTURE RETRY (stale live olean)` for the missing published
`Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle.olean`. A separate
`scompile.py Q35 def-sfb-dc-hom` invocation supplying both delivered Lean files
confirmed the same failure and exited 75. Neither operation pushed a delivery.

Compared the two saved node JSON files against current shared main: both differ
only in `lean`. The prerequisite's four proof imports still match the four current
`proof_deps`; in particular the missing module is the recorded proof prerequisite
`lem-sfb-dc-hom-single`, so dropping it would violate the required proof-import
contract. Both delivered Lean files retain lines of at most 100 characters, and
the obsolete `IntegralHomReduction` import remains absent. No Lean or node change
was justified by this infrastructure diagnostic. The live build and launcher tools
are read-only for this worker; the saved packet is retained for the next retry.

## Repair of the transitive-module workaround

A private-overlay workaround copied the four transitive proof-dependency modules whose
olean artifacts were absent from the live build. They compiled, but preflight correctly
rejected them because these nodes are not in this item's deliverable dependency closure
on the current base (and `SfHomTriangulated` already exists on the base). The workaround
was removed. The repaired prerequisite retains the current theorem statement and no
additional module or node is delivered; its postponed proof imports are intentionally
left to the maintainer's next global build, as allowed for a landed dependency module.
The remaining packet contains only the item module and the prerequisite module.

The final delivered prerequisite module contains only the public imports needed to
elaborate its statement. The four finite-truncation imports are proof-only and were
removed from this stage-2 statement packet after the base preflight rejected supplying
transitive modules outside the item's closure; the theorem proof remains `sorry` and
the node's recorded proof plan is unchanged on the base. The final packet's two Lean
files compile cleanly with the prescribed wrapper.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
