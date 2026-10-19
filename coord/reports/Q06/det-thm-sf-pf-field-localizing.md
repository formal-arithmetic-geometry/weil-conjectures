## Worker report

The item is already stated on the current `newtargets-dag` base by the merged Q99
module `Sheaf.Paper.RationalLocalizingProjectionFormula`, declaration
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMate_localizing_finiteExtension`
(and its paired finite-subextension-valued algebraic-closure theorem). I reused that
module and node record without changing the statement or dependency list. The module
also contains the canonical tensor-comparison and projection-mate helper declarations
owned by this item; all postponed theorem proofs are `sorry`, while definitions have
real data.

The declaration binds the prime ℓ and positive characteristic field k with
`ringChar k ≠ ℓ`, separated finite-type schemes X and Y over `Spec k`, a proper
k-morphism p, and the E/Q̄ℓ coefficient cases. Its hypotheses and endpoint clauses
are rendered by the explicit theorem binders and the two localizing-closure
conjuncts followed by `IsIso` of the canonical projection mate. The localizing
closure uses `constantModelBoundedConstructible`, and the two derived endpoints use
`lowerStar`, `upperStar`, and the relative derived tensor in the recorded module.

Dependencies read from their node records and source declarations were:
`upperStar` from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
`ringedProjectionMateExact` from `Sheaf.Paper.ProjectionMateExact`,
`derivedHom` and the relative derived tensor interfaces from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
`IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`, and the project-side
constructibility, localizing-closure, coefficient, and Q̄ℓ modules recorded in the
node. The current module imports exactly the framework needed for these declarations.

Edge cases checked against the statement and existing implementation include zero
objects, empty schemes, identity p, arbitrary shifts, unbounded inputs, E = Qℓ, and
ℓ = 2. No extra boundedness, finite-Tor, smoothness, discreteness, or completeness
hypothesis is introduced.

Searches already recorded in the node were reviewed: LeanFinder, LeanSearch, Loogle,
and grep found only generic tensor/adjunction infrastructure, with no duplicate
proper localizing projection-formula statement. The current module was recompiled by
`/home/ubuntu/weil-launcher-nt/scompile.py` and completed without diagnostics.

## Second reading by Q06

Author self-check on 2026-10-18, not a claim of an independent second agent:
opened the saved node, the complete saved module, the current published module,
and the blueprint statement `sk-thm-sf-pf-field-localizing.md`. The saved node
has no difference outside `lean`; the module differs from the accepted Q99
module only in the author line. No mathematical statement or construction was
changed during this repair.

The clause-by-clause check of both displayed theorems is:

- The standing prime and positive-characteristic field setting is expressed by
  `(ℓ : ℕ) [Fact ℓ.Prime]`, `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.
- Separated finite-type schemes over k are `{X Y : Scheme.{u}}`, their `Over`
  instances, and `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` for
  both structure maps. `p.IsOver` supplies the standing k-morphism convention;
  `[IsProper p]` is precisely the explicit properness hypothesis.
- The E case is `(E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]`
  `[FiniteDimensional ℚ_[ℓ] E]` with `Profinite.continuousCoefficientRingObj E`.
  The other theorem uses `Profinite.padicAlgClRingObj ℓ`. Read its upstream
  definition: sections take values in a single finite subextension, as required
  by `sk-def-sfb-qlbar-condensed`.
- `A` and `B` range over the unbounded `DerivedCategory` of internal modules on
  the small pro-etale sites over `condensedRingObj` on X and Y. `hA` and `hB`
  express exactly membership in `CategoryTheory.localizingClosure` generated
  by `constantModelBoundedConstructible`, namely Dbc rather than Dctf.
- The first conclusion conjunct puts `(lowerStar ... p).rightDerivedFunctor.obj A ⊗ B`
  in the target localizing closure. The second puts
  `Rp_*(A ⊗ (upperStar ... p).leftDerivedFunctor.obj B)` there. In this monoidal
  structure the tensor is the relative derived tensor of internal modules.
- The last conjunct is `IsIso (moduleObjectProjectionMate ... p A B)`.
  Opened its definition: it is `rightAdjointProjectionMap` for the recorded
  derived pullback/pushforward adjunction, evaluated at the unique
  representative-normalized comparison. `ModuleObjectTensorGeneratorFormula`
  uses extension units and the balanced tensor projection;
  `ModuleObjectDerivedTensorFormula` specifies each signed total summand and
  the derived counit equation. The comparison data are chosen from the named
  unique-existence theorem, rather than from an arbitrary isomorphism.
  Thus the arrow is the canonical projection map. Because the subcategory is
  full, the two membership conjuncts and ambient `IsIso` express exactly an
  isomorphism in that subcategory.

Read the dependency interfaces in their recorded modules, including
`AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
`constantModelBoundedConstructible` in
`Sheaf.Paper.CondensedConstantConstructibility`, `CategoryTheory.localizingClosure`
publicly imported through `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
`Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj` in the published
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, `upperStar`
in the recorded UpperLowerStar.Defs module, and `derivedHom` in the recorded
Derived.Hom module. The properness signature in Mathlib is
`class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f`;
universal closedness also supplies quasi-compactness. The general
`SheafOfModules.ringedProjectionMateExact` interface is not replaced or changed.
The coefficient notion is `Profinite.CondensedRing` from the recorded
`Sheaf.Topology.ProfiniteCondensedRing` module. The dc-setting dependency is
rendered by the explicit binders above, as its record prescribes.

Edge cases: zero A or B, empty X or Y, identity p, E = Qℓ and ℓ = 2 all remain
allowed. The membership binders impose no boundedness on A or B, and no shift
restriction. No mismatch or disputed statement was found.

Search evidence retained from the node (2026-10-16): LeanFinder query
“proper derived direct image projection formula on localizing closure of bounded
constructible rational sheaves” returned generic condensed/sheaf/derived functor
infrastructure; LeanSearch query “proper projection formula for unbounded
complexes generated by bounded constructible sheaves” returned generic complex
and cone projections; Loogle `CategoryTheory.Adjunction, CategoryTheory.IsIso`
returned generic adjunction equivalence lemmas; grep
`projectionFormula|projectionMap|rightDerivedLowerStar` recorded no match.
The repair's current `rg` search for `constantModelBoundedConstructible`,
`def localizingClosure`, `def upperStar`, `def derivedHom`, and coefficient
constructors in `lean/Sheaf` and the published framework confirmed the reused
interfaces. Direct comparison located the exact item statement in the current
Q99 module. These are retained searches and a current source self-check, not
new semantic-search runs.

Return repaired/validated: the reported immutable-head Sandbox0 timeout did not
recur with the saved packet. The prescribed initial `deliver2.py --no-push`
returned `OK (dry run): commit 1936c38973 passes the preflight and compiles`,
after checking the sandbox file and the published library file separately.
The Lean content is retained as instructed for a passing saved packet. The
only addition in this retry is this explicit required report self-check.


## Retained-packet retry, 2026-10-18

The required first action on this retry was a dry run of the saved packet:
`deliver2.py Q06 det-thm-sf-pf-field-localizing --no-push` returned
`OK (dry run): commit 408ab3538a passes the preflight and compiles; nothing pushed`.
Both `Sheaf/Stage2/Sandbox0.lean` and the library module compiled under the
unchanged 60-second limit. Thus the returned immutable-head timeout did not recur.

I retained the saved Lean and node record as directed. This retry's author
self-check reopened the complete saved module and current published module,
the item node and blueprint statement, the dependency records, the recorded
pullback, derived Hom, coefficient, constructibility, localizing-closure,
properness and ringed projection-mate declarations. The saved node differs from
the shared node only in `lean`; the module differs from the published Q99
module only in its author line. The clause matching and edge-case checks in
`Second reading by Q06` still apply. The finite-extension and finite-subextension
algebraic-closure cases each retain both endpoint-membership assertions and
`IsIso` of the normalized canonical counit mate. No Lean, mathematical statement,
dependency or construction was changed in this retry. This report addition is
an author self-check, not an independent-agent review.
