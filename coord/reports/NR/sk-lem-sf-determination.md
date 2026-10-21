## Worker report

The module `Sheaf.Paper.ConstructibleLocalizingDetermination` states
`AlgebraicGeometry.ProEtale.isIso_app_of_constructibleFiniteTor`, with proof `sorry`.
It also supplies the globally named instance
`AlgebraicGeometry.ProEtale.localizingClosureProEtale_isTriangulated`, by projecting
an already recorded existence theorem; this is real proof data with no new sorry.
The instance installs the existing ambient inherited triangulation, so the theorem
requires no arbitrary triangulation or assumption that the closure is triangulated.

Clause-by-clause correspondence:

- “Lambda admissible”: `(ℓ : ℕ) [Fact ℓ.Prime]`, the actual condensed ring
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`, its `[MonObj Λ]`
  and `[IsCommMonObj Λ]` ring structures, and
  `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`. Admissibility is kept even though
  the generic mathematical argument works for more general coefficients.
- Schemes X and Y: `(X Y : Scheme.{u})`. There is no qcqs, nonempty, finite-type,
  or separated hypothesis. The recorded localizing-closure definition already fixes the canonical
  Grothendieck-category derived localizations, with Hom universe `u + 1`.
  No extra `HasDerivedCategory` model parameter is imposed.
- The two functors have exactly the restricted domain and codomain:
  `(localizingClosureProEtale Λ X).FullSubcategory ⥤
   (localizingClosureProEtale Λ Y).FullSubcategory`.
  There are no ambient-domain extensions or completeness hypotheses.
- “Exact functors”: `[F₁.CommShift ℤ] [F₂.CommShift ℤ]` and
  `[F₁.IsTriangulated] [F₂.IsTriangulated]`. Mathlib derives additivity from
  triangulated exactness. The full-subcategory triangulations are inherited by
  Mathlib `ObjectProperty.IsTriangulated`, obtained from the instance above.
- “Preserving direct sums”: for each functor,
  `[∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₁]` (and F₂).
  This is preservation for arbitrary families in the fixed small indexing universe,
  including the empty family. No assumption of preserving other colimits is added.
- “Natural transformation of exact functors”: `(η : F₁ ⟶ F₂)` and
  `[NatTrans.CommShift η ℤ]`. The latter supplies the shift-compatible meaning
  explicitly specified by the node's proof; naturality alone is not substituted.
- “For every K in Dctf(X,Lambda)”: `hη` quantifies over source objects K whose
  ambient object satisfies `constantModelBoundedConstructible Λ X K.obj ∧
  DerivedCategory.finiteTorAmplitude _ K.obj`, and asserts `IsIso (η.app K)`.
  This is precisely the predicate used in the recorded localizing definition.
  All ambient generators are in this full subcategory: evaluate its defining
  intersection on any containing predicate. Thus quantifying generators inside
  the source omits none and avoids an extra choice of a generator-inclusion map.
- The conclusion `∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
  IsIso (η.app K)` is exactly invertibility on the entire localizing category.

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` (recorded dependency
  sk-def-localizing-closure). Its imported `Sheaf.Paper.LocalizingClosure` supplies
  `CategoryTheory.localizingClosure` and
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`, whose actual defining
  predicate is used unchanged. The optional OfSize construction is not redefined.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated`; `Mathlib.CategoryTheory.Triangulated.Triangulated`:
  `CategoryTheory.IsTriangulated`; `Mathlib.CategoryTheory.Triangulated.Functor`:
  `CategoryTheory.Functor.IsTriangulated` (def-weil-triangulated-category).
- `Sheaf.Paper.LocalizingClosureExistence`:
  `AlgebraicGeometry.ProEtale.localizingClosure_exists` (proof dependency
  det-def-localizing-closure-existence), also used by the instance's projection.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `CategoryTheory.ObjectProperty.IsTriangulated`, the inherited `Pretriangulated`
  and `IsTriangulated` instances and exact inclusion (def-weil-triangulated-subcategory).
- `Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`:
  `CategoryTheory.NatTrans.isoLocus_localizing` (proof dependency
  det-sf-determination-localizing), imported non-publicly for the planned proof.
  Its source supports taking the source itself to be a localizing category;
  ambient minimality supplies the final restricted-domain conclusion as in the node.

Edge cases checked before writing: empty X or Y; the zero coefficient ring; zero
objects and functors; empty and infinite coproduct families; generators already
inside their own localizing closure; shifts by zero, positive and negative integers.
The claim is invertibility, not determination/equality of transformations. Thus the
older generation counterexample is irrelevant. No disputed statement or correction.

Searches for an existing statement:

- msearch.py leanfinder, query “Natural transformation between exact functors
  preserving coproducts invertible on constructible complexes is invertible on
  their localizing closure”: eight hits on homological/localization/derived functors,
  none states this restricted-domain specialization.
- msearch.py loogle, query `CategoryTheory.NatTrans.CommShift, IsIso`: zero hits,
  unknown identifier `IsIso`; source reading below resolved the required interfaces.
- msearch.py grep, query `isoLocus|isIso.*[Gg]enerat|isIso.*localizing`, in
  Mathlib CategoryTheory: zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, queries
  `sf-determination|Determination|determination|isIso.*localizing|isIso.*constructible`,
  plus the item id in upstream: located the upstream triangulated-envelope lemmas
  in `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators`, the project
  `LocalizingIsoLocus`, and the older thick-generation/counterexample statement.
  Read the signatures and docstrings: none is this admissible-coefficient,
  restricted-domain pro-etale statement. The upstream triangEnvelope theorem
  concerns finite operations and retracts, and lacks arbitrary coproduct closure.
- rg of the new declaration names in Mathlib, upstream and Sheaf: no collision.

## Second reading by NR

The dispatcher explicitly forbids starting another agent; this section records a
second pass by the same worker, not an independent review. The maintainer supplies
the independent review of the delivery.

Reopened the node and module and checked all binders against the statement.
Admissibility, both exact functors, both sum-preservation assumptions, naturality,
shift compatibility, all generators and all source objects are represented above.
In particular, the generator hypothesis uses the exact conjunction from
`localizingClosureProEtale`, the functors have the restricted rather than ambient
domain, and the source and target use their ambient inherited triangulations.
The helper is a projection from the existing existence theorem, not a new theorem
with an unmatched sorry or an arbitrary category structure. No node text is changed.

## Validation

The initial scompile run reached the item and identified an avoidable model-instance
mismatch: the recorded closure already chooses the canonical Grothendieck derived
category. Removed the explicit alternate `HasDerivedCategory` parameters in favor
of that canonical model; this preserves all mathematical cases.

Subsequent scompile attempts, including the current-server confirmation, stop in
upstream `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` before checking
the revised item: the published object file
`WeilConjectures/Mathlib/Algebra/Homology/Localization.olean` does not exist.
The same tool failure persisted on retry with a refreshed snapshot. No launcher,
read-only source, or compiled artifact was edited to bypass it. The revised file
therefore has not yet received a clean compile result.

The prescribed `deliver2.py NR sk-lem-sf-determination --no-push` also failed
before item compilation, both in its local overlay and current-server confirmation:
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` cannot
load the published `Sheaf/CategoryTheory/SiteCoveringAxioms.olean`. The wrapper
printed `COMPILE FAILED on the server, nothing pushed`. This is a second missing
published dependency artifact; the delivery was not pushed or marked validated.

## Resumed validation, 2026-10-21

Retained the saved packet and first ran the prescribed
`deliver2.py NR sk-lem-sf-determination --no-push`. It failed before item
compilation: the overlay module
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
could not load published
`WeilConjectures/Mathlib/CategoryTheory/Functor/KanExtension/Preserves.olean`.
The wrapper confirmed that missing artifact against current server sources.

Retried the item with the prescribed `scompile.py`. This refreshed snapshot
compiled twelve overlay dependencies, passing the earlier missing artifact, but
stopped in `Sheaf.Paper.CondensedConstantConstructibility`: published
`WeilConjectures/SixFunctors/Etale/UpperLowerStar/Defs.olean` does not exist.
Its server confirmation also failed before checking the item because published
`Sheaf/Paper/ModuleObjects.olean` does not exist. Thus neither wrapper produced
a clean item compile, and nothing was pushed. No source or artifact outside the
sandbox was edited, and no wrapper was modified or bypassed.

Reopened the current node, both statement-dependency records and declarations,
the blueprint statement and proof, and the imported closure/existence and generic
isomorphism-locus interfaces. The saved statement still matches the node.
The sandbox node differs from the current shared node only in `lean`; its recorded
signature exactly matches the file; every Lean line is at most 100 characters;
the only `sorry` is the named item theorem. No Lean changes were made on resume.

## Successful resumed validation, 2026-10-21

The first required dry run on this resume passed: `deliver2.py NR
sk-lem-sf-determination --no-push` reported `OK (dry run): commit aeb6d23ab85
passes the preflight and compiles; nothing pushed`. It compiled both the sandbox
and library module. The earlier missing-artifact failures above are historical;
the saved Lean file now has a clean compilation and preflight result.

Retained the saved Lean statement unchanged. Reopened the current blueprint unit
and proof, current node and all statement-dependency records, and the full source
signatures and docstrings for admissibility, localizing closure, its existence,
the generic isomorphism locus, and Mathlib's inherited triangulations and exact
functors. Confirmed the restricted domain, precise generator conjunction,
shift-compatible natural transformation, fixed-universe direct sums and universal
invertibility conclusion. No additional hypotheses or statement correction are
needed. The sandbox node differs from the current node only in `lean`; its
signature is verbatim, its UTC date is current, the maximum Lean line width is 83,
and its sole `sorry` is the named item theorem. A current name search in both
`lean/WeilConjectures` and `lean/Sheaf` found no declaration collision. No Lean
changes were needed on this resume.
