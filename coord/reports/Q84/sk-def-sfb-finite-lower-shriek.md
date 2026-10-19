## Worker report

The entire statement already exists. This delivery records `existing: true`, with primary
`AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar` in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper`, whose public import closure
exposes the companion declarations for every clause, including the definitions. No Lean module, new definition, proof,
dependency-node change, or statement correction is delivered.

Source read: current blueprint main-20261015,
`sec-six-functors-basics/sk-def-sfb-finite-lower-shriek/_section.md`, the item's complete
statement and proof, all seven statement dependencies and their recorded declarations.
There is no repair note for this item. The current server sources were also obtained with
`scompile.py --source` for the canonical finite-coefficient definition module and the
ordinary `LowerShriek.Defs`, `LowerShriek.OpenImmersion.Defs`, and `LowerShriek.Proper`.
The two old Defs paths are compatibility re-exports. The chosen primary module exposes
the complete collection; the actual lower-shriek definition is owned by the canonical
finite-coefficient module rather than the stale local ordinary implementation.

Hypotheses and clauses are rendered as follows (all names below have prefix
`AlgebraicGeometry.ProEtale` unless otherwise specified):

- The Grothendieck abelian coefficient category is the same arbitrary `A : Type u'`,
  with `[Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]` throughout.
  Schemes have universe `u`; the coefficient-object universe `u'` remains independent.
  These are the published SixFunctors size conventions; finite coefficients in the title
  do not impose finiteness or torsion on this general coefficient category.
- For every `j : U ⟶ X` with `[IsOpenImmersion j]`, `openImmersionLowerShriek A j` has
  type `Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A`.
  Its body is `localizationLowerShriek A j inferInstance`.
  `localizationLowerShriek_eq` identifies this definitionally with
  `sheafToPresheaf ⋙ localizationLowerShriekPresheaf ⋙ presheafToSheaf`.
  The middle functor is `(MorphismProperty.Over.map ⊤ h).op.lan`, where `Over.map`
  composes `(T → U)` with `j`; this is precisely the stated localization Kan extension.
- `openImmersionLowerShriekUpperStarAdjunction A j` has type
  `openImmersionLowerShriek A j ⊣ upperStar A j`, using the dependency's exact pullback.
  It transports the localization adjunction along `upperStarIsoOpenImmersionRestriction`.
- `preservesFiniteLimits_openImmersionLowerShriek A j` states finite-limit preservation.
  The preceding adjunction supplies preservation of finite colimits by the standard
  left-adjoint instance, and `openImmersionLowerShriek_additive` supplies additivity.
  These give exactness between the abelian sheaf categories without additional assumptions.
- `fullyFaithfulOpenImmersionLowerShriek A j` has type
  `(openImmersionLowerShriek A j).FullyFaithful`; it applies to any open immersion,
  with no properness, closed-range, or quasi-compactness condition on `j`.
- For a compactification `c`, `Compactification.lowerShriek A c` is definitionally
  `openImmersionLowerShriek A c.i ⋙ lowerStar A c.g`. Functor order means first `i_!`,
  then `g_*`, exactly the node's `g_* ∘ i_!`.
- The recorded dependency `AlgebraicGeometry.Compactification.BoundaryCompactification f`
  retains the quasi-compact open immersion required by `sk-def-nagata-sketch-data`.
  Its underlying upstream compactification is `c.obj.obj`; applying the existing
  `ProEtale.Compactification.lowerShriek` to that object uses exactly its given `i`, `g`,
  and factorization, not a replacement factorization. The upstream definition is available
  more generally, which does not exclude or change these compactifications. Refinement
  and density are not hypotheses of this unit and are not added.
- For `(f : X ⟶ Y) [HasCompactification f]`, `lowerShriek A f` is definitionally
  `Compactification.lowerShriek A (HasCompactification.compactification f)`.
  `lowerShriek_eq` records its composite formula. This is the specified chosen
  compactification convention; no compactification-independence assertion is inserted.
  A quasi-compact compactification supplies the underlying upstream existence condition;
  its `f` is quasi-compact, and `Compactification.quasiCompact_openImmersion_iff` ensures
  the upstream chosen factorization also has quasi-compact open immersion.
- `lowerShriekToLowerStar A f` has type `lowerShriek A f ⟶ lowerStar A f`.
  Its definition whiskers the actual `openImmersionLowerShriekToLowerStar A c.i`
  with `lowerStar A c.g`, then composes `lowerStarComp A c.i c.g` and the factorization
  equality. The open comparison inserts the inverse of the counit of restriction
  adjoint to direct image, then the counit of extension by zero adjoint to restriction.
  Thus it is the node's canonical comparison, not an arbitrary transformation.
- With the additional hypothesis `[IsProper f]`, `isIso_lowerShriekToLowerStar A f`
  has type `IsIso (lowerShriekToLowerStar A f)`. This is invertibility of the actual
  comparison, not merely existence of some isomorphism of its endpoint functors.

Dependency declarations and modules inspected:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, whose source uses the small
  `Scheme.ProEt.topology` site. This item uses the site itself, not the module-valued
  derived category appearing in the later portion of that dependency's statement.
- `Sheaf.Compactification.BoundaryRefinement`:
  `AlgebraicGeometry.Compactification.QuasiCompactObjects`, `boundaryRefinementProperty`,
  `BoundaryCompactification`, and `DenseBoundaryCompactification`.
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`:
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, `lowerStar_obj_val_obj`,
  and `lowerStarComp`. These are the same functors used by the lower-shriek declarations.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `openImmersionLowerShriek`, `localizationLowerShriekPresheaf`,
  `localizationLowerShriek_eq`, `openImmersionLowerShriekUpperStarAdjunction`,
  `preservesFiniteLimits_openImmersionLowerShriek`, and the additive instance.
- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful`:
  `fullyFaithfulOpenImmersionLowerShriek` and the invertible-unit instance.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`:
  `Compactification.lowerShriek`, `lowerShriek`, and `lowerShriek_eq`.
- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.Comparison`:
  `openImmersionLowerShriekToLowerStar` and `lowerShriekToLowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper`:
  `isIso_lowerShriekToLowerStar`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.

Edge cases checked against the signatures and constructions: empty source/open subscheme
and empty schemes are not excluded; the empty Kan-extension comma category uses the
initial/zero object supplied by the coefficient category. Identity immersions and proper
maps, the zero coefficient category, and non-quasi-compact open immersions are all retained.
The proper-map conclusion concerns the same chosen compactification; it does not assume
it is the identity compactification. No Noetherian, finite-type-on-an-arbitrary-open,
separated-base, torsion, or finite-coefficient assumption is added.

Searches for an existing statement (msearch.py, group Q84, this item):

- LeanFinder: "Extension by zero on proetale sheaves with Grothendieck abelian coefficients
  and compactification lower shriek with canonical comparison to direct image, isomorphism
  for proper morphisms". Eight Mathlib hits about condensed Kan extensions and module
  restrictions; no exact Mathlib statement.
- Loogle: `AlgebraicGeometry.ProEtale.lowerShriek, AlgebraicGeometry.ProEtale.lowerStar`.
  Zero hits; the project-specific identifier is not known to the Mathlib search service.
- Mathlib grep: `lowerShriekToLowerStar|openImmersionLowerShriek|extension.by.zero` in
  `CategoryTheory`. Zero hits.
- LeanSearch: "Extension by zero lower shriek proetale sheaves compactification comparison
  direct image proper". Eight hits, including condensed left Kan extensions, skyscraper
  adjunction, and extension of compactly supported functions; none is this unit.
- `rg` with the canonical names in the prescribed upstream `WeilConjectures`, side
  `lean/WeilConjectures`, and side `lean/Sheaf` found the exact implementations above.
  Searching upstream for the node id found no exact textual tag. The source-name census
  was also checked; source declarations and their full signatures/docstrings, rather than
  names alone, decide this match. Search outputs are retained in `searches.jsonl`.

No STATEMENT-DISPUTED issue or source correction was found. Existing proof dependencies
may still contain postponed proofs; this record asserts a complete statement match only.

Validation: `scompile.py Q84 sk-def-sfb-finite-lower-shriek
scratchpad/ExistingProbe.lean` completed successfully. The scratch probe imports the
proper-comparison module and the two recorded side-project dependency modules, checks all
principal declaration types, synthesizes finite-colimit preservation and additivity of
extension by zero, type-checks `Compactification.lowerShriek A c.obj.obj` for a recorded
boundary compactification, and synthesizes `IsIso (lowerShriekToLowerStar A f)` under
`[IsProper f]`. Both the sandbox compile (2.3 seconds) and library-context check
(2.4 seconds) were clean. The probe is scratch only and is not a delivered module.

The first delivery dry run exposed a record-import issue: its generated existing-name
probe imports only `lean.module`, so choosing the defining lower-shriek module omitted the
downstream full-faithfulness and proper-comparison names. The record now chooses the
existing proper-comparison instance as primary in `LowerShriek.Proper`, whose public
import closure exposes all recorded declarations. No source or statement changed.

## Second reading by Q84

I independently read the node statement, its blueprint source section, the recorded dependency
signatures, and the existing declarations in `LowerShriek.Proper` and its public imports. The
statement's objects and clauses match as follows:

- A Grothendieck abelian coefficient category is rendered by `A : Type u'` with
  `[Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]`; the independent
  coefficient universe and the scheme universe are preserved.
- For every `j : U ⟶ X` with `[IsOpenImmersion j]`, the extension-by-zero functor is
  `ProEtale.openImmersionLowerShriek A j`. Its definition is the sheafification of the
  opposite localization left Kan extension, and `localizationLowerShriek_eq` gives the
  stated sectionwise localization formula. `openImmersionLowerShriekUpperStarAdjunction`
  gives the adjunction to the recorded upper-star pullback.
- Exactness is represented by
  `preservesFiniteLimits_openImmersionLowerShriek`, together with the left-adjoint finite
  colimit preservation (`PreservesColimits.preservesFiniteColimits`) and the additive
  instance; `fullyFaithfulOpenImmersionLowerShriek` gives full faithfulness. No condition
  beyond the node's open immersion and coefficient assumptions appears.
- A compactification `c` gives
  `ProEtale.Compactification.lowerShriek A c = c.i_! ⋙ c.g_*`, which is the node's
  `g_* ∘ i_!` under functor composition notation. The dependency's
  `BoundaryCompactification` supplies quasi-compact compactifications; applying this
  definition to `c.obj.obj` retains the exact source compactification data. The upstream
  `Compactification` API is intentionally a permissive carrier and does not change the
  source case.
- For a chosen compactification, `ProEtale.lowerShriek A f` and `lowerShriek_eq` render the
  chosen lower shriek. `lowerShriekToLowerStar` is the canonical transformation built from
  the open comparison, its counit, `lowerStarComp`, and the factorization equality.
- Under `[IsProper f]`, `isIso_lowerShriekToLowerStar A f` is exactly invertibility of that
  canonical comparison. It does not assert a different isomorphism or compactification
  independence.

No mismatch was found in hypotheses, object types, quantifier order, or conclusion clauses.
The use of the broader upstream `Compactification` carrier was checked against the already
recorded compactification lower-shriek node and the landed `BoundaryCompactification` subtype:
source compactifications embed as `c.obj.obj`, and the implementation adds no assumption to
those instances. I therefore kept the existing declaration record unchanged.

Edge cases checked: the empty scheme and empty open immersion, the identity immersion and
identity/proper morphisms, the zero Grothendieck abelian category, arbitrary (including
non-quasi-compact) open immersions for the open-immersion clause, and proper maps whose chosen
compactification is not the identity. No index-set or `n = 0` quantifier occurs, and no
characteristic, Noetherian, finite-type, separated-base, torsion, or finite-coefficient
hypothesis is introduced.

Searches were independently repeated with `rg` over Mathlib, `WeilConjectures/`, and
`lean/Sheaf`, plus LeanFinder/Loogle/LeanSearch semantic queries for pro-étale extension by
zero, localization Kan extensions, lower shriek, and the proper comparison. They found only
the exact existing project declarations (and unrelated condensed/module or scheme-module
facts), so the `existing: true` binding is correct. The existing-name probe and
`scompile.py` both compile successfully.

The second-reading scratch probe additionally verifies the potentially subtle size of the
compactification domain: `c.obj.obj.hasCompactification` supplies the upstream existence
class from a recorded `BoundaryCompactification`, and
`(HasCompactification.compactification f).quasiCompact_openImmersion
(c.obj.obj.quasiCompact c.obj.property)` gives quasi-compactness of the upstream chosen open
immersion. Thus on the source domain the chosen compactification really is one in the
source sense; it is not merely an arbitrary wider compactification. Both sandbox and
library-context compilation of this strengthened probe passed (2.1 s and 1.9 s).

Independent search details: LeanFinder query beginning "For an open embedding of schemes,
the left adjoint to restriction of proetale sheaves" returned eight scheme-module
restriction/adjunction hits, none concerning this small-site construction; Loogle
`"lowerShriek"` returned no hits. LeanSearch query "Sheafification of a left Kan extension
on the localization of a small scheme site defines exact fully faithful extension by zero"
returned eight generic sheafification declarations, none the item. The `rg` query
`extension by zero|localizationLowerShriek|lower shriek|lowerShriekToLowerStar` found the
canonical project implementation and unrelated helpers; Mathlib has no complete match.
There are no new nodes, dependency modules, or corrected node statements to audit in this
delivery. No delivered Lean source is needed; the existing declarations' data are real
constructions. The sole delivery change beyond the worker's node binding is this independent
second-reading report.
