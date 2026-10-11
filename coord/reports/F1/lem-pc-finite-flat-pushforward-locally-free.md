## Worker report

The node is already stated exactly by the source-repository declaration
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward` in
`WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`; therefore no new
module is written. The node's `lean` record points to this existing declaration
on branch `slopmaster2`.

Hypothesis and conclusion correspondence:

- Schemes `X` and `Y` and their morphism `g : X ⟶ Y` are the explicit binders
  `{X Y : Scheme.{u}}` and `(g : X ⟶ Y)` in the source theorem's surrounding
  namespace and variables.
- The finite hypothesis is the typeclass `[IsFinite g]`, Mathlib's finite
  morphism predicate recorded for `def-weil-finite-integral-morphism`.
- Flatness is exactly `[Flat g]`, the recorded stalkwise flatness predicate.
- Locally finite presentation is exactly `[LocallyOfFinitePresentation g]`.
- The input module is `(ℱ : X.Modules)`, with
  `[SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ]`; this is the
  dependency's finite locally free O_X-module notion, including its finite
  locally free open-cover meaning.
- The conclusion is
  `SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf)
  ((pushforward g).obj ℱ)`, the finite locally free O_Y-module obtained by the
  direct image functor.

Dependencies read: `def-pc-scheme` uses `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom`; `def-weil-finite-integral-morphism` uses
`AlgebraicGeometry.IsFinite` (and `IsIntegralHom` for its integral clause);
`def-weil-flat-morphism` uses Mathlib `AlgebraicGeometry.Flat`;
`def-sbc-locally-finite-presentation` uses
`AlgebraicGeometry.LocallyOfFinitePresentation`; and
`def-amb-finite-locally-free-module` records
`SheafOfModules.IsFiniteLocallyFreeOfRank` from the source's locally-free module
library. The item uses that fixed-rank notion on members of an open cover;
its varying-rank predicate is the existing `SheafOfModules.IsFiniteLocallyFree`
in the same source module, not the dependency's fixed-rank predicate itself.

Edge cases checked: the theorem has no nonemptiness, separatedness, Noetherian,
characteristic, rank-positivity, or quasi-compactness assumptions; empty schemes
and the zero module are therefore included. Rank is allowed to vary locally,
as in `IsFiniteLocallyFree`, and no fixed rank or index universe is introduced.
The finite hypothesis is the finite clause of the finite/integral convention;
no extra integrality hypothesis is silently added.

Searches for an existing declaration:

- `msearch.py ... leanfinder "finite flat locally finitely presented morphism pushforward finite locally free sheaf"` returned nearby finite-presentation and finite-presentation-app lemmas, but no exact theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward, IsFiniteLocallyFree"` returned no Loogle hit (the source declaration is outside Mathlib).
- `msearch.py ... grep "isFiniteLocallyFree_pushforward"` and direct `rg` over `WeilConjectures/` found the exact declaration in `AlgebraicGeometry/Modules/FinitePushforward.lean`.
- Direct `rg` over `lean/Sheaf` found only related statements and no declaration with this exact source theorem.

No statement correction, dependency module, new node, or `STATEMENT-DISPUTED`
flag is needed.

## Earlier second reading (a previous round; superseded)

I independently opened the node, the source theorem and every statement dependency.
The source signature is exactly the node's finite, flat, locally finitely presented
pushforward assertion. The finite locally free hypothesis is attached to the
same `X.Modules` object and the conclusion uses the same `pushforward g` object
and `Y.ringCatSheaf`; no clause, object, or hypothesis is missing. The source
uses `[IsFinite g]` for the node's finite clause, while the node's convention
also documents the separate integral predicate; it does not require integrality
for this theorem. The recorded `lean.statement` is verbatim the source
signature through `:= by`. No mismatch was found.


## Second reading by F1

I opened the sandbox node, its source place
`WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean:208-242`,
the namespace and variables at lines 45-51, and every statement-dependency
node and its recorded declaration (or convention). The source place is a
Lean file, not a Stacks tag; it assumes only `{X Y : Scheme.{u}}` throughout
this theorem. Earlier declarations' Noetherian and integral assumptions do
not carry over. The recorded `lean.statement` is verbatim the source
signature, including its line breaks and `:= by`.

Objects, hypotheses and conclusion, item by item:

- Schemes X and Y: `{X Y : Scheme.{u}}`; Mathlib `Scheme` extends a locally
  ringed space with local affine charts, and `Scheme.Hom` is the morphism
  of underlying locally ringed spaces. Verdict: exact.
- Morphism g from X to Y: `(g : X ⟶ Y)`. The convention dependency
  `def-pc-morphism-conventions` delegates to the named predicates and adds
  no hypothesis here. Verdict: exact.
- Finite g: `[IsFinite g]`. Read `Morphisms/Finite.lean:39-41`: affine
  preimages plus finite ring maps on affine opens. This is the finite
  clause of `def-weil-finite-integral-morphism`, not its integral clause.
  Verdict: exact.
- Flat g: `[Flat g]`. Read `Morphisms/Flat.lean:42-45,99-107`:
  `Flat.iff_flat_stalkMap` identifies the affine criterion with flatness
  of every local-ring map in `def-weil-flat-morphism`. Verdict: exact.
- Locally finitely presented g: `[LocallyOfFinitePresentation g]`.
  Read `Morphisms/FinitePresentation.lean:45-60`: finite presentation on
  affine pairs is the recorded affine-local form of
  `def-sbc-locally-finite-presentation`. No global finite-presentation
  hypothesis is inserted. Verdict: exact.
- O_X-module F: `(ℱ : X.Modules)`, the existing category of module sheaves
  over `X.ringCatSheaf`. Verdict: exact.
- F has an open cover with constant finite rank on each member:
  `[SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ]`.
  I read both source classes at `Sheaf/LocallyFree.lean:133-158`.
  The dependency `def-amb-finite-locally-free-module` records
  `IsFiniteLocallyFreeOfRank`, with one fixed rank d; the item explicitly
  applies that notion separately on cover members. `IsFiniteLocallyFree`
  allows different finite generator sets on those members. The source
  lemma `Scheme.Modules.exists_mem_over_iso_free` in
  `Modules/LocallyFreeAffine.lean:50-60` gives a finite free neighbourhood
  of every point, with rank the cardinality of its finite index type.
  Conversely `SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free`
  at lines 294-308 constructs the predicate from such a cover; and
  `isFiniteLocallyFreeOfRank_iff_exists_over_iso_free` at lines 271-288
  identifies each fixed-rank notion. Verdict: exact; the report's claim
  that the dependency itself records the varying-rank predicate was wrong.
- Conclusion: `SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf)
  ((pushforward g).obj ℱ)`. Read Mathlib `Modules/Sheaf.lean:165-175`:
  pushforward has sections Γ(F, g⁻¹U) with the induced O_Y action.
  It is the direct image g_*F, and the same varying-rank predicate gives
  the required cover on Y. Verdict: exact; no fixed output rank is asserted.

Edge cases: finite index sets may be empty, so rank zero and the zero
module are included. Local generators data permit an empty cover for an
empty scheme. Neither X nor Y is required nonempty, and g need not be
surjective. No field, characteristic, Noetherian, separatedness or
positive-rank assumption occurs. `universe u` is bound explicitly; the
scheme category and module universe use the usual common universe, into
which schemes of different smaller universes can be lifted. No independent
smaller universe for tests, no bound on rank, and no unbound variable occurs.

Independent searches, using different terms from the worker:

- LeanFinder via `msearch.py`: "direct image of a vector bundle under a
  finite locally free morphism" returned the Mathlib pushforward functor
  and its sections formula, but no exact theorem.
- Loogle via `msearch.py`: "AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Flat" returned rank-of-morphism results, including
  `Scheme.Hom.isLocallyConstant_finrank`, not the assertion about all F.
- Grep via `msearch.py`: "locallyFree.*pushforward|pushforward.*[Ll]ocallyFree"
  returned no Mathlib matches.
- LeanSearch via `msearch.py`: "direct image of finite locally free modules
  by finite flat morphisms of schemes" was unavailable (Internal Server
  Error); I record no negative mathematical verdict for that service.
- Direct `rg` in `WeilConjectures` and repository `lean/Sheaf` for both
  orders of locally-free/pushforward found the exact source theorem at
  `FinitePushforward.lean:214`. The repository theorem
  `Scheme.Modules.isFiniteLocallyFree_pushforward_unit` in
  `Sheaf/AlgebraicGeometry/FinitePushforwardLocallyFree.lean` specializes
  to the structure sheaf; it does not replace the all-module theorem.

Mismatch repaired: corrected the Worker report's dependency name and added
this explicit fixed-rank-on-cover versus varying-rank comparison. No Lean
signature or node change was needed. No new nodes or dependency modules,
statement correction, hollow definition or new proof is delivered. H8/H9
requirements for newly written modules do not apply to this existing source
declaration; duplicating it merely to add docstrings would violate H4.
No module is delivered, so there is no new file to compile with scompile;
the existing declaration is in the compiled read-only source library.
