## Worker report

The module `Sheaf.AlgebraicGeometry.LogTowerCoverRigidity` states the complete node as
`AlgebraicGeometry.log_tower_cover_rigidity`, with its sole proof `sorry`. It imports
the landed `Sheaf.AlgebraicGeometry.LogBlowupFullPullback` interface. The only helper
defined here is the cocycle predicate `LogBlowupTowerIso.IsComposite`, with a real
predicate body. There is no dependency-module patch, statement correction, or new
node. The existing definition node `def-trf-log-tower-full-pullback` is added to
`stmt_deps`. No mathematical assertion is proved.

Source read: ILO VIII 3.3.7--3.3.10, printed pp.107--108, and proof of 3.3.15,
pp.109--110 (PDF converted with pdftotext in the sandbox). In particular the source
removes exactly whole-monoid centers, defines pullbacks recursively using pulled-back
ideals, and invokes descent for uniqueness and comparison on finite common covers.
The latest blueprint's `lem-trf-local-term-locality.md` and proof were read: they now
use contracting correspondences. This item belongs to the historical log-resolution
branch recorded in its blueprint metadata; no current unit route is altered.

Clause correspondence, in the order of the conjuncts in the Lean statement:

1. `X U : FineSaturatedLogScheme.{u}` includes locally Noetherian underlying schemes,
   étale monoid sheaves, the log unit condition and fs charts, as fields of the recorded
   definition. `f : EtaleLogHom U X`, `f.IsStrict`, `Etale f.base` and
   `Function.Surjective f.base` render the given surjective strict étale cover.
   `I J : X.logStructure.IdealFamily` with `IsIdeal I` and `IsIdeal J` render arbitrary
   ideal subsheaves, without a coherence or nonemptiness assumption.
   `f.pullbackIdeal I = f.pullbackIdeal J → I = J` is equality detection: for a strict
   morphism the generated pullback ideal is precisely the restricted ideal.
   The second half quantifies every small-étale object `W` and every log section `s`.
   It states `s ∈ I W ↔ ... ∈ I (W ⨯ Scheme.Etale.mk f.base)` using the actual
   restriction along `prod.fst`. Products in `X.scheme.Etale` are the scheme fibre
   products over X, so this is explicitly the specified V ×_X U membership criterion.
   On that object, viewing the restricted ideal on U or the original ideal on X gives
   the same subset of sections. All test objects have the site's existing universe.
2. `B C : LogBlowupTowerOver X` supplies finite ordered saturated log blowup towers
   whose universal-property fields include nonempty coherent actual centers.
   `S T : LogBlowupTowerOver U` and `p q : LogBlowupFullPullback ...` exhibit their
   recursive uncontracted pullbacks, retaining every stage.
   `a : LogBlowupTowerIso S T` is the specified ordered isomorphism, including the
   identity log map at the base and actual center preservation.
   `∃! e : LogBlowupTowerIso B C, e.IsPullbackIso p q a` asserts unique lifting of that
   very isomorphism, including all log-section maps, not merely existence of some
   isomorphism of the underlying blowup spaces.
3. `∀ X B C, Subsingleton (LogBlowupTowerIso B C)` is rigidity without any cover
   hypothesis: there is at most one ordered center-preserving isomorphism over X.
4. For two global and two prescribed local isomorphisms with `IsPullbackIso` compatibility,
   `(e = e' ↔ a = a')` is the equality test on a cover.
5. For three towers and their full pullbacks, the three `IsPullbackIso` hypotheses identify
   the prescribed comparisons; `a.IsComposite b c ↔ α.IsComposite β γ` is the
   corresponding cover test for the cocycle identity, on indices and actual log maps.
6. `X U V W`, the strict étale surjections `f g`, and `r.IsFSPullback f s g` render
   the common cover W = U ×_X V, up to its universal-property identification. Because
   the two cover maps are strict, this fs pullback is also the ordinary scheme fibre
   product. S and T are contracted by their `IsContracted` hypotheses. Full comparisons
   from B and C to S and T exhibit the specified descending towers with the actual
   centers and ordered maps; in particular their canonical uncontracted descent data
   are effective. No arbitrary descent datum, arbitrary map, or choice from existence
   replaces these identifications. Full comparisons along r and s exhibit S' and T'
   over W; `LogBlowupTowerIso S' T'` is the common-cover isomorphism.
   The conclusion explicitly gives `B.tower.length = C.tower.length`, existence of the
   center-preserving isomorphism, and its uniqueness. Specified descent-data
   compatibility follows from clause 3 on the overlaps.
7. `e.IsComposite f g` for any three ordered center-preserving comparisons is the
   three-choice cocycle identity. It applies, in particular, to comparisons obtained
   in clause 6 and to their restrictions to further common covers.
8. `IsChartedLogBlowupInput X` supplies the charted input convention of the dependency.
   For `f.IsIdentity`, a full comparison between the original tower B and its descended
   realization C gives `Nonempty (LogBlowupTowerIso B C)`. Together with clause 3 this
   is the canonical identification returning the original tower, with its actual
   centers preserved by the isomorphism's `centers` field. The original tower itself
   is the realization on the identity cover; no new tower is chosen by the statement.

Dependency declarations used (full signatures and docstrings read):

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogHom`, `EtaleLogHom.CompEq`, `EtaleLogStructure.IdealFamily`, `IsIdeal`,
  `EtaleLogHom.pullbackIdeal`, `IsSaturatedLogBlowup`, `SaturatedLogBlowupTower`.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup` and its public import
  `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`: `EtaleLogHom.IsStrict`, `IsIdentity`,
  `Square`, `IsFSPullback`, `AreInverses`. Strictness uses the normalized canonical
  characteristic relation; identity includes section maps. Cartesian squares are fs.
- `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`: `LogBlowupTowerOver`,
  `LogBlowupTowerIso`, `IsChartedLogBlowupInput`, reused through the full-pullback
  module. No declaration in that dependency is changed.
- `Sheaf.AlgebraicGeometry.LogBlowupFullPullback`: `LogBlowupFullPullback`,
  `LogBlowupTowerOver.IsContracted`, and `LogBlowupTowerIso.IsPullbackIso`. The first
  records full ordered fs pullbacks; the second excludes exactly whole centers;
  the third identifies the actual restricted isomorphism on both level and stage
  indices and all log-section maps. These are imported and reused verbatim.
  Their full signatures, docstrings and the owning DAG node were read on repair.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  `Scheme.Etale`, `Scheme.Etale.mk` and the small étale category's finite limits.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  projections and universal property, underlying the scheme-fibre-product meaning.
  The small-site product presentation uses `Limits.prod`, `Limits.prod.fst`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, used by the existing
  monoid-sheaf and ideal-subsheaf encodings, not replaced by a private sheaf predicate.
- Proof-only import `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`: the recorded
  étale-covering base-change Mathlib match, namely the stable-under-base-change
  instance on `Scheme.precoverage`. The synchronization proof dependency has no
  recorded Lean module, so there is no available proof-only import for it.

Edge cases checked before writing: length zero has `Fin 1` levels and `Fin 0` stages;
full comparison and isomorphism center conditions are then vacuous, and the initial
log map is still the identity. The empty scheme and empty ideal subsheaf are allowed;
no Nonempty-on-points or nonempty-ideal hypothesis occurs in the ideal clause. Whole
centers are allowed in general towers and full pullbacks; only the explicitly
contracted S,T exclude them. A proper principal center such as (t) on the standard
log A¹ remains a stage even though its blowup is an isomorphism. In particular (t)
and (t²) are not identified by comparing blowup spaces. No quasi-compactness,
log-regularity, torsion-freeness, or fan chart is added to the general cover/rigidity
clauses. All log schemes and test fields use the already established universe u.
Surjectivity is indispensable for ideal equality: restriction to an open missing the
support of a difference would otherwise lose the distinction. The identity-cover
clause uses the dependency's charted-input convention and retains actual centers.

Searches performed:

- msearch.py / LeanFinder: "Ordered saturated log blowup towers have unique center
  preserving isomorphisms descending from a strict etale cover". Eight results about
  standard étale pairs/presentations, none for log towers.
- msearch.py / Loogle: "LogBlowupTowerIso". No hits, unknown identifier in Mathlib.
- msearch.py / grep: "LogBlowup|LogScheme". No Mathlib hits.
- msearch.py / LeanSearch: "log blowup tower isomorphism descends uniquely along a
  strict etale surjection". Eight results, including ordinary scheme flat descent;
  none state log-tower rigidity, retain ordered actual centers, or supply full pullback
  compatibility. They are not exact matches.
- rg over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  "log_tower.*rigid|LogBlowupTowerIso|lem-trf-log-tower-cover-rigidity". The only tower
  isomorphism definition is the recorded procedure module; a historical consumer
  mentions this item's id but does not state its theorem. No existing theorem matches.
- Repair search: rg in `lean/Sheaf/AlgebraicGeometry` and the full-pullback DAG node
  finds the existing `IsContracted`, `LogBlowupFullPullback`, and `IsPullbackIso`
  interfaces. These supersede the initial search result for the duplicate helpers.
  A further rg search for `LogBlowupTowerIso.IsComposite` and composition predicates
  found no isomorphism-cocycle definition. `LogBlowupComparison.IsCompositeComparison`
  concerns contracted comparisons over possibly different bases, not isomorphisms
  of towers over one base; it cannot directly replace the isomorphism predicate.

No STATEMENT-DISPUTED issue or statement fault was found.

## Repair of returned delivery 7ce9312cb24d

Point 1: the immutable-head review found that our procedure module redeclared
`AlgebraicGeometry.LogBlowupTowerOver.IsContracted`, already defined in the landed
`Sheaf.AlgebraicGeometry.LogBlowupFullPullback`. The two predicates have exactly the
same body, excluding whole-monoid centers and retaining proper principal centers.
The duplicate has been removed, and the statement now imports and uses the original
name directly. No replacement name or duplicate predicate was introduced.

Reading that module also revealed that its `LogBlowupFullPullback` has exactly the
fields of our `LogBlowupFullComparison`. The latter duplicate is removed too.
Our `IsLift` is replaced by the original `LogBlowupTowerIso.IsPullbackIso`, which
records the same commuting restriction square and additionally spells out the stage
index equality determined by its level indices. Since `before` and `after` of every
ordered identification determine its stage map, that explicit equality imposes no
new mathematical hypothesis. The two square presentations use the same actual log
maps, with equality of level indices transporting their sources.

The original procedure dependency module and node patch have been removed entirely
from the sandbox delivery. The current live procedure module is imported unchanged
through the full-pullback module, avoiding any reverse import or cycle. The retained
`LogBlowupTowerIso.IsComposite` helper belongs to this item's cocycle clause and is
now declared in its own statement module, with this item's source and blueprint tag.
It is listed alongside the theorem in `lean.declarations`. It is a real predicate on
indices and actual log composites, and contains no postponed data or proof.

The repaired node is refreshed from current main; only `lean` and the addition of
the landed definition `def-trf-log-tower-full-pullback` to `stmt_deps` differ. The
TeX statement and proof plan are unchanged. The current server source for the
procedure and full-pullback modules was retrieved using `scompile.py --source` and
matches the read checkout. Clause correspondence and edge cases above were checked
again with the existing full-pullback and restriction declarations.

The packet now consists of the item's single Lean module, its single node record,
and this report. The dependency module from the returned packet is not delivered.

Repair validation: the single module compiled cleanly in both sandbox and library
modes with scompile.py (9.6 s and 13.4 s). The deliver2.py --no-push dry run passed
server preflight and compilation at ff5e97b93a9. Its staged paths were exactly the
item module, item node, and report; no procedure or full-pullback dependency source
was staged. The recorded theorem signature matches the file verbatim, and the node
changes only `lean` and the added landed definition dependency in `stmt_deps`.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
