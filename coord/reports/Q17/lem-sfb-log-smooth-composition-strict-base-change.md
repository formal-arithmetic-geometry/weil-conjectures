## Worker report

The module `Sheaf.AlgebraicGeometry.FSLogSmoothCompositionStrictBaseChange` states
`AlgebraicGeometry.fsLogSmooth_composition_strictBaseChange`, with one postponed
proof. No theorem is proved. The original statement, statement dependencies,
seven-step proof, proof dependencies, and approved Q27 split are preserved verbatim.

Hypothesis and clause correspondence:

1. Throughout, `FineSaturatedLogScheme.{u}` includes its actual scheme, local
   Noetherianity, log sheaf, and fs-chart condition. `EtaleLogHom X Y` includes the
   scheme map and natural compatible relative étale log-section maps.
2. Smooth composition: the first conjunct quantifies over X, Y, Z, f and g,
   assumes `f.IsLogSmooth` and `g.IsLogSmooth`, and supplies a composite `c` with
   `f.CompEq g c` and `c.IsLogSmooth`. `CompEq` fixes scheme and log-section maps.
3. Log étale implies log smooth: the second conjunct is exactly
   `f.IsLogEtale → f.IsLogSmooth` for every log morphism.
4. Mixed composition: the third conjunct assumes `f.IsLogEtale` and
   `g.IsLogSmooth` and supplies their log-smooth composite with `CompEq`.
5. Strict base change: the fourth conjunct assumes `f.IsLogSmooth` and
   `h.IsStrict` and supplies X', p, q, and the common composite c.
   `IsPullback p.base q.base f.base h.base` specifies the ordinary scheme product;
   `p.IsStrict` specifies the log structure pulled back from X. Both `CompEq`
   equations impose log commutativity, and `q.IsLogSmooth` is the conclusion.
   The fifth conjunct makes the same assertion for every given representative
   with these properties. Thus the product is supplied, not an extra existence
   assumption. The pullback and strictness hypotheses specify the intended
   strict log product and are not asserted as extra conclusions for arbitrary maps.
6. Strict étale locality: the sixth conjunct quantifies over arbitrary
   `ι : Type v`, U, V and log maps a, b, r, c. The first two hypotheses say
   `a i` and `b i` are strict and their scheme maps are étale. The next hypothesis
   says each chart square commutes on schemes and log sections. The pointwise
   equation `∀ x, ∃ i z, (a i).base z = x` says the source neighborhoods jointly
   cover X. The conclusions are the two iff statements for log smoothness and
   log étaleness. Covering X suffices, since points of Y outside the image of f
   impose no condition on f; an arbitrary target cover is handled by its pulled-back
   source cover. No finite, nonempty, or small-universe restriction on the family.
7. Saturated blowups: the seventh conjunct takes every representative b and
   ideal I and concludes `b.IsLogEtale` from `IsSaturatedLogBlowup b I`.
   That predicate includes `IsNonemptyCoherentIdeal I` and the actual fs universal
   property and invertibility, so no ideal hypothesis is dropped or manufactured.
8. Finite towers: the final conjunct quantifies over `SaturatedLogBlowupTower`.
   Its level/arrow/center/isBlowup fields supply the entire finite ordered tower.
   The family p maps every level to level zero, `IsIdentity` fixes p at zero
   including all log-section maps, and each `CompEq` specifies the next composite.
   The final-level map is log étale. Length zero is explicitly permitted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogHom`, `EtaleLogHom.CompEq`,
  `EtaleLogStructure.IdealFamily`, `IsSaturatedLogBlowup`,
  `SaturatedLogBlowupTower`, and their component definitions.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `FSLogChart`, its canonical comparison and group conditions,
  `EtaleLogHom.IsLogSmooth`, `EtaleLogHom.IsLogEtale`.
- `def-per-strict-log-morphism` uses its unchanged recorded module
  `Sheaf.AlgebraicGeometry.FSStrictLogMorphism` and its existing declarations
  `EtaleLogHom.CharacteristicRelation`, `EtaleLogHom.IsStrict`, and
  `EtaleLogHom.IsIdentity`. No second definitions are delivered.
- Ordinary scheme pullback and étale notions are Mathlib's `IsPullback` and `Etale`.
  The module publicly imports statement dependencies and privately imports the
  available proof-dependency modules: associated-log universal stalks, coherent
  log ideal chart construction, first-order-thickening base change, finite
  presentation, étale covering composition/base change, affine pullback spectra,
  finite-presentation base change/composition, and local Noetherianity.
- `lem-sfb-fs-log-infinitesimal-criterion` has no recorded Lean statement yet and
  is only a proof dependency, not a notion needed to type this statement. It is
  named in the full proof docstring; no invented module is imported for it.

Source read: the local ILO PDF, VI 1.1--1.8 (printed pp.69--70), VIII
3.3.4--3.3.11 (pp.107--108), and X proof of 1.2 and beginning of 1.1/1.3
(pp.138--139). VIII 3.3.11 explicitly states saturated log blowups are log étale;
VIII 3.3.8--3.3.10 gives their universal property, strict compatibility and towers.
The general criterion is attributed to Kato 1988 Theorem 3.5 as in the node;
its proof is postponed in the DAG criterion node, not fabricated here.

Edge checks before writing:

- Empty schemes: chart conditions are pointwise; an empty family is a cover only
  of an empty source. No `Nonempty` binder excludes this case.
- Tower length zero: `Fin (0 + 1)` has only the initial/final level, so the final
  clause asserts log étaleness of the genuine identity, with no arrows required.
- Principal centers and the unit ideal: these give identity blowups through the
  universal property; no nontriviality hypothesis excludes them.
- Trivial log structures recover the ordinary composition and strict pullback
  statements. Arbitrary characteristic is retained; invertible-order restrictions
  occur only inside the dependency's actual chart criterion.
- Strictness is canonical: the equivalence is constrained by the characteristic
  relation induced by section maps, excluding an unrelated abstract isomorphism.
- Both universes u and v are explicit; arbitrary family size v is retained.

Searches actually run (recorded by msearch in searches.jsonl):

- LeanFinder: "Log smooth morphisms of fine saturated log schemes are stable under
  composition and strict base change; saturated log blowups are log etale".
  Eight hits on ordinary smoothness/étaleness composition and base change; none
  state logarithmic permanence or saturated blowup étaleness.
- Loogle: "IsLogSmooth, IsLogEtale". Zero hits; unknown identifier IsLogSmooth.
- Mathlib grep: "IsLogSmooth|IsLogEtale|log_smooth|SaturatedLogBlowup". Zero hits.
- LeanSearch: "Log smooth morphisms compose and saturated logarithmic blowups are
  log etale". Eight hits on ordinary smooth/étale ring maps and schemes, no match.
- rg of upstream WeilConjectures and project Sheaf for those predicates and
  blowups: the project has the dependency definitions and statements consuming
  them, but no live theorem stating this item. rg of upstream for the item id
  found nothing. The former dropped per-node has the identical natural-language
  statement and an archived signature, but its module is deleted, explicitly
  noted in its lean record. It cannot supply an existing declaration. This
  delivery states the live sfb node with its own approved seven-step proof plan;
  it does not import or add a dependency on the dropped per theorem.
- The new theorem name was searched in both roots and was absent.

No mathematical statement correction and no new DAG nodes are needed.
No STATEMENT-DISPUTED issue was found.

## Repair of return L (immutable head 501e6f29638e)

Inspected the retained packet and ran the prescribed saved-packet dry run first.
It rejected the direct LogFanChartBlowup import because that provider is a legacy
non-module file. The saved packet already contained no duplicate definitions.

The current server source now differs from the older read clone. Read both live
modules using scompile.py --source: FSStrictLogMorphism is a published module-mode
provider of CharacteristicRelation, IsStrict and IsIdentity. LogFanChartBlowup now
imports it and no longer declares these names. The three signatures and bodies
match the original definitions verbatim. Replaced the item's public import with
FSStrictLogMorphism. No definition is copied, renamed or delivered. This reuses
the canonical declarations after their maintainer-side extraction and resolves
both the returned collision and the legacy import boundary.

Refreshed the item node from the shared read clone, preserving only this packet's
lean record. No mathematical statement, dependency list, proof or docstring changes.
The sole delivered declaration remains fsLogSmooth_composition_strictBaseChange
with its one expected sorry. No new node or dependency module is needed: the
existing module is already published on the live server.

## Second reading by Q17

Self-check of the retained statement for this repair (no independent agent was
started, as required by the dispatcher): the eight conjuncts correspond to smooth
composition, étale implies smooth, mixed composition, existence of strict products,
permanence for any product representative, strict étale locality, blowup étaleness
and tower étaleness. CompEq includes section maps, IsStrict is normalized by the
canonical characteristic relation, and IsIdentity fixes all relative étale sections.
No signature or hypothesis changed during repair; the dependency import alone moved
to its current canonical provider. The maintainer's independent reading remains
required. Explicit universes u/v and autoImplicit false retain all stated sizes.

Validation: prescribed scompile.py compiled the published strictness overlay
(7.8 s), the sandbox statement (5.2 s), and the library-path statement (4.9 s)
without errors or warnings. Structural self-check confirms only lean differs
from the shared node, lean.statement is verbatim, the only declaration is the
item theorem with one sorry, and the maximum Lean line width is 83 characters.
