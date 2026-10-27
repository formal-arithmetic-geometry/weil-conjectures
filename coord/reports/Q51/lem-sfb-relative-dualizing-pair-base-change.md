## Worker report

Stage 2, Q51, 2026-10-23. The live node is split and reviewed PASS by Q110 but has
no Lean record. The explicit stage-handoff paragraph of coord/brief-stage2.md §0
permits this statement delivery; the inherited stage-1 refusal does not apply.
The accepted statement, proof and proof dependencies are preserved.

The module Sheaf.AlgebraicGeometry.RelativeDualizingPairBaseChange states arbitrary
base change of the supplied predicate IsCoherentRelativeDualizingPair, and defines
its canonical diagonal and target comparisons with actual data. All newly
postponed proofs have docstrings specifying their source and proof steps; each is
a construction or clause of this owning DAG node, registered in lean.declarations.

Hypothesis and clause correspondence:

- Schemes X,S,S' are Scheme.{u}; u and the derived localization universe w are
  explicit. The families of HasDerivedCategory instances choose localizations,
  including those on opens required by the existing supplied-pair predicate.
- Separated, flat, locally finitely presented f are [IsSeparated f], [Flat f],
  [LocallyOfFinitePresentation f]. No properness, Noetherianity or quasi-compactness
  is assumed. g : S' ⟶ S is completely arbitrary; in particular not assumed flat.
- X' is pullback f g, g_X is pullback.fst f g and f' is pullback.snd f g.
  Mathlib infers the three stability instances on f'. Auxiliary constructions
  allow any commutative square; the invertibility theorem takes IsPullback.
- Supplied K is schemeDerivedCategory X, supplied ξ has source
  DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) and target
  (derivedPullback (pullback.fst f f)).obj K. The hypothesis h is precisely
  IsCoherentRelativeDualizingPair f K ξ, with no replacement predicate.
- K' is explicitly (derivedPullback (pullback.fst f g)).obj K. No object is
  chosen from a mere existence assertion.
- relativeDualizingProductMap is pullback.map with p on both factors. The named
  diagonal equality follows by the two projections and enables ordinary base change.
- relativeDualizingOrdinaryDiagonalMap is the existing adjoint-defined
  Scheme.Modules.moduleBaseChangeMap followed by pushforward of the structure
  sheaf pullback map tensorPullbackObjUnitToUnit. This pins the augmentation.
- relativeDualizingDiagonalBaseChangeMap applies the retained original universal
  counit recordedDerivedPullbackCounit to the degree-zero diagonal complex, then
  the single-complex comparison and the localization of the ordinary map.
  relativeDualizingDiagonalBaseChangeMap_isIso states that this actual map is
  invertible for every cartesian base change of the specified f. No map or iso
  is supplied as an extra hypothesis of the preservation theorem.
- relativeDualizingBaseChangeTarget composes recordedDerivedPullbackComposition,
  the first-projection equation, and inverse recorded composition. Its source
  and target are exactly Lh* Lp1* and Lp1'* Lg_X*.
- relativeDualizingBaseChangeClass is the inverse of the actual augmentation,
  followed by Lh*(ξ) and that target comparison. Its IsIso argument is proof
  data only; the theorem above supplies it, including for nonflat base change.
- isCoherentRelativeDualizingPair_baseChange concludes the same existing pair
  predicate on K' and that class. It states all three defining clauses at once:
  pseudo-coherence, locally finite relative Tor dimension, and invertibility of
  the class multiplication map.
- Identity: relativeDualizingBaseChangeClass_id says the resulting class followed
  by the first-projection pullback of relativeDualizingPullbackId is ξ. The unit
  is extracted from existing derivedPullbackComposition_coherence applied to the
  recorded universal counits and composition, so it is normalized to that structure.
- Iteration: relativeDualizingBaseChangeClass_comp uses two cartesian squares and
  their horizontal paste. The twice-pulled class, followed by Lp1''* of
  recordedDerivedPullbackComposition q p, equals the once-pulled class. This
  composition iso also supplies the corresponding identification of objects.
  The coherence lemma is stated for any such squares with invertible diagonal
  maps; the earlier invertibility theorem supplies each proof under the node's
  hypotheses. This is a general construction identity, not an extra hypothesis
  of the preservation theorem.

Dependency declarations used (the source docstrings and signatures were read):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.Proper / Separated: IsSeparated, the
  closed-diagonal clause of the proper-morphism dependency; IsProper is not
  assumed because the node requires only separatedness.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat (affine-local flatness,
  equivalently the stalk condition).
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  LocallyOfFinitePresentation (affine-local finite presentation).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst,
  snd, diagonal, map, lift_fst; IsPullback.of_hasPullback and paste_horiz.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: schemeDerivedCategory.
- WeilConjectures.AlgebraicGeometry.DerivedPullback: derivedPullback and its
  universal/K-flat specification.
- Sheaf.AlgebraicGeometry.RelativeDualizingPair: relativeDualizingDiagonalModule,
  relativeDualizingDiagonalComplex, IsCoherentRelativeDualizingPair.
- WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition:
  recordedDerivedPullbackCounit, recordedDerivedPullbackComposition,
  recordedPullbackData_E, recordedPullbackData_additive,
  recordedDerivedPullbackCounit_universal, recordedDerivedPullbackCounit_kFlat.
- WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence:
  derivedPullbackComposition_coherence, the normalized unit/composition coherence
  API underpinning the recorded composition dependency. The main composition
  theorem's existential counits were not freshly selected: doing that for a
  fixed derived functor could change its normalization. The recorded API retains
  the original presentation instead.
- WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction:
  Scheme.Modules.moduleBaseChangeMap (the fixed adjoint-defined map).
- WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf:
  Scheme.Modules.tensorPullbackObjUnitToUnit (adjoint to the structure map).

Four nodes are added to stmt_deps to expose the actual constructions used:
lem-pc-recorded-pullback-composition,
lem-pc-ringed-spaces-derived-pullback-composition,
def-sfb-tensor-pullback-structure-sheaf-map, and the new definition owner
def-sfb-module-base-change-map. No dependency module is needed. Already-stated
proof dependencies are imported with plain import, including affine comparisons,
Tor-independent base change, internal Hom restriction and horizontal pasting;
unstated proof dependencies are not assumed as hypotheses.

Sources: read literature/stacks-project/duality.tex, lemma-base-change-relative-
dualizing (Tag 0E2Y), including its definition of the derived class; and
literature/stacks-project/dualizing.tex, same label (Tag 0E2F), including its
explicit generator clause. The source's separated specialization is exactly the
live node, with the entire self-product as the diagonal neighbourhood.

Edge cases checked: identity g, two successive arbitrary maps, empty schemes,
zero/acyclic representatives, and nonflat g. No nonempty, domain, characteristic,
Noetherian, finite type base or flatness-of-g hypothesis occurs. A zero K is
allowed whenever the supplied predicate holds (e.g. empty source); nothing
assumes a chosen generator exists independently of h. Degenerate identity and
composite squares are included by the separate coherence equalities. The two
universe variables are retained, with no object/morphism universe identification.

Searches actually run:

- msearch.py leanfinder: "Pullback of supplied coherent relative dualizing pairs
  along arbitrary base change of flat locally finitely presented schemes";
  eight hits, all ordinary geometric flatness/stability or module pullback,
  none the supplied derived diagonal-class statement.
- msearch.py loogle: "AlgebraicGeometry.IsCoherentRelativeDualizingPair,
  AlgebraicGeometry.derivedPullback"; no hits (unknown project identifier).
- msearch.py grep: "RelativeDualizing|relativeDualizing"; zero Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for
  relativeDualizing.*[Bb]ase|RelativeDualizing.*[Bb]ase|relativeDualizingPullback;
  no existing base-change construction/statement found.
- rg for the exact item id under lean/WeilConjectures; no match.
- rg for dualizing|Dualizing under Mathlib/AlgebraicGeometry; no match.
- Source searches found DerivedPullbackRecordedComposition and its retained
  counit; reused these rather than reconstructing an arbitrary comparison.

No statement correction or disputed mathematics. The first retained draft timed
out because nested existential witness projections triggered expensive unfolding;
replacing these by the published recorded counit/composition fixed that issue.
Only prescribed scompile.py compiles and deliver2.py delivery checks are used.

## Second reading by Q51

A separate manual rereading in this worker session (no other agent was started,
as the dispatched brief prohibits it) compared the live node, source, predicate
and complete final module. The statement keeps separated/flat/lfp on f and leaves
g unrestricted. The diagonal source is ordinary pushforward in degree zero, not
a replacement derived direct image. The class is built from the actual canonical
augmentation, with its target comparison in the correct direction. The supplied
pair predicate is reused, so none of its finiteness or evaluation clauses are
lost. Identity and composition are equalities of classes after the existing
object comparisons, rather than mere existence of unrelated isomorphisms.
No silent statement change is required. The rereading caught the retained draft's
fresh-choice normalization risk and replaced it with the recorded universal
counit/composition. It also checked the composition lemma's paste orientation:
q then p upstairs, k then g downstairs. Definitions have actual data; theorem
proofs are sorry only. All helper declarations belong to this item's canonical
construction or explicit clauses and are listed in its Lean record.


## New nodes

def-sfb-module-base-change-map records the existing plain definition
AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap in
WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction (lines 35–50).
It introduces four schemes, four arrows, a commutativity equality and an arbitrary
module, exactly the Lean binders X S T X₁, f f₁ u₁ v, h and F. The source is the
canonical module adjunction of Stacks 0096 (lemma-adjoint-pullback-pushforward-modules),
applied to the ordinary mate underlying 08HY (remark-base-change). Its composite
uses the pushforward of the v-unit, pushforwardComp, pushforwardCongr h and inverse
pushforwardComp; inverse homEquiv for u₁ produces the required map. There is no
cartesianness, flatness or isomorphism assertion. The edge cases of identity arrows,
empty schemes and zero modules require no extra hypotheses. The node cites
precisely def-pc-scheme and lem-pc-module-pullback-adjunction, which supply its
schemes, modules, functors and fixed adjunctions. There is no new Lean module.

The repair's msearch.py LeanSearch query was "Canonical base change map for sheaves
of modules on a commutative square of schemes defined by pullback pushforward
adjunction": eight ordinary module-adjunction hits, none this map. Loogle query
"AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap" returned no hits (unknown
project identifier). Mathlib grep "moduleBaseChangeMap|baseChangeMap" under
AlgebraicGeometry/Modules returned zero hits. Project rg found the exact upstream
definition and Sheaf consumers. Searching all DAG definition records found only
other constructions (a derived-map predicate, the single-degree composite and
LinearMap.baseChange), with no owner of this plain map; the open-restriction node
is a theorem. blueprint_refs.py search "module base change" returned zero matches;
ancestor returned None, retained from the item's existing recorded ancestry.
The actual searches are recorded in the new node and searches.jsonl.

## Returned delivery repair

The immutable returned head e4a9b25fa0de had the same module and packet dependency
list as the saved packet. The initial dry run of that packet passed preflight and
compilation as b0f26406b0c, but the independent H2 finding still required repair.
Comparison with current live shows that the retained packet differs only in lean
and stmt_deps, and the item has not landed. This repair preserves the Lean file
and accepted statement/proof verbatim.

For the first H2 finding, replace
lem-weil-pbc-module-pullback-structure-sheaf in the added statement dependencies by
the landed def-sfb-tensor-pullback-structure-sheaf-map, whose existing:true record
owns tensorPullbackObjUnitToUnit. No isomorphism theorem for that ordinary map is
used in defining the diagonal augmentation. For the second H2 finding, replace
lem-weil-pbc-module-base-change-map-open-restriction by the new existing:true
owner def-sfb-module-base-change-map above. The theorem nodes are not re-recorded.
The two genuine derived-composition theorem dependencies remain, as accepted in
the return. The earlier report's "three" count is corrected to four dependency
additions: three existing nodes and one new definition node.

Second reading of the repair: the full module was reopened, including the ordinary
augmentation, normalized derived counit, preservation theorem and identity/composition
clauses. Its map calls use exactly the two plain definitions now owned by the cited
definition nodes. The new node's complete signature is copied verbatim from the
upstream def through its result type; its description is the actual inverse
homEquiv composite in that body. The existing tensor structure-sheaf definition
was likewise reopened and agrees with its owner node. No mathematical statement,
object, hypothesis, universe, or class comparison changes in this repair.

The repaired dry run required the new node schema key import_flags; it is now
explicitly empty. Its theorem-node advisory names the same two genuine derived
composition dependencies already judged and accepted in the maintainer return.
Server compilation passed before this metadata-only schema repair.
