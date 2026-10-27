## Worker report

The delivery states `lem-per-admissible-modification-completion-density` in
`Sheaf.AlgebraicGeometry.AdmissibleModificationCompletionDensity`, with main theorem
`AlgebraicGeometry.admissibleModification_completion_density`. It adds the missing
presentation of compatible pointed blowup diagrams in
`Sheaf.AlgebraicGeometry.AdmissibleCompletionPointSystem`. There are two postponed
proofs: the main theorem and `completionPowerQuotientMap_square`, the named
well-definedness equality used to construct its canonical closed-fibre map. All
other delivered declarations are definitions with real data; no theorem is proved.

The primary node's mathematical statement, proof and proof dependencies are unchanged.
Its statement dependencies gain only the new definition node named below. The source
was read directly: ILO XX 4.4, printed pp.373--374 (physical PDF pages 379--380), and
XX 2.4.3--2.4.4, printed pp.364--365 (physical pages 370--371). The source calls the
full-support domination system a filtered preorder and describes the same canonical
Rees congruences. The resolved Q112 stage-1 repair note was read; no withdrawn proof
or attachment was revived.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* A commutative ring: `{A : Type u} [CommRing A]`.
* A henselian pair: `(I : Ideal A) [HenselianRing A I]`, using the recorded
  henselian-pair declaration and its established equivalent idempotent criterion.
* Finite generation of I: `(hI : I.FG)`. It also supplies the object J = I used
  for the structural map to the nonempty colimit.
* A' is the actual I-adic completion: every occurrence is `AdicCompletion I A`,
  and its map is `algebraMap A (AdicCompletion I A)`. No abstract completion or
  arbitrary homomorphism replaces it.
* X and X' are the actual spectra, `Spec (.of A)` and
  `Spec (.of (AdicCompletion I A))`.
* Every finitely generated J with V(J) = V(I): the first conjunct quantifies
  `(J : Ideal A)`, `J.FG`, and `J.radical = I.radical`. Equality of radicals is
  exactly equality of these Zariski closed sets.
* Y_J and Y'_J are `AffineBlowup J` and
  `AffineBlowup (J.map (algebraMap A (AdicCompletion I A)))`. They use the
  dependency's Rees Proj definition, not a newly axiomatized blowup.
* The canonical lift is the existing `AffineBlowup.hom` for that algebra map
  and the reflexive ideal-extension equation. Its structural square is the
  existing `AffineBlowup.hom_toSpec`. These are the affine construction used by
  `def-nagata-strict-transform-blowup-comparison`; the recorded global theorem
  is publicly available through `WeilConjectures.Blowup.BaseChange`.
* The nth fibre products are the two actual `pullback` objects in
  `admissibleCompletionFiberMap`. The completed ideal is `(I ^ n).map ...`,
  equal to `(I.map ...) ^ n` by `Ideal.map_pow`.
* The actual map on these fibres is `pullback.map`, using the blowup lift,
  `Spec.map completionPowerQuotientMap`, and the base completion morphism.
  The first conjunct asserts `IsIso` of this map for every n with `1 ≤ n`.
  This asserts an isomorphism of the actual arrow, with no unrelated iso witness.
* Compatible systems of geometric points: `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (S : AdmissibleCompletionPointSystem I Ω)`. The system's
  `point`, `completedPoint`, `closed`, `point_naturality`, `comparison_point`,
  `completed_point_naturality`, `completed_over` and `completed_comparison`
  are respectively the chosen points, closed-fibre factorization, domination
  compatibility and compatibility with the actual completion comparison.
  A common Ω supplies the same residue-field closure on corresponding fibres;
  the source's geometric point of the inverse limit can be represented in the
  algebraic closure of its residue field, which also points every stage.
* Domination is not replaced by inclusion of ideals. `AdmissibleBlowupIndex I`
  has every FG ideal with radical I as an object. A morphism J → K is exactly
  an X-morphism Bl_K → Bl_J, by `InducedCategory (Over (Spec A))` and opposite.
  This is the category version of the source's preorder; the source proves
  uniqueness of these arrows for full-support ideals. No ideal is omitted.
* The strict henselizations are exactly `Scheme.strictHenselizationRing` from
  the dependency record. `rings_obj` and `completedRings_obj` identify the
  diagram objects with these actual rings. `rings_map`, `completedRings_map`
  and `comparison_app` identify every arrow with `pointedStrictLocalRingMap`.
  That helper is only `Spec.preimage` of the already-defined canonical
  `Scheme.strictHenselizationMap`, with equality transports of geometric points.
  Thus no arbitrary ring map or arbitrary isomorphism is substituted.
* The ring diagrams and their natural transformations in S are a presentation
  of the induced canonical diagrams, including their functor laws. They do not
  assume the main congruence, stagewise quotient bijectivity, flatness, or
  completeness of a strict-local ring. Uniqueness of pointed strict-local maps
  makes the indicated coherences automatic for the source's compatible system.
* B and C are the actual Mathlib colimits `S.sourceRing = colimit S.rings`
  and `S.targetRing = colimit S.completedRings`.
* u is `S.colimitMap = colimMap S.comparison`, the map induced by the specified
  stage maps. The structural map A → B is `S.sourceBaseMap hI`, the canonical
  structural map at J = I followed by the coprojection. Naturality makes this
  agree with every stage's structural map. Composition with u is the canonical
  A → C: the stage comparisons lie over the completion map and original base.
* The second conjunct asserts `Function.Bijective` of
  `Ideal.quotientMap (((I ^ n).map αB).map u) u Ideal.le_comap_map`.
  Its source is B/I^n B. By `Ideal.map_map`, its target is C/I^n C for the
  canonical structural map αC = u ∘ αB. This is the actual induced quotient
  homomorphism, so bijectivity says precisely that it is a ring isomorphism.
* The last conjunct binds φ in B and assumes exactly
  `I.map (S.sourceBaseMap hI).hom = Ideal.span {φ}`. Its conclusion is the
  canonical quotient map from `B ⧸ Ideal.span {φ ^ n}` to
  `C ⧸ (Ideal.span {φ ^ n}).map u`. By `Ideal.map_span`,
  `Set.image_singleton` and `map_pow`, the target ideal equals
  `Ideal.span {(u φ) ^ n}`. This is exactly φ' = u(φ) and the displayed
  principal-power quotients, without requiring φ to be regular or nonzero.

Dependency declarations read and used:

* `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianRing`
  (from Mathlib), with the node's idempotent interpretation already recorded.
* `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its commutative ring/algebra structures and canonical algebra map.
* `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
* `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`.
* `WeilConjectures.Blowup.Affine.Functoriality` and `.BaseChange`, exposed by
  `WeilConjectures.Blowup.BaseChange`: `AffineBlowup.hom`,
  `AffineBlowup.hom_toSpec`, `AffineBlowup.isClosedImmersion_pullbackLift`;
  the recorded global
  `Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap` uses this
  same affine comparison, as its source and chart formulas explicitly show.
* `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, the actual small affine-etale colimit.
* `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`:
  `Scheme.strictHenselizationMap`, uniquely characterized over the base and
  geometric-point evaluation. Its source and `strictHenselizationMap_existsUnique`
  were read; it invokes the recorded `strictHenselizationFunctoriality`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.map`, projections and canonical universal maps.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points
  are the recorded inline `Spec (.of Ω) ⟶ Y` encoding. Also read the recorded
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
* `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `colimMap`.
* `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.quotientMap`,
  `Ideal.quotientMap_comp_mk`; `Ideal.map_map`, `Ideal.map_pow`,
  `Ideal.map_span` justify the equivalent target-ideal spellings.

Available proof-dependency modules are ordinary imports of the theorem module.
`lem-per-admissible-modification-system` currently has no recorded Lean module,
so there is no import to add for that proof dependency; it is not needed to type
this statement. It is not used as an assumption. Its future proof supplies the
filteredness invoked by the main theorem's complete proof docstring. All remaining
stated proof dependencies are imported directly or by their publicly imported
owning modules. The direct category is thin, so its directed-preorder presentation
can be used with the existing finite-data lemma when the proof is written.

Edge cases checked before writing and during the second reading:

* I = 0 and the empty generating list: the completion is A, full-support J
  has nil radical, and blowups of the zero/nilpotent centres are empty where
  appropriate. The first clause remains valid. No geometric point system is
  demanded on an empty fibre. When a system exists it contains every index.
* A is the zero ring: no Field/nontrivial assumption is imposed on A. Scheme
  and fibre comparisons include empty schemes. A point-system binder can be
  empty without excluding the independent scheme conclusion.
* J = I is always present under hI; equal or mutually dominating ideals are
  not identified or discarded, and all actual arrows remain in the category.
* I = top is compatible with the henselian-pair hypothesis only for the zero
  ring; it is not silently excluded. The source's geometric closed-fibre choice
  naturally has no points in the empty case.
* The quantifiers are exactly n ≥ 1; no unrequested n = 0 conclusion is added.
* The principal case allows φ = 0, nilpotents and zerodivisors: no Cartier,
  regularity, domain or nonzero hypothesis is added.
* All rings, the all-ideals index, its hom sets, and the geometric points use
  the common universe u. No smaller independent test universe is introduced.

Searches for an existing statement and the new definition:

* msearch LeanFinder, `Admissible blowups over a ring and its adic completion
  have isomorphic closed fibres and strict henselization quotients`: 8 hits,
  including `IsAdicComplete.henselianRing`, `AdicCompletion.factor_evalₐ_eq_eval`
  and Weierstrass-preparation statements. None compares blowups or these colimits.
* msearch Loogle, `AdicCompletion, AffineBlowup`: 0 hits; it reports
  `unknown identifier 'AffineBlowup'` because this search service indexes Mathlib.
* msearch grep, `blowup.*completion|completion.*blowup`, AlgebraicGeometry:
  0 hits. Grep for the item id in WeilConjectures and Sheaf: no declaration.
* msearch LeanSearch, `The category of full support admissible blowups with
  compatible geometric points and strict henselization ring diagrams`: 8 hits
  for general limits, gluing, affine spectra and pullbacks, no matching system.
* msearch LeanFinder, `Compatible pointed admissible blowup systems and their
  canonical strict local ring colimit comparison`: 8 hits for gluing,
  Spec-to-local-ring equality, finite data and valuative criteria, no match.
* msearch grep of Mathlib for
  `AdmissibleBlowup|admissibleBlowup|CompletionPointSystem|pointedStrictLocalRingMap`:
  0 hits. Source/project grep also finds ordinary admissible-blowup names:
  `IsAdmissible` in `WeilConjectures.Blowup.AdmissibleBlowup` describes one
  centre away from a preserved open, and `AdmissibleBlowupDatum` in
  `Sheaf.AlgebraicGeometry.AdmissibleLocalFreeGluing` packages one such blowup.
  Their signatures and docstrings were read; neither supplies this pointed
  completion system. The narrower search
  `AdmissibleBlowupIndex|CompletionPointSystem|pointedStrictLocalRingMap` has
  no hits in either source directory. Individual affine blowup maps and canonical
  strict-local maps exist and are used.
* `tools/blueprint_refs.py search admissible`: 165 blueprint matches; none
  defines this compatible completion point system. DAG grep found the item
  and related admissible-modification lemmas, not another definition of this data.
* `dag/lean_names_upstream.json` was consulted for the blowup maps and for
  potential name collisions. The new names have no existing declarations.

No statement dispute or mathematical correction is recorded.

Validation: both delivery modules were compiled individually in dependency order
using the prescribed `scompile.py` against the live build. The definition module
and theorem module are clean. No global build or direct repository mutation was run.

## New nodes

`def-per-admissible-completion-point-system` supplies the missing definition of
compatible geometric points on every full-support admissible blowup and its
corresponding completed blowup, together with their specified canonical strict-local
ring diagrams, structural transformation, colimits and induced comparison. Source:
ILO XX 4.4 pp.373--374 and XX 2.4.4 p.365; the canonical maps use Stacks 04HX/04GU
through the existing project declarations. The node records the actual msearch
LeanSearch, LeanFinder and Mathlib grep results and the source/project/DAG searches.
The admissible-modification-system lemma describes filteredness and comparison
properties; it does not define this compatible pointed data. The new module does
not state or assume those properties and does not duplicate a blowup or a strict
henselization. The auxiliary definitions in its `lean.declarations` give the index,
canonical individual ring maps, actual colimit objects and actual induced arrow.
The sourceBaseMap selects the available J = I stage, not an unprovided basepoint.

## Second reading by N8

Author's separate second reading; the maintainer supplies the independent review.
I reopened both node copies and both Lean files and checked the clauses above
against the actual signatures. In particular, I checked the direction of opposite
index arrows (K dominates J), the direction of strict-local ring pullbacks (H_J to
H_K), the source and target of `Spec.preimage`, and the equality transport in
`pointedStrictLocalRingMap`. The equality there is h.symm, taking H_x to H_(y f).
The comparison components are from H_J to H'_J and `colimMap` therefore goes B to C.
The closed-fibre map points from the completed blowup fibre to the original fibre;
its two square witnesses have the directions required by `pullback.map`.

I checked the henselian and finite-generation binders, all J and n quantifiers,
the full-support radical condition, the corresponding geometric points, both
colimits, the actual induced map u, and the principal specialization with exactly
the single hypothesis IB = (φ). The codomain ideal spellings are equal ideals,
using the named Mathlib map lemmas; they do not assert comparison with a different
completion or strict-local object. I checked that the helper structure contains
no bijectivity/congruence assumption and no flatness or excellence hypothesis.
The only elaboration repairs were marking the extracted domination map
noncomputable and writing its full name instead of unsupported field notation;
line-width warnings were removed. The statement did not change. The first clean
combined compile covers each file separately in dependency order.

The first prescribed `deliver2.py --no-push` passed with a clean per-file compile
and server preflight. A final search-summary edit distinguishes the existing ordinary
admissible-blowup vocabulary from the absent compatible pointed completion system;
the definition and theorem files are unchanged from the clean compile.
