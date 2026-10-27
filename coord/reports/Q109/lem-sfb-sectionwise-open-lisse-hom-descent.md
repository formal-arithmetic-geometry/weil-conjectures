## Worker report

The module `Sheaf.Paper.SectionwiseOpenLisseHomDescent` states
`AlgebraicGeometry.ProEtale.sfbSectionwiseOpenLisseHomDescent` with `sorry`.
Its six helper definitions have actual data. No theorem was proved. The node's
natural-language statement and seven proof steps are unchanged.

Source read: the complete item, every statement dependency and its recorded
declaration/docstring, Q103's split/review record, and the current blueprint
direct-images proof, paragraph (3). The blueprint invokes the surrounding open
coefficient argument; the item explicitly identifies its matrix/gluing lemma as
an extracted auxiliary assertion, rather than a verbatim blueprint theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any scheme and open immersion: `{X V : Scheme.{u}} (j : V ⟶ X)` with
  `[IsOpenImmersion j]`. There is no quasi-compactness, connectedness,
  separation, reducedness or Noetherian assumption.
- Arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is
  the unbundled form of the recorded `Profinite.CondensedRing`; it does not
  assume a topological-ring presentation.
- Pulled-back coefficients and internal modules: `condensedRingObj Λ X`
  is the recorded point pullback, and `M N : Mod (Sheaf
  (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)` are internal
  modules over it. `CondensedRing.upperStar` is the existing ringed-topos
  inverse image, including its extension of scalars.
- Every affine pro-etale test object: `hsec` quantifies over every
  `W : X.ProEt`, assuming only `IsAffine W.left`. Its asserted bijective map
  is `sfbOpenHomCoefficientRestriction Λ j W`, the composite of the actual
  localization section map `sfbCoefficientSectionMap Λ W` and the actual
  coefficient global-section map along `pullback.fst W.hom j`. Its source
  is exactly the value of Λ_X at W, and its target is Γ(W_V, Λ_(W_V)),
  canonically Γ(W_V, Λ_V) by coefficient localization. No affineness of
  W_V is imposed. Neither factor is an arbitrary chosen isomorphism.
- Lisse modules: `hM` and `hN` use the recorded
  `IsLisseCoefficientModule`. Its `Mod.IsFree` is explicitly finite free
  of some natural-number rank on each covering member, including zero.
- Actual Hom bijection: the existential equivalence `e` goes from
  `M ⟶ N` to `j^*M ⟶ j^*N`; its first conjunct identifies its value on
  every map with `(CondensedRing.upperStar Λ j).map`. Thus its inverse
  is uniquely determined; it is not an arbitrary equivalence between Hom sets.
- Every common affine trivializing cover and every pair of bases: `C`
  ranges over `Scheme.Cover.{v} Scheme.proetalePrecoverage X`, with its
  own independent index universe `v`; `hC` requires every member affine.
  The functions `a b : C.I₀ → ℕ` permit varying ranks, and `α β` are the
  specified trivializations. There is no restriction to a chosen cover.
- Entrywise inverse coefficient restriction: for every `i`, `row : Fin
  (b i)` and `col : Fin (a i)`, the matrix-entry clause computes the
  local matrix of `e.symm u` using these bases. The right-hand side applies
  `Equiv.ofBijective ... (hsec ... (hC i))` inversely to the local matrix
  of `u`, then applies the canonical source identification θ_W. This
  last θ_W is necessary because the inverse lands in Λ_X(W), whereas the
  displayed matrix entry is a global section of Λ_W. The two descriptions
  are exactly the coefficient localization identification.
- Restricted bases: `upperStar.mapIso α` and `upperStar.mapIso β` are
  followed by the already recorded `coefficientHeartFiniteFreePullbackIso`.
  The map on the open fibre is `sfbOpenHomPullback Λ (C.f i) j u`,
  conjugating the actual pullback of `u` by the composition comparisons.
  The matrix entry evaluates `ι_col ≫ h ≫ π_row` at the global unit;
  this is the usual b-by-a orientation, with no copied module structure.
- Cover and basis independence: the same inverse `e.symm` satisfies this
  formula for every `C`, `α` and `β`. Since the forward map is fixed, the
  equivalence itself is unique. No auxiliary equivalence or inverse is
  chosen separately for a cover or for its bases.
- Overlap refinements: for any pair of covering members and any small-site
  object `T` with site morphisms to both members, the `HEq` conjunct
  identifies the two restricted local extensions. The helper
  `sfbOpenHomCompositePullback` identifies iterated pullback with pullback
  along the composite. `HEq` is needed only because those two composites
  are equal scheme arrows rather than definitionally identical arrows.
  This ranges over all overlap refinements, including nonaffine ones.
- Unique gluing: the last cover conjunct quantifies over every family `k`
  of local maps whose actual restriction is the pulled-back `u`, and asserts
  `∃! h`, with exactly those local restrictions. The inverse matrices give
  such a family; its unique glue is `e.symm u`. Agreement and unique gluing
  use actual module maps, not only underlying functions or matrices.
- Base change: the final quantifiers introduce arbitrary `Y` and `f : Y ⟶ X`.
  The square is the actual `pullback f j`, with open map `pullback.fst f j`
  and projection to V `pullback.snd f j`. The two following hypotheses
  are exactly the analogous affine coefficient bijections on Y and
  lisseness of both pulled-back modules. The resulting `e'` again has
  actual open restriction as its forward map. The last equality is
  `f^*(e.symm u) = e'.symm (sfbOpenHomPullback Λ f j u)` for every u.
  `sfbOpenHomPullbackComparison` is the composite of the inverse of
  `upperStarComp` on one side, transport along `pullback.condition`,
  and `upperStarComp` on the other. Thus the asserted equality includes
  the required canonical coefficient identifications explicitly.
- This concerns morphisms between M and N supplied on X. There is no
  assertion of essential surjectivity or extension of arbitrary objects.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, whose
  unbundled ring-object encoding supplies the coefficient parameters.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, the underlying object of `coefficientRing`, with the
  inherited monoid and commutativity instances.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology,
  `Scheme.proetalePrecoverage` and
  `Scheme.proetalePrecoverage_le_precoverage_weaklyEtale`. The cover-object
  helper extracts its witness using the covering's `mem₀`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its Hom and
  regular module. `WeilConjectures.CategoryTheory.ModuleObjects.Free`:
  `Mod.finiteFree`, the finite biproduct of regular modules.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor` and its relocalization interface are
  the recorded slice conventions, used by the proof plan.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar` and `CondensedRing.upperStarComp`.
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`:
  `sfbCoefficientSectionMap`, `sfbCoefficientGlobalMap`, `sfbSectionOne`,
  owned by the new `def-sfb-coefficient-section-maps` existing:true record.
  The localization theorem remains a proof dependency, as on the accepted base.
- `Sheaf.Paper.CoefficientHeartCurveLisseDescent`:
  `coefficientHeartFiniteFreePullbackIso`, owned by the new
  `def-sfb-coefficient-finite-free-pullback` existing:true record. Its
  construction works for all scheme morphisms and all natural-number ranks.
  The curve-descent theorem is not a statement dependency.
- Plain proof imports retain the recorded internal/sectionwise equivalence,
  `homObj_isSheaf_and_sections`, covering axioms, affine-open basis, and
  weakly-etale stability. The free-matrix proof-dependency node has no
  Lean binding on the read base, so it has no proof import yet; it is
  not needed to type the statement.

Edge cases checked:

- Rank zero: the relevant `Fin 0` index is empty, so the matrix clause
  is vacuous exactly for the empty matrix. Finite-free objects still
  exist and the Hom equivalence and gluing clauses remain present.
- Empty scheme: empty covers and their empty rank/basis functions are
  allowed. Unique gluing then asserts the singleton Hom set, as required.
- Empty open V: the coefficient hypothesis forces the coefficient sections
  on each affine test object to be zero; lisse modules are then zero,
  so this is a valid case, not an omitted exception.
- Identity open: the actual restriction and inverse reduce under the
  canonical identity comparisons to the identity. The theorem still
  includes this case and arbitrary base changes.
- The zero coefficient ring is permitted; no nontriviality hypothesis is
  present. Varying ranks, nonaffine open fibres and nonaffine overlaps
  are permitted. Cover indices live in independent universe v; the small
  site has object universe u+1 and morphism universe u, with Ab in u+1.

Searches actually run using msearch.py:

- LeanFinder: "Restriction of morphisms between lisse finite locally free
  sheaves is bijective if coefficient sections restrict bijectively on
  every affine pro etale object". Eight hits, led by
  `PresheafOfModules.homEquivOfIsLocallyBijective`; the latter concerns
  precomposition along a locally bijective map on one fixed ringed site,
  not open inverse image under an affine coefficient-section hypothesis.
  Other hits concern locally bijective sheaf maps and scheme stalks.
- Loogle: `"SheafOfModules", "restrict", "Bijective"`: zero hits.
- Mathlib grep: `(lisse|Lisse).*(hom|Hom)|(hom|Hom).*(lisse|Lisse)`:
  zero hits.
- LeanSearch: "Restriction to an open subscheme is fully faithful on
  finite locally free coefficient modules when coefficient sections
  restrict bijectively on an affine basis". Eight hits, including
  `Scheme.Modules.restrictFunctor`, `restrict_obj`, `morphismRestrict`
  and `IsOpenImmersion.isoRestrict`. These are scheme-structure-sheaf
  constructions and do not assert the item.
- `rg` of both project roots for the item id and open-lisse-Hom-descent
  names found no existing declaration. Further searches for free-matrix
  helpers found only private continuous-field-specific matrices; these
  require a topological field realization and do not apply here.
  The public canonical finite-free pullback comparison was found in
  `CoefficientHeartCurveLisseDescent` and reused directly.

No dependency module repair, statement correction or `STATEMENT-DISPUTED`
flag is needed. The new definition nodes supply ownership of existing helpers.
The first compiler pass exposed only
the missing implicit conversion of a pro-etale cover member to a site
object; the real-data `sfbOpenHomCoverObject` fixes it without a new
mathematical assumption. The matrix formula explicitly applies θ_W at
the end of inverse coefficient restriction to keep its two section
encodings aligned.

The previous worker's rejection referred to Q103's stage-1 split. This
packet adds the missing stage-2 Lean binding; it does not resplit the node.
The initial dry-run attempt in this session confirmed that the retained
sandbox had no node or Lean file, only dispatcher markers.

Validation: the final module compiled cleanly in both sandbox and real
module modes through scompile.py (5.2 and 14.7 seconds), including the
restricted-to-site overlap formulation. There are no compiler errors or
unexpected warnings. Delivery preflight is run through deliver2.py.


## Repair of returned delivery

Return L on immutable head `0a481d34ddc3` identified H2 and theorem-stmt_dep
faults: the packet cited two theorems while using only their real-data helper
definitions. The initial required dry run of the retained packet passed
mechanically (`f42a3926a34`), but the independent review finding still required
this repair. The item now cites the two definition nodes below instead of
`lem-sfb-coefficient-sections-localization` and
`lem-sfb-coefficient-heart-curve-lisse-descent` as statement dependencies.
The former remains in the unchanged proof_deps. Every original base field
except `lean` and the authorized statement-dependency additions is retained.
The original Lean module is retained byte for byte: the review accepted all its
hypotheses, conclusions, edge cases, comparisons and genuine helper data.

## New nodes

`def-sfb-coefficient-section-maps` owns the exact existing
`sfbCoefficientSectionMap`, `sfbCoefficientGlobalMap` and `sfbSectionOne`
definitions in `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`.
The signature recorded verbatim is that of the section map; the declarations
list includes all three. Theta evaluates the coefficient mate then restricts
along the diagonal, the global map evaluates the same mate at the final object
and restricts along its graph, and the unit evaluates the internal ring unit.
These are exactly the maps of the auxiliary coefficient-localization argument
in item proof step 1 (Stacks 00Y0, 03CE and 03EH). There is no assertion of
invertibility in this definition node and no duplicate construction.

`def-sfb-coefficient-finite-free-pullback` owns the exact existing
`coefficientHeartFiniteFreePullbackIso` definition in
`Sheaf.Paper.CoefficientHeartCurveLisseDescent`. It records precisely its
finite-biproduct comparison followed by the canonical regular-module
comparison, used to restrict the bases in item proof step 3. The source is the
same direct-images auxiliary argument. All f and n are allowed, including
zero; neither a closed immersion nor a curve hypothesis occurs in its full
signature. The coefficient map and its inverse give the comparison on every
regular summand, so no arbitrary basis choice is introduced.

Searches for both nodes: msearch LeanSearch, query "Canonical coefficient
section maps from the coefficient mate and finite free module pullback
comparison for commutative condensed rings on the pro etale site", returned
8 hits (including SheafOfModules.pullbackObjFreeIso); reading that declaration
showed it concerns sectionwise sheaves and not the present internal-module
comparison. Loogle `"Mod", "finiteFree"` and Mathlib grep of the four helper
names each returned 0 hits. Exact results and digests are in both nodes'
mathlib_searches. Project/DAG rg found only these existing implementations and
their parent theorem records; no definition node owns them. Thus existing:true
records, with no new modules, follow H12 and the explicit return instruction.
blueprint_refs search found 2 coefficient-section and 38 finite-free blueprint
matches, none owning these definitions. The ancestor command returns None;
both nodes retain that null ancestor and prepend the item to its via chain.

## Second reading by Q109

Self-check in this repair session (no independent reader is claimed; the
assignment forbids starting another agent): opened the saved item, its full
Lean module, both existing helper implementations and their records. The
returned review had already checked every mathematical clause. Rechecked that
all nine original stmt_deps remain, both added theorem stmt_deps are absent,
and precisely the two new definition nodes replace them. Each helper's exact
name, universe u, parameters, codomain and real-data body matches its new
node: theta and global map require no monoid binder; the evaluated unit needs
MonObj; the finite-free comparison needs MonObj and IsCommMonObj. Independent
cover-index universe v remains bound in the unchanged theorem. Both existing
signatures are taken verbatim from their source. No theorem conclusion is
claimed as definition data. This fixes the one numbered return finding.

Repair validation: scompile.py compiled the retained module cleanly in sandbox
and library modes (8.8 s and 12.0 s). The repaired packet passed deliver2.py
--no-push at 32765e9ddc7, including its generated module-mode checks of all four
existing definitions and the server preflight. No errors or unexpected warnings.
