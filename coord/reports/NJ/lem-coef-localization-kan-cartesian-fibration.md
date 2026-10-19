## Worker report

The module `Sheaf.CategoryTheory.LocalizationKanCartesianFibration` defines
`SSet.Enhanced.cartesianLocalizationDiagrams` and states
`SSet.Enhanced.localization_kan_cartesian_fibration`.  The helper is the full
simplicial subcomplex of the internal hom on the pullback
`pullback η π`; its vertex predicate sends every edge whose image under the
canonical projection `pullback.snd η π` is an equivalence in `E` to an
 equivalence in the target `T`.  The theorem quantifies over small
quasicategories `W`, `K`, and `E`, a weak equivalence `η : W ⟶ K` with Kan
replacement target, and a Cartesian fibration `π : E ⟶ K`.  For each target
`T` in `SSet.{max (u + 1) v}` with `T.Quasicategory`, it supplies a map from
`Fun(E,T)` to the helper subcomplex, identifies its composite with the actual
precomposition map along the lifted pullback projection, and asserts both
`IsFunctorEquivalence` and `IsFullyFaithful`.  The latter records all mapping
spaces and hence allows noninvertible coherent transformations.

The Lean rendering of each hypothesis and clause is as follows.

* `W`, `K`, and `E` are `SSet.{u}` with `[Quasicategory W]`,
  `[Quasicategory K]`, and `[Quasicategory E]`.
* `η : W ⟶ K`, `[KanComplex K]`, and
  `hη : IsWeakHomotopyEquivalence η` encode the chosen Kan fibrant replacement.
* `π : E ⟶ K` and `hπ : cartesianFibration π` encode the Cartesian fibration,
  using the recorded inner-horn and Cartesian-edge interface.
* The target clause is `∀ (T : SSet.{max (u + 1) v}), T.Quasicategory →`;
  the explicit `uliftFunctor` maps place the small source and pullback in this
  containing universe.
* The full subcategory is
  `cartesianLocalizationDiagrams (uliftFunctor.map η) (uliftFunctor.map π) T`.
  Its predicate is
  `∀ e, IsEquivalenceEdge E ((pullback.snd η π).app _ e) →
  IsEquivalenceEdge T (...)`, with the target evaluation written through
  `h.app (op ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op e`.
* The supplied comparison `e` has the displayed internal-hom type, and the
  equality after its inclusion is exactly precomposition by
  `pullback.snd` of the lifted maps.
* `IsFunctorEquivalence e ∧ IsFullyFaithful e` is the identification of the
  complete coherent functor categories, including all higher transformations
  and mapping spaces.

The statement dependencies used are:

* `Sheaf.CategoryTheory.CompleteAlgebroid`, declaration
  `SSet.Enhanced.Algebroid.completeCategory` for the stated infinity-category
  and universe conventions (and its imported enhanced-diagram interfaces).
* `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, declaration
  `SSet.Enhanced.cocartesianFibrationOver`; the theorem uses the same module's
  exported `cartesianFibration` and `IsCartesianEdge` interface.
* `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen`, for the Kan--Quillen and weak
  homotopy-equivalence conventions used by `hη`.

The stated proof-plan imports are retained: `SSet.Enhanced.infinity_cocartesian_mapping_criterion`,
`SSet.Enhanced.right_pinch_comparison`,
`SSet.Enhanced.mapping_composition`,
`SSet.AlgebraicTopology.relative_marked_anodyne_calculus`,
`SSet.AlgebraicTopology.path_fibration_replacement`, and
`SSet.Enhanced.infinity_functor_pushout`; the enhanced-diagram module supplies
`fullSubcomplex`, `IsFunctorEquivalence`, and `IsFullyFaithful`.

Edge cases checked before writing: `W` may be empty; the pullback and its full
subcategory then remain well-defined and the edge predicate is vacuous.  The
identity replacement `η = 𝟙 W` gives the expected restriction along the
identity pullback.  The identity fibration `π = 𝟙 K` reduces the condition to
inverting every edge of `W`: every image edge in the Kan complex `K` is an
equivalence. This is the groupoid-completion universal property.  Empty fibers and targets are allowed by
simplicial-set pullbacks and the universal full-subcomplex predicate.  The
containing-universe lift does not impose an equality between the small and
large universes.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "Cartesian fibration over a groupoid completion
  localizes the pullback at arrows mapping to equivalences"`: returned only
  ordinary Grothendieck and free-groupoid declarations, with no infinity-
  categorical localization match.
* `msearch.py ... loogle "cartesianFibration, IsCartesianEdge,
  IsFunctorEquivalence, fullSubcomplex"`: zero hits; `cartesianFibration` is
  not a Mathlib identifier.
* `msearch.py ... grep "cartesian.*fibration|groupoid.*completion|fullSubcomplex"`:
  no Mathlib match for the combined query.
* `rg` over `WeilConjectures/` and `lean/Sheaf/`: found only ordinary
  Grothendieck constructions and the distinct
  `SSet.Enhanced.simplicial_groupoid_localization`; no declaration with this
  Cartesian-fibration-over-groupoid-completion statement.

No `STATEMENT-DISPUTED` flag or node fault was found.  The released repair note
was read: the stage-1 re-split leaves the item's statement unchanged, so no
statement correction or new dependency node is required.

## Second reading by NJ

I reread the node, the repaired stage-1 proof route, the module, and all three
statement dependencies.  The source and target of the comparison map are the
lifted internal functor simplicial sets; its composite is the canonical
precomposition map along the actual pullback projection.  The helper predicate
mentions exactly the arrows whose image in `E` is an equivalence and imposes no
condition on transformations.  The two final predicates retain equivalence on
objects and all mapping spaces.  No hypothesis or conclusion was added or
removed, and the identity, empty, and universe cases above still typecheck.

The module compiled cleanly in both sandbox and library modes with
`scompile.py`; only the expected `sorry` proof remains.

The returned stage-1 repair was applied to the proof route.  The former first
step is now two elementary steps: the first uses
`lem-coef-kan-quillen-right-proper` for the same-universe Kan factorization and
universe enlargement, and the second uses
`lem-coef-infinity-pinch-comparison`, the existing
`lem-coef-infinity-cartesian-mapping-criterion`,
`lem-coef-infinity-cocartesian-mapping-criterion`, and
`def-coef-infinity-fibrations` for the opposite mapping-square/horn
identification.  The remaining steps were renumbered and their internal
references were checked: straightening is step 3, cofinality step 4,
localization step 5, the Kan-base equivalence calculation step 6, edge
reflection step 7, and the final functor-category assembly step 8.  The item
statement and its Lean record are unchanged.  The added proof dependency is
`lem-coef-infinity-cartesian-mapping-criterion`, imported from
`Sheaf.CategoryTheory.InfinityCartesianMappingCriterion`.

## Saved-packet self-check, 2026-10-17

The required first dry run passed preflight and compiled the saved module in
sandbox and library modes (dry-run commit `35c9c45688`). I compared the saved
node with the current shared node: the statement is unchanged, and all proof
steps after the split first step are unchanged except for their step-number
references. Every saved proof step is below 2000 characters (the longest is
1651). The already-landed Cartesian mapping criterion supplies the argument
previously carried inline, so no duplicate node or module is needed.

Delivery-tool limitation: the successful dry run explicitly reports that the
saved `proof` and `proof_deps` changes are NOT delivered because those fields
are not stage-2-owned. Thus the re-split described above is present in the
saved sandbox node, but this stage-2 wrapper carries only the Lean record,
module and report. The maintainer must not interpret the successful stage-2
packet as having landed those proof-field changes. The prescribed instruction
for this retry is to retain a passing saved packet and push it after this
self-check; no Lean statement or record has been changed in this retry.

## Retained-packet verification, 2026-10-17

The required first dry run for this retry passed at `4139de00b7`: server
preflight and separate sandbox/library compilation both succeeded. The saved
statement equals the current shared statement, and `lean.statement` matches the
module signature verbatim. The eight saved proof texts have lengths 525, 578,
750, 1651, 569, 1377, 430, and 622 characters. The Cartesian mapping criterion
is already recorded in the shared DAG with its landed module, so the saved
split uses that node without introducing a duplicate. The existing module and
Lean record were retained unchanged in this retry. As reported above, the
wrapper explicitly excludes the saved proof/proof_deps edits; this successful
stage-2 delivery does not claim to have landed those stage-1 fields.

## Final retained-packet check, 2026-10-17

The first dry run of this retry passed at `a759416b8f`, including server
preflight and separate sandbox/library compilation. I reread the saved module
and dependency interfaces and verified the recorded theorem signature verbatim.
The item statement is unchanged; the retained split has eight steps, all under
2000 characters, with later step metadata preserved. No statement, Lean record,
or module was changed in this retry. As the dry run explicitly reports, its
stage-2 commit excludes the saved `proof` and `proof_deps` edits. The retained
packet is pushed under the explicit retry instruction; its stage-1 re-split
still requires maintainer promotion through the appropriate stage-1 path.

## Maintainer second-reader correction, 2026-10-17

The independent immutable-delivery review corrected the identity-fibration edge
case above: it inverts every edge of `W`, not merely equivalence edges of `W`.
For example, `W = Δ[1]` and `K = Δ[0]` requires the unique nondegenerate edge
to become invertible. The delivered Lean predicate already says this exactly;
no Lean declaration, signature or node record needs changing. The immutable
module was reproduced with `scompile.py NJ
lem-coef-localization-kan-cartesian-fibration <snapshot module>`: separate
sandbox and library modes both passed without diagnostics (1.5 s and 1.6 s).
The installed wrapper used the server side overlay. No global build or direct
project edit was performed.
