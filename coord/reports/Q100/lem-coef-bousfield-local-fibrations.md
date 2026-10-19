## Worker report

The delivery states `CategoryTheory.BousfieldLocalization.fibration_iff_of_isLocal` in
`Sheaf.CategoryTheory.BousfieldLocalFibrations`, with `sorry` as its entire proof.
`IsLocal` and `localEquivalences` are real Prop-valued helper definitions belonging to
this node's local-object/local-equivalence terminology; all three declarations are
listed in `lean.declarations`. No independent new notion, dependency replacement,
statement correction, or disputed statement is needed. The node is unchanged except
for `lean`.

Source checked directly: Hirschhorn, *Model Categories and Their Localizations*,
[Proposition 3.3.16(1), printed p. 63](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf#page=77).
The printed source states the equivalence for local endpoints, without requiring
properness or combinatoriality. Its proof factors in the given localization, shows
the intermediate object local, and uses local Whitehead and lifting. The Lean docstring
contains all eight expanded steps of the DAG proof, including boundary degree zero,
the tensor of the initial object, the hammock-components bridge to ordinary localization,
and the final arrow retract.

Hypothesis and clause correspondence:

- The underlying category is `{M : Type u} [Category.{v} M]`. Its original model
  structure is `[ModelCategory M]`. `[HasLimits M]`, `[HasColimits M]` and both original
  `HasFunctorialFactorization` instances spell out exactly the model-category convention
  of `lem-coef-simplicial-model-nerve-localization`. The limits and colimits are properties
  of the same underlying category for both model structures.
- Simplicial enrichment is `[SimplicialCategory M]`; `_T : SimplicialTensorCotensor M`
  supplies the tensors/cotensors, and `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`
  is precisely the recorded SM7 property for the original structure. No localization
  simplicial structure is assumed.
- The small collection of arrows is presented by `{I : Type w} {A B : I → M}` and
  `s : ∀ i : I, A i ⟶ B i`. This is an arbitrary small family, not a finite family;
  repeated members do not alter the universal locality test. Every set of arrows has
  such a presentation, and a family defines its image set. `u`, `v` and `w` are explicit
  independent universes, with no equality imposed between category-object, hom or index
  universes.
- The original derived mapping convention is made concrete by `(Q : M ⥤ M)` and
  `(ε : Q ⟶ 𝟭 M)` with `_hQ` asserting for every object that `Q.obj Z` is original
  cofibrant and `ε.app Z` is an original trivial fibration. These are choices already
  available from original functorial factorization of the initial arrows, rather than
  a stronger condition on the original category or on any member of `s`. Naturality of
  `ε` makes `Q.map f` the actual replacement of `f`, not an arbitrary map. The theorem
  works for every such replacement, matching the dependency's replacement-independent
  derived-mapping convention.
- `IsLocal Q s Z` is exactly `IsFibrant Z ∧ ∀ i, ...`, where the second conjunct is
  `SSet.Enhanced.IsWeakHomotopyEquivalence
  (eHomWhiskerRight SSet (Q.map (s i)) Z)`. That map has source `sHom (Q.obj (B i)) Z`
  and target `sHom (Q.obj (A i)) Z`. As `Z` is original fibrant, these are precisely
  original derived mapping spaces. No restriction on the original `A i` or `B i`
  is imposed. Replacing the target again is unnecessary for an already fibrant target.
- `(L : ModelCategory M)` gives the assumed existing localized model structure on
  the identical category. `_hL₁` and `_hL₂` supply its two functorial factorization
  axioms under the same convention. Its classes are accessed by explicit projections
  from `L`; it never becomes a competing instance for the original structure.
- `_hC : L.categoryWithCofibrations.cofibrations = cofibrations M` is the equality of
  cofibration classes. `_hW : L.categoryWithWeakEquivalences.weakEquivalences =
  localEquivalences Q s` is the exact equality of weak equivalences with the class
  that, for every `Z` with `IsLocal Q s Z`, makes the actual enriched precomposition
  by `Q.map f` a weak homotopy equivalence. Both directions of “exactly” are retained.
- The endpoint hypotheses are `_hX : IsLocal Q s X` and `_hY : IsLocal Q s Y`.
  They require original fibrancy and locality, not localized fibrancy.
- The conclusion `L.categoryWithFibrations.fibrations p ↔ Fibration p` compares the
  localized class directly with the original instance's class. It includes both
  implications. No properness, accessibility, combinatoriality, cofibrancy of the
  endpoints, or special property of `s` occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization`, its full signature, proof
  docstring and supporting `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7`.
  The theorem's mapping-space clause expressly permits functorial cofibrant/fibrant
  replacements. The consumer uses this exact enrichment and actual precomposition
  interface, rather than defining another localization or another mapping-space model.
- Its public dependency `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, including the enriched representing
  properties of its tensor and cotensor universal elements.
- Its public dependency `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, the realization/homotopy-group definition
  already used by the recorded dependency's mapping formulas and SM7 interface.
- Mathlib `ModelCategory`, `IsCofibrant`, `IsFibrant`, `Fibration`, and the enriched
  `eHomWhiskerRight`, with their original structure instances. No private substitute
  for these notions is introduced.

All stated proof dependencies are also directly imported as ordinary, non-public
imports: `Sheaf.CategoryTheory.HammockComponentsLocalization`,
`Sheaf.CategoryTheory.HammockInfinityLocalization`,
`Sheaf.AlgebraicTopology.KanQuillenRightProper`,
`Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`, and
`Sheaf.CategoryTheory.ModelLocalizationDetectsWeakEquivalences`. The lifting-class
node is a Mathlib leaf with its four exact closure declarations recorded, so it does
not require a `lean` repair. None of these proof interfaces is used as an assumption
of the statement.

Edge cases checked before writing:

- Empty `I`: the universal mapping test is empty and `IsLocal` is just original
  fibrancy; the theorem retains all arrows between fibrant endpoints.
- An identity-only family: `Q.map` preserves identities and enriched precomposition
  is identity. Again all original fibrant objects are admitted.
- Non-cofibrant domains/codomains in the family and in `p`: only `Q.obj` is required
  cofibrant; none of those original objects is excluded.
- The map empty-to-point in simplicial sets: locality genuinely imposes the derived
  test, so the predicate is not universally true; the empty simplicial set is not
  local for that test.
- Terminal/zero examples and identity `p` cause no special branch or nonemptiness
  requirement. The intermediate boundary criterion includes degree zero in the proof
  docstring; no positive-degree-only criterion is substituted.
- Both original and localized factorization conventions are explicit, while the
  localized enrichment and localized fibrancy of the endpoints are absent as required.

Searches made (the remote services were invoked through `msearch.py` with this group
and item, and their log is retained by that wrapper):

- LeanFinder query: “Fibrations between S-local objects in a left Bousfield localization
  coincide with original fibrations”. Eight results, headed by
  `HomotopicalAlgebra.fibration_iff`, `CofibrantObject.factorsThroughLocalization`,
  `FibrantObject.weakEquivalence_homMk_iff`, and `isFibrant_of_fibration`.
  These describe a single model structure or its homotopy category; none compares
  changed model structures or supplies the present locality test.
- LeanSearch query: “Left Bousfield localization preserves fibrations between local
  objects”. Eight results, including `Localization.LeftBousfield.W`,
  `Localization.LeftBousfield.isLocalization` and `ObjectProperty` locality results.
  Read Mathlib `CategoryTheory/Localization/Bousfield.lean`, especially its `isLocal`
  and `isLocal_iff_isIso`: they test ordinary Hom-set bijections, rather than derived
  mapping-space equivalences, and do not compare model fibrations.
- Loogle query `"fibration", "local"`: zero results.
- msearch grep query `Bousfield|local.*fibr|fibr.*local`, subdirectory
  `AlgebraicTopology/ModelCategory`: seventeen incidental results, including the
  cofibrant/fibrant homotopy-category localization comparisons and FundamentalLemma.
  Read `ModelCategory/Basic.lean` and the bifibrant localization signatures; no exact
  declaration or existing derived local-object predicate occurs there.
- `rg` in upstream `WeilConjectures` for `Bousfield|bousfield|local.*fibr|fibr.*local`,
  and separately for the node id: only the ordinary site-localization/Bousfield imports
  and incidental matches, no model-localization fibration theorem. Checked the
  upstream Lean-name index for this node and the proposed theorem name: no match.
- `rg` in the project's `lean/Sheaf` for the same concept and local-object predicate
  names: Bousfield--Kan comparison files concern a different construction; the existing
  model localization modules supply the required foundations but no local-fibrations
  statement. The `IsLocal` helper uses the mathematical definition spelled out in this
  node, and `localEquivalences` is its corresponding class, not an ordinary Hom-set
  version of Mathlib's predicate.

Validation: `scompile.py Q100 lem-coef-bousfield-local-fibrations` compiled the delivered
module cleanly, separately in the sandbox and at its library module path, with the
side-project overlay. All universes and variables are explicit, all lines meet the
100-column bound, and the single postponed theorem has the matching DAG node and
complete proof docstring. The required delivery dry run checks this complete packet;
the second reader supplies the independent reading and performs delivery.

## Second reading by Q100

I independently read the sandbox node, all three declarations in
`BousfieldLocalFibrations.lean`, the recorded statement dependency's node and source,
and the Mathlib predicates they use. The node's source is Hirschhorn rather than
Stacks: I opened the [Rochester PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/pshmain.pdf#page=77)
and read Definition 3.1.4(1), Definition 3.3.1(1), Proposition 3.3.16(1) and its
surrounding proof. The proposition assumes an existing left Bousfield localization
and local endpoints; it does not assume properness or combinatoriality. The node's
restriction to simplicial model categories and its model-category conventions are
explicitly inherited from `lem-coef-simplicial-model-nerve-localization`.

My object/hypothesis/conclusion list, with the Lean rendering and verdict:

1. An original model category on an underlying category: `{M : Type u}`,
   `[Category.{v} M]`, `[ModelCategory M]`. The completeness/cocompleteness and both
   functorial weak factorization requirements of the dependency node are exactly
   `[HasLimits M]`, `[HasColimits M]` and the two original
   `HasFunctorialFactorization` instances. I read Mathlib's `ModelCategory` source:
   its own fields supply finite limits/colimits, lifting, retract closure,
   two-out-of-three and nonfunctorial factorizations, so these additional explicit
   binders supply the inherited convention rather than new mathematical hypotheses.
   Verdict: exact.
2. A simplicial model category, enriched, tensored, cotensored, with SM7:
   `[SimplicialCategory M]`, `_T : SimplicialTensorCotensor M` and
   `_hSM7 : SimplicialModelLocalization.SatisfiesSM7 M`. I opened the tensor/cotensor
   record and its enriched representing maps, and the actual SM7 `cornerMap` and
   `SatisfiesSM7` definitions in the recorded dependency module. SM7 asserts the Kan
   lifting condition and the weak equivalence condition when either input is trivial.
   Verdict: these are the same objects as the dependency, with no localized enrichment
   assumed.
3. A small set S of arbitrary arrows: `{I : Type w}`, `{A B : I → M}` and
   `s : ∀ i : I, A i ⟶ B i`. A family presents its image set, and each set of arrows
   has such a presentation. Duplicate indices repeat an identical universal test.
   Verdict: exact; no finiteness or nonemptiness and no cofibrancy of A or B is added.
4. Original derived mapping spaces and S-local objects: `(Q : M ⥤ M)`,
   `(ε : Q ⟶ 𝟭 M)` and `_hQ` specify a functorial original cofibrant replacement with
   trivial-fibration augmentation. Such a choice is available from the original
   functorial factorization of initial maps. The theorem works for every such choice.
   `IsLocal Q s Z` is original `IsFibrant Z` together with weak homotopy equivalence of
   `eHomWhiskerRight SSet (Q.map (s i)) Z`, from `sHom (Q.obj (B i)) Z` to
   `sHom (Q.obj (A i)) Z`. I read `MappingPresentation`, `MappingFormulas` and the
   theorem `simplicial_model_nerve_localization`: its natural enriched comparison and
   replacement spans justify precisely this actual precomposition model into fibrant
   Z. Naturality of ε pins `Q.map s` to s; it is not an unrelated chosen map.
   Verdict: exact, computed entirely in the original model structure.
5. An existing model structure on the same category: `(L : ModelCategory M)`, with
   `_hL₁` and `_hL₂` giving the inherited functorial factorizations for its explicit
   classes. Limits and colimits concern the same underlying category, so the existing
   hypotheses serve both structures. L is an ordinary explicit parameter, never a
   second instance that could silently replace original fibrancy or weak equivalence.
   Verdict: exact.
6. Unchanged cofibrations: `_hC` equates
   `L.categoryWithCofibrations.cofibrations` with `cofibrations M`. Verdict: equality
   retains both directions of the stated requirement.
7. Exactly the arrows inducing original derived equivalences into every local object:
   `_hW` equates L's weak-equivalence class with `localEquivalences Q s`. That helper
   quantifies `∀ Z : M, IsLocal Q s Z → ...` and tests the actual precomposition by
   `Q.map f`, using the same enrichment and realization weak equivalence as in item 4.
   I opened `SSet.Enhanced.IsWeakHomotopyEquivalence`: it requires a bijection on
   realized path components and every positive based homotopy group, not merely
   equivalence on components. Verdict: exact.
8. Local endpoints and an arbitrary arrow: `{X Y : M}`, `(p : X ⟶ Y)`,
   `_hX : IsLocal Q s X`, `_hY : IsLocal Q s Y`. Verdict: the required original
   fibrancy and locality are present; localized fibrancy and endpoint cofibrancy are
   not substituted.
9. Both implications of the conclusion:
   `L.categoryWithFibrations.fibrations p ↔ Fibration p`. The left side uses L's class
   and the right side the original instance. Verdict: exact. No properness,
   combinatoriality, accessibility, existence of another localization, or special
   assumption on S occurs anywhere in the signature.

Edge cases: empty I reduces `IsLocal` to original fibrancy; an identity-only family
adds no mapping constraint; zero/terminal objects and identity arrows are allowed
whenever they satisfy the stated locality. Arbitrary noncofibrant A, B, X and Y are
allowed because replacement is applied before mapping. There is no positivity
restriction or natural-number binder in the theorem; the proof's boundary test
explicitly retains n = 0. The empty underlying category cannot satisfy the source's
complete model-category hypotheses, consistently with Lean. Empty schemes and
characteristic conditions do not occur in this categorical statement. The object,
hom and arrow-index universes u, v, w are independent; the mapping spaces use the
hom universe v through the dependency's `SimplicialCategory` convention. No site
universe, smallness equality or index bound has been imposed.

Independent searches, through the prescribed wrapper and direct source reads:

- LeanFinder: "A morphism between homotopy local fibrant objects is a fibration in
  the localized model structure exactly when it is an original fibration". Eight
  hits, including `isFibrant_of_fibration`, `fibration_iff` and fibrant/bifibrant
  subcategory facts. Their returned signatures concern one supplied model structure;
  none gives the present two-structure equivalence.
- LeanSearch: "Weak equivalences detected by derived mapping spaces into homotopy
  local objects and fibrations in a second model structure". Eight hits, headed by
  `weakEquivalences`, `weakEquivalence_iff` and
  `CofibrantObject.weakEquivalence_toHoCat_map_iff`; no localization comparison.
- Loogle: `"localEquivalence"`, zero hits. Wrapper grep for
  `Bousfield|localEquivalence|local.*fibration` in `AlgebraicTopology/ModelCategory`
  also returned zero hits.
- Direct `rg` searches in Mathlib's model-category and Bousfield files, upstream
  `WeilConjectures`, and the project's `lean/Sheaf` used Bousfield, local objects,
  local-equivalence names and local/fibration combinations. I opened
  `Mathlib/CategoryTheory/Localization/Bousfield.lean`: `ObjectProperty.isLocal`
  tests ordinary Hom-set bijections, so cannot replace either derived helper here.
  I also opened upstream `WeilConjectures/Mathlib/CategoryTheory/Localization/Bousfield.lean`:
  `adjunctionOfIsLocal` constructs an ordinary reflective-subcategory adjunction from
  that Hom-set predicate, not this notion or theorem. The project's Bousfield--Kan
  and generic model-localization statements have different conclusions. There is no
  exact existing declaration or duplicate helper. The upstream-name index has no
  item/name match. Both helper definitions are real predicates of this node's own
  local-object/local-equivalence terminology, listed in `lean.declarations`.

No new definition node, dependency module, repair handoff or statement correction
is present. I checked the sandbox node against the shared node: only `lean` differs.
I additionally read the saturation theorem's arbitrary-endpoint signature and
Mathlib's lifting-class declarations, and verified the stated proof imports.

Mismatches found and changes: no mathematical mismatch in the signature or helper
bodies. The theorem proof docstring called the intermediate arrows "i trivial
cofibrant and q fibrant"; I corrected this to "i a trivial cofibration and q a
fibration". Its compressed steps omitted the explicit initial-tensor identification
and the wide-subcategory/universe/formal-inversion bridge that the DAG proof spells
out. I added those explanations to steps 3 and 7. All eight proof steps and their
cited dependencies are now present. The statement, node fields, definitions and
imports were retained. Every declaration has the source and blueprint marker;
there are no hollow definitions, file-local interfaces or newly proved facts, and
the one theorem proof is entirely `sorry`.

Second-reader validation: the exact delivered module compiled cleanly through
`scompile.py Q100 lem-coef-bousfield-local-fibrations lean/Sheaf/CategoryTheory/BousfieldLocalFibrations.lean`
in both sandbox (1.6 s) and library-path (1.8 s) modes, with no diagnostics. I checked
that every universe/variable is bound, all Lean lines are at most 100 columns,
`lean.statement` is verbatim the file's theorem signature, and all three declared
names are listed in the record. The required `deliver2.py --no-push` preflight is
run on this reviewed packet before delivery.

Dry run completed successfully: `deliver2.py Q100 lem-coef-bousfield-local-fibrations
--no-push` reported `OK (dry run)` at commit `223f2e5928`; preflight and compiles
passed, with nothing pushed. The final delivery includes this validation record.

## Maintainer review fix (2026-10-17)

The delivered signature bound `(L : ModelCategory M)` after the original
`[ModelCategory M]`. A binder of class type is a local instance, and Lean prefers the most
recent one. Every later instance-resolved term therefore used `L`: `cofibrations M` in
`_hC`, `IsLocal`/`localEquivalences` (original fibrancy) in `_hW`, `_hX` and `_hY`, and
`Fibration p` in the conclusion. The `pp.explicit` signature showed all of these
elaborated with `L`. `_hC` was `rfl`, and the conclusion was proved by
`Iff.intro (fun h => ⟨h⟩) (fun h => h.mem)`. The claims above that `L` "never becomes a
competing instance" were therefore wrong. The fix binds `L` immediately after
`[Category.{v} M]` and before the original `[ModelCategory M]`. With `pp.explicit`, all
instance-resolved classes are now the original instance and `L` occurs only through its
projections. The trivial proof fails, and `_hC` is no longer `rfl`. Nothing else in the
statement changed, and the record's `lean.statement` is re-read from the fixed file.
