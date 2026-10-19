## Worker report

This repairs the delivery returned at immutable head `a79979fe23e2`, without changing
its mathematical node statement or proof plan. The saved packet was inspected first;
the prescribed initial `deliver2.py --no-push` passed at `6f548b2514`. The subsequent
semantic self-check confirmed the issues in the return, so the packet was repaired
before delivery. Comparison with the current shared node found only the previous
`lean` delta. This packet additionally cites the now-published owning nodes for frames and general
Bousfield localization in `stmt_deps`. A later refreshed-import failure also required
a one-annotation dependency repair for the already published straightening module
(see Dependency modules below). All other non-`lean` fields are preserved.

The module is `Sheaf.CategoryTheory.DgPresheafModelLocalizations`, with one postponed
theorem `HomotopicalAlgebra.dgPresheafModelLocalizations`. Definitions have full data;
no proof is supplied. The theorem's docstring now contains the complete text of all
eleven DAG proof steps, including their dependency ids. Each helper has its own
source and blueprint docstring. The node's declaration list enumerates all eighteen
module declarations.

For the following clause mapping, write U = max u v w. This is explanatory notation
in this report; the Lean signature spells out every universe expression.

| Node hypothesis or clause | Lean rendering and check |
| --- | --- |
| Small category and arbitrary topology by covering sieves | `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`. `GrothendieckTopology` is Mathlib's sieve topology, with maximal-cover, pullback-sieve and transitivity axioms. There is no fibre-product or subcanonical hypothesis. |
| Chosen universe bound containing site and coefficient ring | The module objects are in `Type U`, presheaf complexes in `Type (U + 1)`, and complex morphisms in `Type U`. All three `combinatorial` fields are `CombinatorialModelCategory.{U+1,U,U}`. Thus the site objects, site arrows, coefficients, representable generators and their small coproducts fit the same small bound. The coherent localization has the explicitly declared larger universe `max (U+1) t`. There is no equality imposed on u, v or w. |
| Arbitrary commutative coefficient ring | `{Λ : Type w} [CommRing Λ]`, including the zero ring. `ModuleCat.{U,w} Λ` retains this very ring. |
| Associated module sheaves | The first existential is `HasWeakSheafify J (ModuleCat.{U,w} Λ)`. It supplies the sheafification interface in the conclusion, rather than adding an extra hypothesis to the site or ring. The resulting `presheafToSheaf` is used in both later sheaf clauses. |
| P = module presheaves; M = unbounded cochain complexes | `DgPresheaf C Λ` is exactly `CochainComplex (Cᵒᵖ ⥤ ModuleCat.{U,w} Λ) ℤ`. No boundedness assumption occurs. |
| Objectwise quasi-isomorphisms | `DgObjectwiseQuasiIso` is `HomologicalComplex.quasiIso` for this presheaf category and `ComplexShape.up ℤ`. Homology and isomorphisms in the functor category are objectwise. |
| W_J = isomorphisms of all sheafified cohomology presheaves | `DgSheafifiedCohomologyMap` is literally `presheafToSheaf.map (homologyFunctor.map f)`. `DgSheafCohomologyEquivalence` requires `IsIso` for every integer n. |
| Complete and cocomplete model category, retracts, two-out-of-three, both weak factorization systems | Each model data structure supplies `hasLimits`, `hasColimits`, and a Mathlib `ModelCategory`. Its CM axioms give retract closure, two-out-of-three and the two lifting/factorization systems; the imported combinatorial interface supplies both functorial factorizations. Trivial classes are intersections with its weak equivalences. |
| Combinatorial and left proper projective structure | `DgProjectiveModelData.combinatorial` uses the recorded `CombinatorialModelCategory`. `leftProper` is `DgLeftProper`, testing the actual pushout of a weak equivalence along a cofibration. |
| Projective weak equivalences and fibrations | `weakEquivalences` equals `DgObjectwiseQuasiIso`; `fibrations` equals `DgObjectwiseDegreewiseSurjective`, which quantifies every degree and site object. |
| Projective cofibrations | `DgProjectiveCofibration` is the left lifting class against maps satisfying both objectwise surjectivity and quasi-isomorphism; the `cofibrations` field is equality with this class. |
| Projective homotopy function complexes are coherent mapping spaces in D(P) | `S : DgCoherentLocalization` provides the actual map from the large nerve and `FiniteReedy.IsLocalization` at W_obj, including the quasicategory and full coherent-functor universal property. `DgHomotopyFunctionComplex` is the dependency's right-pinched mapping space. The theorem also supplies `CosimplicialFrameMappingData` for P and this same q, including actual-map normalization and both naturality comparisons. |
| All projective objects fibrant | `P.everyObjectFibrant` tests the terminal map of every complex against the projective fibration class. |
| Projective integer-shift Quillen autoequivalences | `P.shifts : DgShiftQuillenAutoequivalences P.model` quantifies every r in ℤ and preservation of cofibrations and weak equivalences. The same quantifier includes -r; the canonical complex shifts are inverse autoequivalences. |
| M_J, same category, same cofibrations, exactly W_J | `DgSheafModelData.model`, `.cofibrations`, `.weakEquivalences` and `.combinatorial`. `.objectwiseIncluded` records W_obj ⊆ W_J, used by the specified comparison. No hypercover test, hypercover generation or local fibrant-object identification is asserted. |
| Identity M → M_J left Quillen | `DgSheafModelData.identityLeftQuillen` records the nonautomatic part, preservation of projective trivial cofibrations; its cofibration equality records preservation of cofibrations. |
| Every small set B of complex maps | `∀ (I : Type U) (B : I → Arrow (DgPresheaf C Λ))`. An indexed family represents a small set by its image, and repetition changes no locality test. This includes the empty family and excludes a family as large as the entire U+1-sized arrow category. |
| Existence of M_B with unchanged cofibrations | `∃ L : DgBousfieldModelData (P := P) B`, whose `.cofibrations` is the same projective class. |
| Fibrant objects precisely the old fibrant B-local objects | `L.fibrant` is a biconditional with `GeneralBousfield.IsLocal P.model B Z`. This exact published definition is old fibrancy plus `IsFrameOrthogonal P.model (B i).hom Z` for every i. |
| W_B precisely maps testing as equivalences into every such Z | `L.weakEquivalences = GeneralBousfield.localEquivalences P.model B`. This quantifies all old fibrant B-local Z and uses the same framed precomposition test on f. Both predicates refer explicitly to P.model. |
| Mapping-space tests computed in the original projective model | `GeneralBousfield.IsFrameOrthogonal` uses actual `frameHomPre` maps of old cofibrant replacements and old cosimplicial frames, normalized by the degree-zero augmentation square representing the specified arrow. The comparison datum above identifies these with the action of q(f) on coherent mapping spaces. There is no independently chosen precomposition map in the packet. |
| Identity M → M_B left Quillen | `L.identityLeftQuillen` and the unchanged cofibration class. |
| Functorial fibrant replacement and both factorizations | `L.fibrantReplacement` supplies a functor R, natural unit η and its trivial-cofibration/fibrant-value properties. `L.functorialFactorizations` explicitly records both factorization systems; they are also part of combinatoriality. |
| Shift-invariance hypothesis up to objectwise quasi-isomorphism of arrows | `DgShiftInvariant B`: for every r and i, some B j is related to `(B i)[r]` by `Relation.EqvGen DgArrowQuasiIsoSquare`. Each generating relation is a commuting square with both endpoint maps objectwise quasi-isomorphisms. The equivalence closure includes identities, reverse squares and arbitrary finite zigzags. |
| Localized shifts Quillen autoequivalences | `DgShiftInvariant B → DgShiftQuillenAutoequivalences L.model`, for both shifts and their inverses. |
| If B ⊆ W_J, identity M_B → M_J left Quillen and W_B ⊆ W_J | The final implication assumes `∀ i, DgSheafCohomologyEquivalence J (B i).hom`, and concludes `DgLeftQuillen L.model M.model (𝟭 _)` together with inclusion for every map f. `DgLeftQuillen` means preservation of cofibrations and trivial cofibrations; the identity has its canonical identity adjunction. |

The previous packet also appended a separately quantified Quillen universal-property
clause. It is removed from the conclusion, since the node states the three model
structures and their specified comparisons; general localization's universal property
is an imported proof input for the final comparison, as in proof step 11. No clause
of the natural node statement is removed.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, no Lean object. Its explicit
  universe requirements are implemented above.
- `def-weil-pbc-sheafification`: `CategoryTheory.presheafToSheaf`,
  `toSheafify` and `sheafificationAdjunction`, module
  `Mathlib.CategoryTheory.Sites.Sheafification`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory` and
  `DerivedCategory.Q`, module `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  the source category and homology maps use its cochain-complex API.
- `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap` and `IsWeakHomotopyEquivalence`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- `lem-coef-combinatorial-localization-presentability`:
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`,
  module `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`; its
  imported `CombinatorialModelCategory` is the common model interface.
- Newly cited, already published `lem-coef-cosimplicial-frame-mapping`:
  `CategoryTheory.CosimplicialFrameMappingData`, `frameHomPre`,
  `CosimplicialFrame`, and `cosimplicial_frame_mapping`, module
  `Sheaf.CategoryTheory.CosimplicialFrameMapping`.
- Newly cited, already published `lem-cbc-general-bousfield-localization`:
  `HomotopicalAlgebra.GeneralBousfield.IsFrameOrthogonal`, `IsLocal`,
  `localEquivalences` and `general_bousfield_localization`, module
  `Sheaf.CategoryTheory.GeneralBousfieldLocalization`.

The proof imports include the published presentable-cellular-factorization,
accessible-monad-presentability, accessible-arrow-inverse-image and Smith-recognition
modules. The Mathlib proof leaves are imported from HomologySequenceLemmas,
Abelian.DiagramLemmas.Four, ModuleCat.Presheaf.Sheafification,
Abelian.GrothendieckAxioms.Sheaf, ModuleCat.AB and Presentable.Presheaf; the recorded
Grothendieck-locally-presentable declaration is imported from the upstream
GabrielPopescu module. The genuine enriched-projective-diagram-model proof node
has no published declaration; it is not used to manufacture a definition or a
new untracked postponed theorem. It remains the first dependency of the single
postponed theorem's proof plan.

Source checked: [Choudhury--Gallauer](https://arxiv.org/pdf/1511.02828),
Corollary 3.1, Definition 5.6, Theorem 5.7(1)-(2), Remark 5.8, Definition 5.9,
and the first paragraph before Lemma 5.12. The current DAG's sieve-based,
no-hypercover-generation proof route is preserved.

Searches retained and repeated during repair:

- `msearch.py ... leanfinder 'unbounded complexes of module presheaves projective model structure set Bousfield localization'`: eight hits, including `CochainComplex.IsKProjective` and its bounded/projective sufficient conditions; no theorem giving this model-structure statement.
- `msearch.py ... loogle 'ModelCategory, CochainComplex'`: zero hits, unknown identifier `ModelCategory` in the remote search service.
- `msearch.py ... leansearch 'model category of unbounded complexes of module presheaves Bousfield localization'`: eight hits; ordinary Bousfield orthogonality and derived-category localizations, no model structure with this statement.
- `msearch.py ... grep 'Bousfield|[Pp]rojective.*[Mm]odel' AlgebraicTopology/ModelCategory`: zero hits.
- `rg` in the named upstream `WeilConjectures` tree and shared `lean/Sheaf` for `DgPresheaf|dgPresheafModel|IsFrameOrthogonal|lem-cbc-dg-presheaf-model-localizations`: no upstream declaration for this node; the published general-localization framed predicates were found and reused. Existing consumers mention this node as proof input.
- `rg` of the upstream Mathlib ModelCategory directory for Bousfield: no matching model-localization declaration. The saved searches additionally covered unbounded dg presheaves, local models and shift Quillen equivalences; none gave an exact existing main declaration.

Edge cases checked mathematically against the definitions: the empty site, the
terminal site with an arbitrary sieve topology, the zero ring, the zero complex,
all integer cochain degrees, r = 0 and both signs of r, the empty small family,
repeated members, maps with noncofibrant endpoints, and a shift comparison that
exists only by a reverse or multi-step zigzag. The empty family makes the local
condition precisely old fibrancy. The full mapping-space tests retain higher
homotopy groups; no test is replaced by ordinary Hom-set orthogonality. In
particular, the case w > v no longer restricts coefficients to v-sized modules,
and the case u > v no longer asks a v-small generating family to cover a larger
site-object set.

No STATEMENT-DISPUTED flag, natural-statement correction or new definition node is
needed. The main theorem uses `sorry`; the dependency module retains its existing
single postponed straightening theorem unchanged.

## Second reading by Q04

A final separate reading of the current node and the final source was performed
in this single-worker repair, following the dispatcher instruction not to start
other agents. This is a recorded self-check; the maintainer's independent review
is the independent reading of the delivered immutable head.

H3, arbitrary action: the saved `DgCoherentLocalization.precomposition`, identity
and composition fields were independent of q. They were removed entirely. The
final locality and weak-equivalence fields use the published framed predicates
on P.model. In their definition, the augmentation square fixes the represented
map in degree zero; the supplied normalized frame/coherent comparison retains
both naturality squares. Thus even the action, and not merely the objects of the
mapping spaces, is now fixed by the localization. This reading also checked that
P.model is used in both locality tests, rather than L.model.

H3, universes: the saved `ModuleCat.{v,w}` could be too small for its ring or site,
and its combinatorial universe w could be too small for its morphisms and site
index. All coefficient modules now have universe U, complex homs have universe U,
complex objects have universe U+1, and every combinatorial field uses U. The
coherent localization is explicitly lifted above U+1. Sheafification is supplied
existentially, so there is no residual added sheaf-existence assumption or an
equality of site object and morphism universes.

H3, smallness: the saved `Set (Arrow ...)` included the full large class of maps.
Every B-related binder now uses a family `I : Type U`, matching the U-small
colimits and generating sets. No B-membership binder on a U+1-sized set remains.
The quantifiers include the empty family; no nonemptiness was introduced.

H3, shifts: the saved hypothesis required a single directed square from each
shift into a member of B. The final predicate takes the equivalence closure of
the commuting quasi-isomorphism-square relation. Reversing a square and joining
two squares are therefore accepted without any additional assumptions. Every r
and -r occur in the preservation conclusion, matching the node's definition of
Quillen autoequivalence.

H8: checked each of the eighteen declarations for a source/blueprint docstring.
The main docstring now reproduces every proof step, not just the old one-sentence
summary: free linear dg category and transfer; split cellular cofibrations;
left properness, fibrancy and shifts; frame comparison; exact sheafification and
filtered cohomology; accessible arrow inverse image; weak saturation; Smith
recognition; general set localization; zigzag shift calculation; and the final
comparison including all weak equivalences, using equal trivial-fibration classes.
The listed dependency ids agree with each proof step.

H11: the table in the Worker report was read back against every paragraph of the
node. Its first rows cover every binder and the site/universe/coefficient
conventions. The remaining rows cover every projective, sheaf-local and small-set
localization clause. This reading found the earlier merely implicit functorial
fibrant-replacement clause and made it an explicit field. It also removed the
unrequested separately quantified universal-property conclusion. No hypercover
fibrancy or generation clause was introduced, no finite-limit site hypothesis
appeared, and no definition was replaced by an arbitrary chosen map.

Validation uses only the authorized `scompile.py` and `deliver2.py` wrappers.
The final file is compiled separately as both sandbox and module path, with no
errors or warnings. The final dry run is required to pass before the push.


## Dependency modules

`lem-coef-space-valued-straightening`, module
`Sheaf.CategoryTheory.SpaceValuedStraightening`, is a required indirect dependency:
`GeneralBousfieldLocalization → CombinatorialLocalizationPresentability →
CompleteAlgebroid → KanRelativeNerveLeftFibration → SpaceValuedStraightening`.
After the successful dry run at `82e1712a23`, both push attempts were refused while
compiling the newly refreshed published overlay: `SpaceValuedStraightening.lean:64:7`,
`lean.dependsOnNoncomputable`, because `Diagrams` depends on the now-noncomputable
`smallSpaces`. The second attempt used a new overlay snapshot and reproduced the
same diagnostic. Removing this import would discard a required recorded interface.

Under the authorized unusable-dependency repair, the packet includes that node and
the exact current source obtained with `scompile.py --source`, adding only
`noncomputable` to `abbrev Diagrams`. Its data remains the actual internal functor
simplicial set `(ihom (ulift B)).obj smallSpaces`. The mathematical content and all
other declarations are unchanged; the dependency node changes only in `lean`, with
the compiler diagnostic and repair recorded in `lean.note`. Its published source is
not edited on this machine. The item adds this already published owning node to
`stmt_deps`. Both sibling files are compiled separately in dependency order.

The dependency's statement was read against its source declarations as follows:
`LeftFibrations` is the coherent nerve of genuinely small left fibrations with the
specified enriched mapping objects, and `Diagrams` is the coherent internal functor
object into `smallSpaces`. `Straightening.map` and `.equivalence` give the claimed
equivalence for each small quasicategory; `.mapping_kan` states the mapping-space
Kan property. Its `.naturality`, together with `BaseNaturality`, records pullback
and precomposition naturality and the coherent equivalence for all base changes.
For the ordinary-base comparison, `CommaPresentation.fst`, `.snd`, `.square` and
both variable actions characterize the displayed subset-quotient/simplex-colimit
left adjoint as the canonical comma pullback. `IsOrdinaryComparison` quantifies L,
R and the adjunction on all strict diagrams. Its counit clause imposes Kan values
only on G. Its replacement-comparison clause quantifies every weak equivalence
L(X) → D with D strict Kan-valued and X a left fibration; `IsStrictCoherentNerve`
fixes D on every simplex and enriched mapping simplex. `IsComparisonNatural`,
`IsFibrationDiagram` and `IsCoherentFamily` retain naturality in X and G as a full
coherent transformation. No projective cofibrancy assumption is present. The
single postponed theorem supplies exactly these clauses for the same global S.

The final second reading by Q04 also compared this dependency's delivered text to
the current server source: the sole code change is the computability annotation;
all object constructions, signatures and ten proof steps are retained. Its empty
base, empty fibers and noncofibrant diagram cases are unchanged. This additional
repair changes no mathematical interface and resolves the concrete compiler
failure instead of bypassing its published dependency.
