## Worker report

Stage 2, Q71, lem-sfb-space-four-property-fppf-descent, 2026-10-23.
The inherited BLOCKED ending concerned a stage-1 unchanged split. The current node is
split, reviewed PASS by Q26, has no lean record, is queued for stage 2, and has no
repair note. The current brief §0 explicitly authorizes this stage handoff. The
accepted statement, proof, and proof dependencies remain unchanged.

AlgebraicSpaceFourPropertyFppfDescent.lean states four_property_fppf_descent, with
one postponed proof, `by sorry`. AlgebraicSpaceAffineQuasiFinite.lean supplies two
real Prop definitions owned by the new definition node. Nothing is proved here.

Clause-by-clause correspondence:

- A scheme S in the size convention is `{S : Scheme.{u}}` with explicit universe u.
  X,Y and all base changes are `AlgebraicSpace S`, the recorded full subcategory of
  big-fppf sheaves; their morphisms retain their natural transformations.
- Each property separately is `P : MorphismProperty (AlgebraicSpace S)` with hP the
  disjunction of equality to MapIsAffine, MapIsFiniteType, MapIsQuasiFinite and
  MapIsSeparated. This neither combines their hypotheses nor assumes all four.
- Affine: MapIsAffine quantifies over every `T : Over S`, proof `IsAffine T.left`,
  and natural transformation `a : yoneda.obj T ⟶ Y.obj.obj`. It requires an affine
  U and actual maps p,q whose square is `IsPullback q (yoneda.map p) f.hom.hom a`.
  This says that the test fibre product is represented by an affine scheme. It
  does not merely require an arbitrary map or assume representability of f.
- Finite type: the existing MapIsFiniteType is MapIsQuasiCompact f.hom.hom AND
  MapIsLocally (@LocallyOfFiniteType) f. The latter quantifies over every compatible
  pair of representable etale scheme charts. MapIsQuasiCompact uses affine tests
  and CompactSpace of the existing Point topology. This is equivalent to the
  node's quasi-compact scheme tests and quasi-compact atlas convention: cover a
  quasi-compact scheme test by finitely many affine opens, compose the resulting
  quasi-compact etale atlases, and use the atlas topology. Conversely a
  quasi-compact space has a finite collection of affine etale chart images
  covering its compact point space; their finite disjoint union is the required
  quasi-compact atlas. No compact-Hausdorff convention is imposed.
- Quasi-finite: MapIsQuasiFinite is the existing MapIsFiniteType plus, for every
  Ω : Type u with Field and IsAlgClosed, every s : Spec Ω ⟶ S, and every map
  a : h_(Spec Ω,s) ⟶ Y, `Finite (Point (Limits.pullback f.hom.hom a))`.
  These are point CLASSES of the entire geometric fibre, not its set of Ω-valued
  sections. The definition follows the item's literal finite-geometric-fibre
  convention; it does not substitute Mathlib's scheme locally-quasi-finite class.
- Separated: the existing MapIsSeparated is IsRepresentableWith closed immersion
  of `pullback.diagonal f.hom.hom`. Every scheme base change of the diagonal is
  required to be a scheme closed immersion, exactly the statement's convention.
- Isomorphism invariance: first conjunct quantifies over eX : X ≅ X', eY : Y ≅ Y',
  arrows f,f', and the commuting-square equality. Its conclusion is `P f ↔ P f'`.
  Both the source and the target may vary.
- Arbitrary algebraic-space base change: second conjunct quantifies over every
  g : Y' ⟶ Y, with no flatness or finite-presentation restriction, and states
  `P f → P (enlargedFibreProductFst g f)`.
- Cover index: `I : Type w`, with universe w independent of u, is any set index.
  The Yᵢ are algebraic spaces and g i : Yᵢ i ⟶ Y are the covering maps.
- Fppf: the third conjunct assumes separately ∀i MapIsFlat (g i), ∀i
  MapIsLocallyOfFinitePresentation (g i), and the recorded IsJointlySurjective
  on their underlying presheaf maps. Flatness/lfp use precisely the existing
  all-compatible-etale-chart tests, with scheme Flat/LocallyOfFinitePresentation.
  Joint surjectivity uses field-extension lifts, not sectionwise surjectivity.
- Cover equivalence: `P f ↔ ∀ i, P (enlargedFibreProductFst (g i) f)` is the full
  iff, retaining both directions and each member of the original covering.
  The chosen fibre product has order Yᵢ ×_Y X, and fst projects to Yᵢ. This is
  canonically X ×_Y Yᵢ by exchanging matching pairs, so no projection is reversed.
  enlargedFibreProduct is the actual sheaf pullback with the algebraic-space
  property supplied by fibreProduct_isAlgebraicSpace; no arbitrary pullback chosen.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsRepresentableWith,
  IsEtale and IsAlgebraicSpace, with their full signatures and source docstrings.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback and etale_fibreProduct_isScheme.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat; its affine definition is
  equivalent to stalkwise flatness by Flat.iff_flat_stalkMap.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  LocallyOfFinitePresentation, the affine-local presentation property.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: IsAffineHom; scheme tests use
  IsAffine, imported from the same scheme affine infrastructure.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType and
  QuasiCompact via the existing space finite-type predicate.
- Mathlib.Topology.Defs.Filter: CompactSpace, without a separation axiom.
- Mathlib.FieldTheory.IsAlgClosed.Basic and AlgebraicClosure: IsAlgClosed and
  AlgebraicClosure. The dependency's mathlib_match is its usable record.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- def-weil-size-convention is a metatheoretic convention, not an importable object.
- Added landed definition dependency def-sfb-space-morphism-properties:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties, MapIsFlat,
  MapIsLocallyOfFinitePresentation, MapIsFiniteType, MapIsSeparated, MapIsLocally.
- Added landed definition dependency def-sfb-space-sheaf-fibre-product:
  Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite, enlargedFibreProduct and
  enlargedFibreProductFst. The declaration body and source docstrings were read.
- Added landed definition dependency def-trf-algebraic-space-jointly-surjective-family:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity, IsJointlySurjective.
- New definition dependency def-sfb-space-affine-quasifinite-properties reuses
  MapIsFiniteType and Point (AlgebraicSpacePointClasses). It has no sorry.

The module imports the already stated proof dependencies: FpqcClosedImmersionDescent,
FamilyCommonExtensionFields, FppfSheafCoproductPartition,
AlgebraicSpaceRepresentableEtaleSchemeTests, FpqcAffineDescent, and the relevant
Mathlib affine, quasi-separated, algebraic-closure and scheme-coproduct modules.
The sfb finite-refinement, lft-locality, chart-test, quasi-affine descent,
quasi-compact tests/locality, separated-fp composition and stack finite-type
calculus nodes currently have no Lean declarations; no imports for them exist.
They are proof prerequisites, not missing objects required to state this theorem.

Edge cases read before drafting: empty X, empty Y, empty covering index (possible
only over empty Y), empty geometric fibres, identity isomorphisms/base changes,
non-affine test targets, arbitrary nonrepresentable covering maps, and arbitrarily
large set indices. Empty affine schemes and finite empty point sets are allowed.
No Nonempty, separation, quasi-compactness or flatness hypothesis is placed on f.
Test fields live in Type u, matching the big site's test schemes, so no too-small
independent field universe vacates the geometric tests. Source/target schemes
have no Noetherian or base-field restrictions.

Searches (actual msearch logs are retained in searches.jsonl):

- leanfinder: "Affine finite type quasi finite and separated morphisms of algebraic
  spaces are stable under base change and local for fppf coverings" returned 8
  scheme-only stability/multiplicativity facts, including
  instIsStableUnderBaseChangeSchemeLocallyQuasiFinite and
  locallyOfFiniteType_isStableUnderBaseChange; no exact space theorem.
- loogle: "AlgebraicGeometry.AlgebraicSpace,
  MorphismProperty.IsStableUnderBaseChange" returned zero hits, unknown
  AlgebraicGeometry.AlgebraicSpace in Mathlib.
- msearch grep: "AlgebraicSpace|algebraic.space" in AlgebraicGeometry returned 0.
- leansearch: "Affine morphisms and finite type morphisms with finite geometric
  fibres of algebraic spaces" returned 8 scheme facts: IsAffineHom, IsFinite,
  isAffineHom_iff and constructors/instances; no algebraic-space definitions.
- rg over lean/Sheaf, lean/WeilConjectures and dag/lean_names_upstream.json for
  MapIsAffine|MapIsQuasiFinite|four_property_fppf_descent returned no existing
  declarations. rg for the blueprint id in upstream and Sheaf returned none.
- DAG rg for MapIsAffine|MapIsQuasiFinite|affine.*finite.geometric.fib found theorem
  consumers, no definition owner. blueprint_refs.py search "four-property" and
  "affine quasi-finite" each returned 0; ancestor reports blueprint.from.node None.
- Broader project scans found AlgebraicSpaceMorphismProperties and
  ProperCurveModuli. Their existing predicates are reused, not copied.

Source: read spaces-descent.tex definition-property-morphisms-local and Tags
041Z, 041U, 0421, 0427, plus spaces-morphisms.tex definition-affine (03WF),
definition-locally-quasi-finite (03XJ) and the cited base-change lemmas. No statement
correction is needed; the node explicitly fixes the finite-geometric-fibre convention.
The only item changes are lean and added definition statement dependencies.

## New nodes

`def-sfb-space-affine-quasifinite-properties` introduces MapIsAffine and
MapIsQuasiFinite in AlgebraicSpaceAffineQuasiFinite.lean. Its first predicate is
exactly Stacks spaces-morphisms definition-affine, Tag 03WF. Its second is finite
type with finite geometric-fibre point classes, exactly the consumer's explicit
convention; Stacks 03XJ/03XL/0427 supply its context. All data are genuine formulas:
cartesian test squares and the existing Point of the presheaf pullback. It reuses
MapIsFiniteType and all underlying notions. The searches above found no existing
space affine or finite-geometric-fibre predicate or definition owner; the node
records the actual search results, the inherited null ancestor, and the item via.
No dependency interface repair or source-based statement change is made.

## Second reading by Q71

Self-check, with the node and both modules reopened; no other agent was started.
I compared each clause above, checked the existing definitions' bodies rather than
their names, and checked pullback projection orientation. The initial source tag
03WG named affine-locality rather than definition-affine; corrected it to 03WF
in the new node. Added the existing definition owner for enlargedFibreProductFst,
and the landed chart-property and joint-surjectivity definition owners. The
conclusions have no extra clause and neither require all four properties together
nor restrict base change to covering maps. The algebraically closed field test
uses finite Point classes, including extension-valued points, and has no
unjustified Ω-section identification. The quasi-compactness predicate's affine
point-compactness formulation agrees with the statement's scheme-test/atlas form
by the finite affine covering and final-atlas topology arguments above. Both new
definitions are real; the sole theorem has sorry and a nine-step proof docstring.
All variables/universes are explicit, autoImplicit is false, all source lines
have at most 100 characters, and module/public-import visibility is used.

Validation: scompile.py compiled both modules separately in dependency order,
including their library paths, cleanly. The final import-complete version and the
required server preflight are checked by the delivery wrapper below.

Dry-run repair: the server schema requires `import_flags` on every new definition
node (tools/stage2_delivery.py), though the brief field list omits it. Added the
empty list, matching the existing fibre-product definition node. First dry run
compiled the final import-complete files and found only this schema omission.
