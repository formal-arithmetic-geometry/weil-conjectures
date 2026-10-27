## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantOpenAffinizationEquivariance` states the
node in two theorems, each with `sorry` as its entire proof:
`AlgebraicGeometry.invariant_open_affinization_flat_comparison` is its general flat
comparison and chart assertion;
`AlgebraicGeometry.invariant_open_affinization_equivariance` is its descent specialization.
Source read: `literature/stacks-project/more-groupoids.tex`, Tag 0APK,
`lemma-ind-quasi-affine`, from the invariant W and E through the final diagram and
its two open inverse images (lines 3092 onwards). Tags 0API and 0APJ supply the
canonical embedding and flat comparison used in that argument. Both theorem docstrings
carry the corresponding steps of the node's proof. No theorem is proved.

Hypotheses and objects, clause by clause:

- R to T: `R T : CommRingCat.{u}`, `r : R ⟶ T`; flat spectrum map:
  `[Flat (Spec.map r)]`. No injectivity, nonzero-ring, or surjectivity is assumed here.
- V over Spec R: `f : V ⟶ Spec R`. Quasi-separated V is
  `[QuasiSeparatedSpace V]`, the absolute scheme property in the node and source.
- Every quasi-compact open is a quasi-compact open of an affine:
  `hV : ∀ Q, IsCompact (Q : Set V) → Scheme.IsQuasiAffine Q.toScheme`.
  Mathlib's quasi-affine condition gives precisely the open embedding into its affine
  spectrum of sections, and includes compactness. No quasi-compactness of V is imposed.
- E is presented by `U : I → V.Opens`, `I : Type v`, `hI : Nonempty I`,
  `hqc : ∀ i, IsCompact (U i : Set V)`. Its points are `{x // ∀ i, x ∈ U i}`.
  This simply eliminates the named E by its defining equality, and does not require
  directedness or closure under intersections of the original family.
- Its inverse-image structure sheaf and section ring C are the existing
  `Scheme.intersectionStructureSheaf` and `Scheme.intersectionSections V U`.
  `Scheme.intersectionAlgebraSections f U` gives the same ring its actual R-action.
- The arbitrary open W and W contained in E are `W : V.Opens` and
  `hW : ∀ x : W, ∀ i, x.val ∈ U i`. No compactness of W is assumed.
- `intersectionOpenRestriction U W hW` constructs C to Gamma(W,O_W) as the
  inverse-image adjoint of the actual open inclusion comorphism, evaluated on the
  full subspace. It is not a map supplied as a hypothesis or chosen from existence.
- `intersectionOpenAffinization U W hW` applies the recorded affine adjunction
  to that restriction. It is exactly j_E restricted to W: the normalized j_E
  corresponds to id_C, so its restriction corresponds to this same ring map.
  The locality and uniqueness of j_E itself are supplied by the recorded
  `intersection_canonical_affine_embedding`, rather than repeated as a new construction.
- The first conclusion `IsOpenImmersion (...)` says j_E restricted to W is open.
  Its J is its open range; in the second theorem J and W isomorphic to J are explicit.
- V_T is `pullback f (Spec.map r)`, g is `pullback.fst`, E_T is the intersection
  of `g ⁻¹ᵁ U i`, and W_T is `g ⁻¹ᵁ W`.
- `α` is a ring isomorphism from the actual C tensor_R T. Its equation fixes its
  homomorphism to the recorded `intersectionBaseChangeMap`, which is the actual
  product-map construction c tensor t maps to g-sharp(c)t. Its definition and the
  full signature/docstring of `flat_affine_intersection_sections_base_change` were read.
- `IsPullback` uses the restricted j_E_T followed by Spec(alpha.hom), the actual
  restricted projection W_T to W, Spec of c maps to c tensor 1, and j_E restricted
  to W. Thus it asserts equality with the base change as a canonical cartesian
  square, without replacing the specified map by an arbitrary open immersion.
- The following `Set.range = (...) ⁻¹' Set.range` is exactly the asserted open image
  J times_S Spec T in the tensor-spectrum coordinates. The source maps are the
  canonical maps in that same square. An open subset with its restricted structure
  sheaf is determined by this underlying open; no reduced-subscheme encoding is used.
- For every `L : V.Opens`, `_hL : IsAffineOpen L`, `hLW : L ≤ W`, D is
  `Gamma(L.toScheme, top)`, with its actual scalar action in `intersectionOpenAlgebra`.
  The equation for μ on `intersectionScalarTensorPure` is exactly
  c tensor t maps to restriction(c) tensor t. `IsPushout` states the ring square
  with C to D and the two inclusions into the tensor products is a pushout in
  CommRingCat, so it tests all commutative target rings, not only fields or domains.
- The chart `δ` identifies D tensor_R T with Gamma(L_T,O), by its displayed pure
  tensor formula. The subsequent equality with the canonical restricted map shows
  μ is the corresponding geometric chart map, not merely some abstract pushout map.

Descent hypotheses and conclusions:

- The specialization uses `R A : CommRingCat.{u}`, `r : R ⟶ A`, flatness and
  `[Surjective (Spec.map r)]`. `V : Over (Spec A)` incorporates the assumed
  factorization through X; its S-map is `V.hom ≫ Spec.map r`.
- D is the recorded `Over.DescentDatum (Spec.map r) V`, in its transport encoding.
  Its canonical `invariantIntersectionOverlap r V D` is phi from V times_S X to
  X times_S V, with the orientation specified in the node. The dependency's full
  source, including D.toHom and overlap construction, was read.
- The same hV, U, hI, hqc, W, hW hypotheses are retained. `hEinv` expresses equality
  of the two inverse-image subsets by pointwise equivalence; `hWinv` expresses
  equality of their opens on the overlap. These are exactly E and W invariance.
- ψ is a ring isomorphism from A tensor_R C to C tensor_R A. Its equality with
  `intersectionBaseChangeMap`, `intersectionLeftComparison`, and the actual
  `intersectionSectionsMap` of phi uniquely characterizes its comorphism, including
  its direction. It is not an unspecified isomorphism.
- `intersectionOpenRightMap` and `intersectionOpenLeftMap` are explicit composites
  of the canonical restricted maps with the canonical section comparisons. The
  isomorphism k is phi restricted to W times_S X, fixed by its equality with the
  two open inclusions. Their next equation is exactly
  theta composed with (j_E restricted to W times id_X) equals
  (id_X times j_E restricted to W) composed with restricted phi.
- The following image equality says theta sends J times_S X onto X times_S J.
  The first theorem identifies these ranges with the actual open base changes.
- F is the affine scheme datum whose overlap is Spec(ψ), fixed by the explicit
  tensor/pullback coordinate equation already used in the sibling interface.
  No effectivity assertion is added here.
- J is an open of Spec C, its set equals the range of j_E restricted to W, and
  `e : W.toScheme ≅ J.toScheme` has composite with J's inclusion equal to that map.
- `hhA` asserts this map is over X. For every test scheme H, equal-S-image pair of
  X-points a,b, and W-point vW over a, the final existential vW' is its restricted
  D-transport, and its image in Spec C is the F-transport of the original image.
  Together with e, this is exactly W isomorphic to J intertwining the restricted
  descent data, including their cocycles. The explicit proofs in the signature only
  verify that the named maps are morphisms over X; they prove no mathematical clause.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and the
  equivalent absolute `QuasiSeparatedSpace` interface used by both section dependencies.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, fst, snd;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullbackPushforwardAdjunction`.
- `Sheaf.AlgebraicGeometry.RingedSubspace`: `ringedSubspace` and
  `locallyRingedSubspace` in `AlgebraicGeometry.LocallyRingedSpace`. The intersection
  dependency uses the same explicit inverse-image sheaf on the intersection presentation;
  the preceding embedding theorem supplies its locally ringed interpretation.
- `Sheaf.AlgebraicGeometry.IntersectionStructureSections`: `intersectionInclusion`,
  `intersectionStructureSheaf`, `intersectionSections`, `intersectionRestriction`.
- `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`: `intersectionSectionsMap`,
  `intersectionAlgebraSections`, `intersectionScalarTensor`, `intersectionTensorSource`,
  `intersectionScalarTensorPure`, `intersectionBaseChangeMap`, and its flat theorem.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `ΓSpec.adjunction`, the scheme
  restriction of the recorded `ΓSpec.locallyRingedSpaceAdjunction`.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`,
  `DescentDatum.toHom`, its universal point and transport laws.
- `def-a1-invariant-intersection-affine-coordinates` now owns the existing plain
  definitions in `Sheaf.AlgebraicGeometry.InvariantIntersectionAffineDescent`: the
  canonical overlap, left tensor and pure tensors, comparison, swap, affine model,
  and affine overlap coordinates. The item cites this definition node in stmt_deps.
  The sibling theorem `invariant_intersection_affine_descent` remains a proof-side
  ingredient in the theorem docstring (step 2), not a statement dependency.
- `def-a1-intersection-section-tensor-comparison` owns the existing section maps,
  scalar algebra, tensor source and pure tensors, and canonical base-change map in
  `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`. Both the item and
  the affine-coordinate definition node cite this definition node. The existing
  `lem-a1-intersection-sections-flat-base-change` remains in the item's proof_deps.
- Proof imports retain the recorded canonical-embedding, inverse-image-stalk and open
  base-change interfaces. Tensor universal-property declarations are available from
  the public tensor imports of the section comparison dependency.

Edge cases checked before drafting and again after elaboration: W empty; E empty
(nonempty indexing is retained and does not assert E nonempty); V empty; zero rings
and T=0; identity base change T=R; an affine V with E=V; W not quasi-compact;
non-directed and repeated members of the presenting family; arbitrary set-index universe v;
nontrivial descent datum and identity transport. Restriction and tensor maps are actual
functorial maps in every case. Neither spectrum nor section ring requires nonzero data.
No statement fault or STATEMENT-DISPUTED finding; no source correction is made.

Searches performed on this assignment:

- msearch leanfinder, query “Canonical map from an open in an intersection of quasi
  compact opens to its spectrum of sections is compatible with flat base change and
  descent”: eight hits on ordinary open-restriction naturality, including
  `Scheme.Opens.toSpecΓ_SpecMap_map`; none states the whole item.
- msearch loogle, query `AlgebraicGeometry.Scheme.toSpecΓ,
  AlgebraicGeometry.Scheme.toSpecΓ_naturality`: one hit, `Scheme.toSpecΓ_naturality`,
  which concerns schemes and their own global sections, not this intersection ring.
- msearch grep, query `intersection.*[Ee]quivarian|invariant.*affinization|toSpecΓ_naturality`
  in AlgebraicGeometry: fourteen ordinary naturality hits, none the whole statement.
- msearch leansearch, query “Canonical affinization of an intersection of quasi compact
  opens commutes with flat affine base change and is equivariant under descent data”:
  eight hits on generic affine/flat descent and quasi-separatedness; no exact match.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for this node id, intersection/equivariance,
  and invariant/affinization: no declaration for this item. The complementary sibling
  affine-descent module was found and reused. rg on Mathlib and both project roots for
  every introduced declaration name found no collisions. Existing open-affinization and
  invariant-open-image lemmas were read; they do not state the intersection comparison.

## Second reading by Q58

This is a second pass by the dispatched worker, not a claimed independent-agent review:
the dispatch explicitly prohibits starting other agents. The maintainer performs the
independent delivery review. I reread the node, Tag 0APK, both theorem signatures and all
six helper definitions. The first theorem retains the flat-only case, arbitrary W,
canonical tensor map, chart formula and pushout. The second retains the factorization,
faithfully flat cover, both invariance hypotheses, psi's comorphism orientation,
restricted-overlap equation, open image and restricted transport compatibility. The
chart comparison δ was included to tie the ring pushout to the geometric canonical map;
the psi coordinate equation and affine datum use the existing sibling constructions.
No mathematical hypothesis or clause was dropped or added. Compile-time repairs only
made imports public and made the over-category commutativity proof terms explicit.


## New nodes

`def-a1-intersection-section-tensor-comparison` records the existing definitions in
`Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`, with `existing: true`.
The primary signature is `intersectionSectionsMap`; its declarations list also names
`intersectionSubsetMap`, `intersectionSheafMap`, `intersectionScalars`,
`intersectionAlgebraSections`, `intersectionScalarTensor`, `intersectionTensorSource`,
`intersectionTensorMap`, `intersectionScalarTensorPure`, and `intersectionBaseChangeMap`.
The statement specifies each construction: induced continuous subspace map, adjoint
sheaf comorphism, evaluation on global sections, structural scalar map, scalar algebra,
right-factor tensor scalar structure, pure tensors, product map on a commutative square,
and its pullback specialization. These are the canonical constructions of Stacks 0APJ,
`lemma-affine-base-change`, used in the 0APK diagram. The general commutative square
requires its commutativity and subset-containment proofs; the pullback specialization
supplies them canonically. There is no flatness, quasi-separatedness, compactness, or
nonempty-family requirement on the constructions themselves, and no isomorphism claim.
The node uses the recorded intersection sheaf, inverse image, scheme, spectrum, and
fibre-product definition nodes. The empty intersection (empty index type), empty
subspace, zero rings, and arbitrary family universes are admitted by these definitions.
The map's scalar compatibility uses the existing named `intersectionScalars_map`
theorem; only this proof is postponed, with no unknown data chosen.

`def-a1-invariant-intersection-affine-coordinates` records the existing definitions in
`Sheaf.AlgebraicGeometry.InvariantIntersectionAffineDescent`, with `existing: true`.
Its primary declaration `invariantIntersectionOverlap` is the pullback lift whose
projections are the structure map on the first V-projection and D.toHom. Its remaining
listed declarations are `intersectionLeftTensor`, `intersectionLeftTensorPure`,
`intersectionTensorSwap`, `intersectionLeftComparison`, `intersectionAffineModel`,
and `intersectionAffineOverlapIso`. The tensor is A tensor_R C; its swap reverses the
two factors. The left comparison composes that swap, the right base-change map, and
section pullback along pullback symmetry. The affine model is Spec of the actual
section ring with the induced A-action, and the overlap isomorphism is the canonical
pullbackSpecIso, after identifying the structural composite. These are precisely the
coordinate constructions in Stacks 0APK, `lemma-ind-quasi-affine`, before the final
canonical diagram. They use the new section-tensor definition node and the existing
scheme, spectrum, intersection, descent-datum and pullback definition nodes. There
is no assertion of invariance or effective descent here. Empty V, empty E, zero rings,
identity r, and empty/repeated presentation families cause no change of construction.

For each new node the searches were run afresh on 2026-10-23 and recorded in its
mathlib_searches. LeanSearch and LeanFinder each returned eight generic hits: section
restriction and open-immersion APIs for the section node; gluing and pullback APIs for
the affine-coordinate node. The exact queries and returned declaration names are in
the JSON records and searches.jsonl. Mathlib grep for each node's construction names
returned zero hits. rg over lean/WeilConjectures found no definitions, and rg over
lean/Sheaf found exactly the two existing modules used here. Targeted rg over all
DAG nodes found only the two theorem records; no definition node owned these notions.
blueprint_refs.py search intersection sections returned 15 unrelated blueprint nodes;
search invariant intersection returned one unrelated Tor-amplitude node. Neither is
the same definition. blueprint_refs.py ancestor identified lem-a1-affine-hc0; both
new nodes retain that ancestor with the item's complete via chain and precise place.
No existing construction was copied or redeclared; no new Lean module is needed.

## Returned delivery repair

The return on immutable head b9a2e73b3bf6 identified two ownership errors, H2 and a
theorem statement dependency. Both are repaired by the two definition nodes above.
The item no longer adds lem-a1-invariant-intersection-affine-descent to stmt_deps;
it adds the two definition nodes instead. The theorem remains a proof-side ingredient
through the unchanged proof docstring and module import. The already recorded flat
base-change theorem remains in proof_deps. No theorem is used via .choose to provide
these plain definitions. No theorem statement, proof, proof_deps, or other existing
node is changed. The saved packet was first dry-run unchanged (067a17a147a passed),
then repaired against current main's node, whose only differences were the saved lean
record and the erroneous added theorem dependency. The returned head's Lean and
mathematics are retained exactly as the reviewer requested.

The second reading by Q58 for this repair read both new nodes against the existing
full definition signatures and bodies and Stacks 0APJ/0APK. Each clause is constructional:
no theorem conclusion or extra hypothesis has entered a definition. The two sets of
owned declarations are disjoint. The affine-coordinate node depends on the section
node, never on the theorem or on this item; hence there is no new dependency cycle.
The original hypothesis-by-hypothesis review above still applies to the unchanged
Lean signatures. This remains an in-thread self-check, as dispatch forbids agents.


Server validation found that the live blueprint ancestry has four further ancestors
beyond the older read clone's chain. Both new nodes' blueprint.from.via now include
lem-a1-normal-locally-constant-finite-section, lem-a1-normal-proetale-monodromy,
lem-a1-smooth-lisse-integral-lattice and lem-a1-degree-zero-compact-support-sections,
exactly as reported by the server preflight. No mathematical or Lean change was needed.
The explicit scompile.py check passed (sandbox 8.7 s, library 3.1 s).
