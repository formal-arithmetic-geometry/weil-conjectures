## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDescentSaturationQuasiAffineCover` states
`CategoryTheory.Over.DescentDatum.affine_descent_saturation_quasi_affine_cover`.
Its sole theorem has proof `sorry`. No definitions, auxiliary theorems, new nodes,
or dependency repairs are needed. The node's mathematical statement is unchanged.

Hypotheses and objects, in node order:

- Affine schemes A and B: `{A B : Scheme.{u}} [IsAffine A] [IsAffine B]`.
- The morphism p: `(p : A ⟶ B)`.
- Flat and surjective: `[Flat p] [Surjective p]`, precisely the recorded Mathlib
  properties, not assumptions about rational points or ring maps chosen separately.
- Finite presentation: `[LocallyOfFinitePresentation p] [QuasiCompact p]
  [QuasiSeparated p]`, the three conditions stipulated in the node and convention.
  The latter two are automatic between affines, but are displayed as the node
  explicitly spells out this meaning of finite presentation; they impose no
  further mathematical restriction.
- A scheme V over A with structure morphism π: `{V : Over A}`, with underlying
  scheme `V.left` and π equal to `V.hom`. This is the exact existing descent API.
- Descent isomorphism and cocycle: `(D : Over.DescentDatum p V)`. Its natural
  transport, identity and composition laws are the recorded equivalent form of
  the descent isomorphism over A ×_B A satisfying the cocycle over the triple base.
  No effectiveness assumption is imposed. The identity law follows from the
  cocycle and invertibility, so this interface adds no hypothesis.
- Separated π: `[IsSeparated V.hom]`; no properness assumption is used.
- Locally quasi-finite π: `(_hπ : V.hom.IsLocallyQuasiFinite)`, the recorded
  Stacks notion, including local finite type, rather than bare Mathlib
  `LocallyQuasiFinite`, which omits that requirement.
- No quasi-compactness or local finite-presentation hypothesis is imposed on π.
- Explicit `universe u` puts A, B, V and their pullbacks in `Scheme.{u}`.
  `V.left.affineOpens` is the actual set of all affine open subsets; no independent
  family-size or nonemptiness restriction is imposed. `autoImplicit` is false.

Every construction and conclusion:

- An arbitrary affine open C is `C : V.left.affineOpens`, with open `C.1` and
  inclusion `C.1.ι`. Mathlib defines this subtype by `IsAffineOpen`.
- The scheme C ×_B A is the domain of
  `pullback.map (C.1.ι ≫ V.hom ≫ p) p (V.hom ≫ p) p C.1.ι (𝟙 A) (𝟙 B) ...`.
  This is the canonical inclusion into V ×_B A, not an arbitrary map.
- `D.toHom` is precisely φ followed by the projection A ×_B V → V, as its
  docstring and full transport construction state. Composing the displayed
  pullback map with `D.toHom` therefore gives exactly r_C in the node.
- `∃ W : V.left.affineOpens → V.left.Opens` supplies the open subschemes.
  `(W C : Set V.left) = Set.range (...)` fixes their underlying sets to W_C;
  openness is the `Opens` type itself. The existential does not choose an
  unspecified saturation: equality to the specified image determines every W C.
- `IsCompact (W C : Set V.left)` is quasi-compactness without Hausdorffness,
  equivalently `CompactSpace (W C).toScheme` by compactness of a subtype.
- `C.1 ≤ W C` is the containment C ⊆ W_C.
- `IsQuasiAffineHom ((W C).ι ≫ V.hom)` is exactly quasi-affineness of the induced
  morphism from the open subscheme to A, using the dependency's definition.
- `(⨆ C : V.left.affineOpens, W C) = ⊤` says that these very opens cover V.
  The per-open and covering clauses concern the same family W.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`,
  `IsAffineOpen`, `Scheme.affineOpens` (available through statement imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (available through the imported morphism modules).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded separated component
  `AlgebraicGeometry.IsSeparated`, whose definition is in `Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  underlying the canonical open-subscheme inclusions.
- `Mathlib.Topology.Defs.Filter`: `IsCompact`, `CompactSpace` (transitive imports).
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `DescentDatum.toHom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and `pullback.map`.
- The scheme and size convention nodes introduce no separate declarations;
  their finite-presentation and universe conventions are expanded above.

Proof-plan imports include `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
(`UniversallyOpen.of_flat`),
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`
(`Scheme.Hom.isLocallyQuasiFinite_resLE`), and
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`
(`Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`). The other recorded
proof matches are already available in the statement imports: open-immersion
base change, compactness and quasi-separatedness of affine schemes, qcqs permanence,
`IsQuasiAffineHom.of_locallyQuasiFinite`, and `Scheme.isBasis_affineOpens`.
Their corresponding six proof steps are written in the theorem docstring.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-separated-locally-quasi-finite-morphisms-fppf-descend`, specifically the
reduction to a flat surjective finite-presentation map of affines, the displayed
saturation diagram, and the subsequent covering paragraph (Tag 02W8).
The node agrees with this source. There is no statement dispute or correction.

Edge cases checked before writing:

- Empty V: every range and open involved is empty, and the supremum is top in the
  one-element lattice of opens of the empty scheme. No nonempty binder is present.
- Empty C: C ×_B A and its image are empty, so compactness, containment and
  quasi-affineness of the empty open are consistent.
- Empty A or B: surjectivity forces A empty if B is empty, and a V over empty A
  is empty. The same conclusions remain meaningful.
- Identity p: the identity transport gives W_C = C; an affine C mapping to affine A
  is quasi-affine, as asserted.
- Non-quasi-compact V: the family may be infinite, and the theorem asserts only
  the quasi-compactness of each saturation, without a finite subcover of V.
- No base-field, characteristic, reducedness, Noetherian or rational-point
  assumptions appear. Set.range uses all scheme points.

Searches (2026-10-22; performed with the prescribed `msearch.py`):

- LeanFinder: "Saturations of affine opens under an fppf descent datum cover a
  separated locally quasi-finite scheme by quasi-compact quasi-affine opens".
  Eight results, including `quasiCompactCover_iff`, finite affine refinements and
  `Scheme.exists_isOpenCover_and_isAffine`; none concerns descent saturation.
- Loogle: `"DescentDatum", "IsQuasiAffineHom"`: zero results.
- Mathlib grep: `saturat.*descent|descent.*saturat|quasiAffine.*image|image.*quasiAffine`
  in AlgebraicGeometry: one hit, `preimage_opensRange_toSpecΓ` in QuasiAffine.lean,
  which concerns canonical maps of quasi-affine schemes, not descent saturation.
- LeanSearch: "For a flat surjective finite presentation map of affine schemes
  the saturation of every affine open of a separated locally quasi-finite scheme
  with descent datum is quasi-compact open and quasi-affine". Eight hits, including
  flat descent of morphism properties, quasi-compact covers, and quasi-separated
  affine opens; no exact result.
- `rg` of the project and upstream sources for
  `saturat.*[dD]escent|[dD]escent.*[sS]aturat|affine_descent_saturation|affineDescentSaturation`:
  existing orbit saturation and `DescentSaturationInvariantOpen` concern invariance
  and restriction of an already open saturation, not this geometric covering result.
  Read both `DescentSaturationInvariantOpen.lean` and `DescentOrbitSaturated.lean`.
  The former confirms the same pullback-map expression and `D.toHom` orientation.
- `grep -rn` of the node id in `lean/WeilConjectures`: no existing declaration.
  `rg` of the new theorem name in upstream sources, Sheaf and
  `dag/lean_names_upstream.json`: no collision.

## Second reading by N8

Re-read the node and final signature as a separate clause-by-clause pass. The
universal affine-open subtype quantifier covers every affine C. The map inside
Set.range has the same base B and projection orientation as the Stacks diagram;
its first factor is inclusion and its second is the existing universal transport.
The two affine-base hypotheses and the flat, surjective, lfp, qc and qs conditions
are explicit. Separatedness and the recorded finite-type-inclusive local
quasi-finiteness concern V.hom, while no finite presentation or compactness of
V.hom has appeared. Membership in Opens supplies openness, IsCompact gives
quasi-compactness, the lattice inequality gives containment, the composite to A
is the required quasi-affine morphism, and iSup equals top supplies the cover.
No mathematical mismatch was found and no statement correction was made.
This is the worker's second pass; the maintainer's independent review follows
this delivery, as specified by the dispatcher brief.
