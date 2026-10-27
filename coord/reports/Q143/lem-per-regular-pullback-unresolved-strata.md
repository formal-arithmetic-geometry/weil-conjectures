## Worker report

The delivery states `lem-per-regular-pullback-unresolved-strata` in
`Sheaf.AlgebraicGeometry.RegularPullbackUnresolvedStrata`. Four named theorems carry
`by sorry`; no result is proved. A supporting definition node exposes the actual sets,
closed ideals and density predicate, with real data throughout. The item's mathematical
statement, proof and proof dependencies are unchanged. Its statement dependencies gain
three already recorded interfaces and the new definition node.

The source was read directly at
https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf
(Temkin arXiv:0904.1592v2): §§2.1.6--2.1.10, 4.1.1--4.1.3 and 4.3.
The latest blueprint was searched through `tools/blueprint_refs.py`; the item's ancestor
is `lem-per-artin-gabber-affine-curve`, not a unit statement. No statement correction or
dispute is needed.

Hypotheses and clauses, in order:

- All four theorems bind `X Y : Scheme.{u}`, `[IsReduced X]`, `[IsReduced Y]`,
  `[IsNoetherian X]`, `[IsNoetherian Y]`, `hQX` and `hQY` asserting
  `IsQuasiExcellent Γ(_, U)` for every affine open, and `h : Y ⟶ X` with
  `hRegular : IsRegularSchemeMorphism h`. Thus neither finite type, separation,
  characteristic zero, finite global dimension, surjectivity nor nonemptiness is imposed
  on h. The recorded regular-morphism definition is exactly flatness and regularity of
  each `h.fiberToSpecResidueField x` after every finite extension of `X.residueField x`.
  The finite-dimensional extension test includes the residue field itself. Universes are
  explicit; schemes, their residue fields and representing test fields all have universe u.
- `c_X(x)` is `ringKrullDim (X.presheaf.stalk x)`, with values in `WithBot ℕ∞`.
  This is local height, not Mathlib's opposite topological specialization-order height.
- `regular_pullback_geometry` asserts `(h.stalkMap y).hom.IsRegular` at every y,
  `singularSet Y = h ⁻¹' singularSet X`, and `IsReduced (pullback f h)` for every
  reduced locally Noetherian T and arbitrary `f : T ⟶ X`. These are precisely the
  Noetherian-setting reduced-base-change and singular-locus assertions. It also exposes
  regularity and singular-locus equality for the finite-type Noetherian base changes
  used for the tower schemes, centers and closed sets in the node's proof. Localizations
  are included: the morphism h has no finite-type restriction; the imported
  `IsLocalization.isRegular_and_fiber` supplies their regularity, including a localization
  meeting zero. No arbitrary-base-change local-Noetherianity assertion is smuggled in.
- A finite ordinary blowup tower is the existing `OrdinaryBlowupTower X`; `A.center i`
  is its actual quasi-coherent ideal, and `(A.center i).subscheme` is its full center,
  including nilpotents. The only center hypothesis `hCenters` is the recorded full
  `RingedSpace.IsCoherent ... (A.center i).toModules`, including the finite-type-kernel
  condition. Nonempty, regular or nowhere dense centers are NOT assumed.
- `unresolvedSet A` is exactly the terminal singular image union the finite indexed
  union of singular images of all centers, using `A.toBase` and each `subschemeι`.
  `unresolvedSet_isClosed_and_regular_pullback` asserts its closedness, existence of a
  contracted pullback tower with `OrdinaryResolutionComparison h A B`, and
  `unresolvedSet B = h ⁻¹' unresolvedSet A` for EVERY such comparison. The existing
  comparison identifies each level by a cartesian square, retains the extended ideals
  in order, and deletes exactly unit ideals. It is not an arbitrary comparison map,
  and no choice of an unspecified tower replaces the construction.
- The closed subset is `Z : Set X` with `hZ : IsClosed Z`; the integer is `r : ℕ`.
  `hHeight : ∀ x ∈ Z, (r : WithBot ℕ∞) ≤ ringKrullDim ...` says that there is no
  point of smaller height. S is literally `heightStratum Z r`.
- `lowestCodimensionStrata_regular_pullback` asserts `S.Finite` and
  `S ⊆ componentGenericPoints Z`. The latter uses Mathlib's generic points of the
  subspace Z, embedded back in X, so it means generic points of components of Z.
  The reduced closure C is `(reducedClosureIdeal S).subscheme`; its support is
  `closure S`, by the existing vanishing-ideal API.
- The equality `heightStratum (h ⁻¹' Z) r =
  componentGenericPoints (h ⁻¹' closure S)` gives EXACTLY the claimed points, in both
  directions. The ideal equality `(reducedClosureIdeal S).comap h =
  reducedClosureIdeal (heightStratum (h ⁻¹' Z) r)` identifies their reduced closure
  scheme-theoretically with `C ×_X Y`. This is stronger than a mere support equality
  in presentation only: `comapIso` identifies the pulled-back ideal's subscheme with the
  canonical fiber product over Y, so ideal equality is exactly equality of the closed
  subschemes the node identifies. The vanishing ideal on the right is radical.
- For EVERY generic y of the pulled-back C, the last conjunct gives `h y ∈ S`,
  `ringKrullDim (Y.presheaf.stalk y) = (r : WithBot ℕ∞)`, and regularity of the actual
  local ring homomorphism `(h.stalkMap y).hom`. Its target point s is h y, as required;
  no arbitrary local map or field-valued substitute is introduced.
- In the last theorem `P : Scheme`, `p : P ⟶ X`, `[IsProper p]`, and
  `I : P.IdealSheafData` are the proper ambient scheme and its closed center.
  `[IsReduced I.subscheme]` is reducedness of the center. With `f = I.subschemeι ≫ p`,
  `hPure : HasPureCodimension (Set.range f) e` is pure codimension e of its image.
  `hDense : IsGenericallySchematicallyDense f` says on EVERY open of the center that
  functions with the same germs at points over generic image points agree. This is
  exactly the local-scheme schematic-density test in the node and Temkin §2.1.6, not
  just topological density or the existence of a dense open.
- `equicodimensionalCenter_regular_pullback` uses the actual `pullback f h` and its
  structural map `pullback.snd f h`. It asserts reducedness and properness over Y,
  and, if the pulled-back center is nonempty, the same pure-codimension-e and schematic
  density properties for its actual image. Thus it explicitly retains the node's empty
  exception. The local regularity assertions for these finite-type pullbacks are also
  supplied by `regular_pullback_geometry`.

Dependency declarations read and reused:

| Node | Module and declaration |
| --- | --- |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian; IsNoetherian combines this with compactness |
| def-exc-excellent-ring | Sheaf.RingTheory.ExcellentRing: IsQuasiExcellent, not the stronger IsExcellent |
| def-weil-regular-scheme | Sheaf.AlgebraicGeometry.IsRegularScheme: IsRegularScheme = IsLocallyNoetherian and the upstream stalkwise IsRegular |
| def-nagata-global-blowup | WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType, publicly exposing WeilConjectures.AlgebraicGeometry.Coherent: RingedSpace.IsCoherent |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat: Flat, with iff_flat_stalkMap |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber: Scheme.Hom.fiber and fiberToSpecResidueField |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper |
| def-per-regular-scheme-morphism | Sheaf.AlgebraicGeometry.RegularSchemeMorphism: IsRegularSchemeMorphism |
| def-trf-ordinary-resolution-rule | Sheaf.AlgebraicGeometry.OrdinaryResolutionRule: OrdinaryBlowupTower, toBase, OrdinaryResolutionComparison |
| def-weil-pbc-g-ring | WeilConjectures.RingTheory.GRing, public through ExcellentRing: RingHom.IsRegular |

The new definition module also uses the already recorded Mathlib `ringKrullDim`,
`genericPoints`, `IsGenericPoint`, `irreducibleComponents`, `Scheme.Hom.ker`,
`Scheme.IdealSheafData.vanishingIdeal` and `comap` interfaces. In particular
`reducedClosureIdeal` constructs its data directly with `vanishingIdeal`; it does not
select a closed scheme from a postponed existence theorem. `toModules` is the existing
kernel construction in WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module.

Proof dependencies with recorded declarations are imported privately, including the
regular-local, localization and base-change ring interfaces, fibre-stalk quotient,
regularity ascent/descent, geometric reducedness, blowup geometry/properness, reduced
closed subschemes, going down, height formula and total fractions. The two blowup
base-change nodes have closed upstream audits, whose declarations
`blowupFlatBaseChange` and `blowupFlatBaseChangeIso` were read and are imported from
WeilConjectures.Blowup.FlatBaseChange. The unrecorded proof nodes
`lem-per-quasi-excellent-finite-type-stability` and
`lem-trf-regular-locus-affine-chart-gluing` have no module to import; their steps remain
in the theorem docstrings for stage 3. No missing statement prerequisite is left behind.

Edge cases checked before and after writing:

- Empty schemes and empty localizations: no `Nonempty` assumption on X, Y or h.
  Empty point sets and zero-ring spectra remain permitted.
- Empty Z or S, r = 0, and r larger than every height: the finite-set and component
  statements become the correct empty or generic-point assertions. The vanishing ideal
  of the empty closure is the unit ideal, whose subscheme is empty.
- Zero-length towers: `Fin A.length` is empty; only the singular image of the initial
  (also final) scheme contributes. `Fin.last` is valid also at length zero.
- Unit centers and nonempty Cartier centers: contraction deletes precisely the former;
  the latter remain even though their blowup map may be an isomorphism.
- Nonreduced centers in the unresolved-set theorem: singular loci are those of the
  complete center schemes. Reducedness is imposed only in the final center theorem.
- Disconnected and nonequidimensional ambient schemes: local dimensions are used;
  no finite-dimensionality, catenarity or equal component dimensions is assumed.
- Positive-dimensional regular fibres: only the fibre-generic points have height r;
  the theorem does not incorrectly identify every point over S with the lowest stratum.
- Nonsurjective regular h may lose whole components or make a center empty; there is
  no bijection S with its inverse image and no hidden nonemptiness requirement.

Searches performed:

1. msearch leanfinder: “Regular base change preserves singular loci and lowest codimension
   strata and unresolved sets of blowup towers”: eight hits, smooth base-change results
   and elliptic-curve nonsingularity; no exact statement.
2. msearch loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.IsReduced`: four hits,
   the existing geometrically reduced pullback results only. The relevant signatures
   in Mathlib.AlgebraicGeometry.Geometrically.Reduced were read and imported.
3. msearch grep: `singularLocus|unresolved|OrdinaryBlowupTower` in AlgebraicGeometry:
   zero Mathlib hits. Local rg of WeilConjectures and Sheaf found the existing ordinary
   tower and regular-morphism interfaces; both are reused.
4. msearch leansearch for the unresolved-locus union, height strata and generic-image
   schematic density: eight hits including smoothLocus, unramifiedLocus, zero loci and
   Scheme.height_of_isClosed. None defines this combination; notably topological order
   height has the opposite convention from the local height required here.
5. msearch leanfinder for definitions of unresolved sets, codimension strata and
   generic-image germ injectivity: eight spreading-out/germ-injective scheme hits,
   which concern extension from one local scheme, not joint section-germ injectivity
   over generic image points.
6. msearch grep `unresolved|heightStratum|SchematicallyDenseOver|genericPointsOf`:
   zero hits. Local rg in WeilConjectures/Sheaf found only unrelated uses of
   “unresolved” and proof-docstring mentions, not declarations of the new notions.
   DAG title search and blueprint_refs searches for “unresolved” and “schematic density”
   found no definition to reuse. The already existing `singularLocusIdeal` is the ideal
   of the closed singular set, not this singular set or tower unresolved union;
   `SchematicallyDenseOpen` concerns an open subscheme, not this generic-image test.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py Q143 lem-per-regular-pullback-unresolved-strata`, in both sandbox and library
module forms. Final compiler exit code 0; no errors or unexpected warnings. The first
compile of the final theorem needed an explicit `: Scheme.{u}` on the pullback inside
`Nonempty`, to prevent inference of a pullback in Type; this was repaired and recompiled.
All binders and the universe are explicit; both auto-implicit options are disabled.

## New nodes

`def-per-unresolved-strata-geometry` defines the singular set, local-height stratum,
ambient generic points of a subset, reduced closure ideal, unresolved tower set,
pure ambient codimension and schematic density over generic image points. Its source
is Temkin §§2.1.6--2.1.9 and 4.1.1--4.1.3/4.3; Stacks 01J3 supplies the existing reduced
closed construction. These are the explicit geometric data the item uses, not new
assumptions about a resolution algorithm. The node cites the existing tower, ring
Krull dimension, generic-point/component and ideal-sheaf nodes. Three search kinds and
local DAG/project searches are recorded verbatim from msearch's result log in its
`mathlib_searches`. Shared existing constructions are called, never replaced by copies.
Every definition has real data; the module contains no postponed proof.

## Second reading by Q143

I reopened both Lean files and their node records for a separate second pass; this is
a worker self-check, with the independent maintainer review still to follow. The check
matched all common reduced/Noetherian/quasi-excellent and regular-fibre hypotheses,
verified that arbitrary non-finite-type h are included, and expanded every new definition.
In particular the unresolved union uses singularities of the center SCHEMES, S consists
of generic points of components of Z (not of X), the height equation uses stalk Krull
dimension, and the ideal equality gives the full reduced closed pullback. The last
hypothesis is section-germ injectivity on every open over generic IMAGE points, not
ordinary topological density. The actual center is closed in a proper ambient scheme,
and the same image codimension and schematic density are asserted on its literal fibre
product when nonempty. No mathematical mismatch or node correction was found. The only
elaboration repair was the explicit Scheme type annotation described above. Both node
signatures were extracted verbatim from their files, and all four postponed theorems
carry the corresponding steps of the node's thirteen-step proof in their docstrings.
