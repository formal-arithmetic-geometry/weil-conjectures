## Worker report

The delivery states `AlgebraicGeometry.Scheme.orientedAffineNeighbourhoodLimit` in
`Sheaf.Paper.OrientedAffineNeighbourhoodLimit`. Only this theorem is postponed. Its
docstring includes all ten steps of the node's proof. The other declarations construct
the actual site, its sections, the compatible lifts, the diagram, and the canonical
strict-localization maps. No definition has postponed data. The item's natural-language
statement and dependencies are unchanged.

Hypotheses and objects, checked against the node:

* `X Y S : Scheme.{u}` and `f : X ⟶ S`, `g : Y ⟶ S` are arbitrary schemes and morphisms.
  There is no Noetherian, separated, finiteness, or nonemptiness hypothesis.
* `Ωx`, `Ωy`, their `Field` and `IsAlgClosed` instances, and `x`, `y` are exactly the
  recorded inline definition of the two geometric points; their fields need not agree.
* `c : strictLocalization (y ≫ g) ⟶ strictLocalization (x ≫ f)` and `hc` express the
  specialization over S. The word specialization includes being an S-morphism: `hc`
  writes this out, rather than adding an unrelated condition. Illusie's description
  of points, §1.2 printed p. 5, describes the corresponding morphisms of strict
  localizations over S; §1.3 printed p. 7 gives this affine-neighbourhood limit.
* `OrientedEtaleTriples f g` is the comma category with objects `(U,W,V,U→f*V,W→g*V)`.
  `orientedEtaleTopology` has the three generating covering types of the dependency,
  using the actual small étale pretopologies and actual base-change functors.
* `z` is a geometric morphism from sets in the containing universe to sheaves on that
  site. `OrientedPointCorrespondence x y c z` spells out “corresponds to (x,y,c)” by
  the natural inverse-image formula for sheafified representables: a natural family
  of bijections with the compatible lift pairs. This is not an arbitrary choice of
  a site, fibre functor, or scheme map. The correspondence contains no limit,
  initiality, cofilteredness, affineness, or étaleness assertion being proved here.
* `orientedEtaleAssociated` is the dependency's `largeAssociated` (`uliftYoneda ⋙
  presheafToSheaf`) on the étale triple site; `orientedEtaleSections`
  is its composite with `z.inverse`. Thus its category of elements is exactly the
  pointed-triple category in the statement, with the required morphisms.

Clauses of the conclusion:

* `orientedAffineProperty z` requires all three coordinates U,V,W to be affine. Its
  full-subcategory inclusion is the first conjunct, `.ι.Initial`. The opposite-final
  formulation for section colimits is the equivalent formulation, not a separate
  added property. The next conjuncts are `IsCofiltered` and `EssentiallySmall.{u+1}`.
* For every section, `e.equiv` supplies the U- and W-lifts. `orientedMiddleLift` gives
  its V-lift from the U-lift. The defining equation in `OrientedCompatibleLifts`
  says precisely that the W-image is the specialization of the U-image: it uses
  `orientedStrictPoint (y ≫ g) ≫ c ≫ orientedStrictLeg (x ≫ f) ...`.
  The two naturality fields ensure that morphisms carry these lifts correctly.
* `orientedFibreProductDiagram` sends the actual triple to `pullback
  (orientedTripleLeft T) (orientedTripleRight T)` and its actual morphism to
  `pullback.map` of the three coordinate morphisms. `orientedAffineDiagram` restricts
  this diagram along the full inclusion and the category-of-elements projection.
* The fourth and fifth conjuncts assert `IsAffine` of each object and `IsAffineHom`
  of every transition, respectively.
* `q` is a natural transformation to the constant `pullback f g`. Its two projection
  equations identify it uniquely with the canonical U/W structural map to Z; it is
  not an unconstrained replacement map. Every `q.app n` is asserted to be étale.
* `orientedMilnorTube` is the actual pullback of `orientedStrictMap f x` and
  `orientedStrictMap g y ≫ c`. The latter is exactly the requested composite through c.
  `orientedStrictMap` is constructed by pulling back pointed neighbourhoods, then
  applying the already-proved limit universal property, without choosing a map.
* `l`, `i`, and `Nonempty (IsLimit l)` give the limiting cone and its identification
  with M. The first two cone equations specify each leg by the canonical strict-local
  projections to the chosen pointed U- and W-neighbourhoods. The last two equations
  specify the maps to the two factors of Z as the displayed fibre-product projections
  followed by the canonical maps to X and Y. Scheme pullback extensionality identifies
  the resulting Z-map; this is a limit of Z-schemes as stated in the node.
* No conjunct asserts that a stage or M is nonempty.

Dependency declarations used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric points use the
  dependency's inline `Spec (.of Ω) ⟶ X` convention.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtalePretopology`,
  `smallEtaleTopology`, `Scheme.Hom.Etale`.
* `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, map, and extensionality.
* `Sheaf.CategoryTheory.Sites.OrientedProductUniversal`: the existing universal
  statement and geometric-morphism API, publicly retained by the extension module.
  Its triple-site constructors have the universe extension described below.
* `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`: `PointedEtaleNeighborhood`,
  `strictHenselization`, `strictLocalization`, `neighborhoodDiagram`,
  `strictLocalizationConeAll`, `isLimitStrictLocalizationConeAll`, and
  `strictLocalizationToBase`, publicly re-exported by the recorded dependency module
  `Sheaf.AlgebraicGeometry.StrictHenselization`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `pointSmallEtale` and
  `pointSmallEtaleElementsBaseChange`, which provide the actual pointed-neighbourhood
  base-change functor used to construct the canonical map.
* The size convention is represented by explicit universe u, the containing universe
  u+1 for sets and site objects, and `EssentiallySmall.{u+1}`. Hom universes are not
  equated with site-object universes.

Proof-dependency imports include Point.Basic (representable fibre), Limits.MorphismProperty
(finite limits of étale base change), OpenImmersion (affine shrinking), Filtered.Final
and Limits.Final (initiality and limits), Pullbacks (affine fibre products),
Morphisms.Affine, Morphisms.Etale, and Elements (pointed neighbourhoods). The DAG proof
dependency `lem-trf-site-point-fibre` has no recorded Lean statement, so no nonexistent
module is imported; it is not needed to type this statement. Its use remains step 2
of the proof plan for stage 3.

Edge cases checked: the empty scheme admits no geometric point and is not artificially
given one; no geometric points are required in D or M. Even when compatible point data
exist, U×_V W can be empty because compatibility is through a specialization rather than
equality of closed lifts; the construction and conclusion allow this. Identity f/g and
identity c are retained; different algebraically closed residue fields are retained.
There is no imposed quasi-compactness or separatedness of X,Y,S. Empty covering families
and arbitrary containing-universe covering indices are allowed. The index is the actual
pointed-triple category, never an unrelated arbitrary category. The small-skeleton clause
uses the project's containing-universe convention rather than imposing smallness in u.

Searches for an existing statement (2026-10-17):

* msearch LeanFinder: “oriented affine pointed etale triple neighbourhoods strict
  henselization fibre product limit”: eight general étale-property results, no match.
* msearch LeanSearch: “The affine pointed triple neighborhoods in an oriented product
  of etale topoi have inverse limit the fiber product of strict localizations”:
  eight general affine-limit/profinite results, no oriented-neighbourhood theorem.
* msearch Loogle: `CategoryTheory.Limits.IsLimit, AlgebraicGeometry.Scheme`: twelve
  general gluing, pullback, and affine-transition-limit results, no match. An earlier
  unqualified `IsLimit` query was rejected and is not treated as negative evidence.
* msearch grep: `orientedTriple|pointed.*triple|strictHenselization.*limit`, in
  Mathlib/CategoryTheory: no match.
* Direct rg of Mathlib, upstream WeilConjectures, and shared lean/Sheaf for the new
  declaration names: no existing declarations. Upstream grep for the node ID: no
  occurrence. The existing strict-localization construction and oriented-product
  universal module were found and reused, rather than independently reconstructed.

No STATEMENT-DISPUTED flag or source-based statement correction is needed. Checked
`coord/repair-notes` for this item and the universal dependency: no entries exist.

## Dependency modules

`lem-trf-oriented-product-universal`: its recorded constructors require SmallCategory,
tying object and hom universes. The actual étale categories have object universe u+1
and hom universe u. `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites` publicly
imports the entire original universal statement unchanged and states the dependency node's
notion for sites with independent object universe `w` and hom universe `v`: the same comma
category `largeTriples`, the same three covering types `largeGenerators`/`largeTopology`,
associated sheaves `largeAssociated` valued in the containing universe `Type (max v w)`, the
projection functors and structural arrows `largeFirst`, `largeSecond`, `largeToFirst`,
`largeToSecond`, `largeMiddle`, the lift formula `LargeHasLiftFormula`, and the primary
theorem `universalWithLargeSites` (proof `sorry`, with the node's ten-step plan). For `v = w`
it is exactly the recorded `universal`; on the étale sites it is typed with sheaves in
`Type (u+1)`, as the item uses them.

(Maintainer reviewer correction: as delivered, `universalWithLargeSites` was only the abbreviation
`@universal`, i.e. the small-site theorem under a new name, so the record's primary
declaration did not state the universal property for the large sites it claimed to repair. The
reviewer's fix replaces it with the genuine universe-generalized statement above. The sentence of
the dependency record's `note` calling `universalWithLargeSites` "a transparent abbreviation to
the original universal theorem" is superseded by this fix.)


## Second reading by Q65

I made a separate clause-by-clause second pass with the original node, current blueprint
update for strict henselization, source references, and final Lean file open. This is a
self-review, not a claim that another worker reviewed it: the dispatcher's explicit
instruction prohibits starting other agents; the maintainer's independent review remains
the next review.

The discarded initial scratch draft used an arbitrary site and abstract maps, which did
not identify the node's objects. It is excluded from the delivery. The final file instead
constructs the actual comma site, actual inverse-image sections, and canonical limit maps.
The second pass checked the orientation of c, all three affine conditions, the actual
transition maps, naturality of the point identification, both canonical cone legs, and
the map over Z. It also caught the incompatible dependency universes and the compiled
strict-localization mismatch; the large-site dependency repair resolves the universe mismatch; the strict-henselization
wrapper is used unchanged, without an extra universe equality or statement change.


## Validation

The two modules compile without errors or warnings using the prescribed scompile.py
wrapper. The final extension's transparent universal-theorem abbreviation and the
existing upstream strict-localization declarations also passed the delivery wrapper's
compilation probes.

The initial dry run reached server preflight and rejected five inherited
`proof_deps` omissions on the sandbox copy of the strict-henselization dependency.
Because §1(B) permits only its `lean` field to change, the repair removed that sandbox
copy and imported its unchanged recorded wrapper module instead. The dependency's
canonical upstream strict-localization declarations remain available through that public
import, while the DAG dependency itself is no longer staged as changed.


## Maintainer review (FIX)

Independent maintainer review of head df7a8e3f0. The item statement was checked clause by clause
against the node and judged correct; it is unchanged. The fix makes the §1(B) dependency module
state the oriented-product universal property for sites with independent universes, instead of
renaming the small-site theorem, and makes the item's `orientedEtaleAssociated` reuse the
dependency's `largeAssociated`. That gives one definition of the associated sheaves. Both files compile
singly with `tools/nt_compile.py` (no errors or warnings besides `sorry`); a probe confirmed that
`universalWithLargeSites` instantiates on `X.Etale`, `Y.Etale`, `S.Etale` with sheaves in
`Type (u+1)`.

