## Worker report

Q91, stage 2, item `lem-trf-nearby-specialization-slice`. The delivery states the node
in `Sheaf.Paper.NearbySpecializationSlice`, namespace
`AlgebraicGeometry.OrientedNearbyCycles.SpecializationSlice`. All seven postponed
statements are named theorems with entire `by sorry` proofs and source/proof docstrings.
Definitions contain actual constructions. No theorem is proved in this delivery.
The main statement and hypotheses of the DAG item are unchanged.

The module constructs the actual geometric slice with the universal `lift` from
`OrientedNearbyCycles`: its first leg is the geometric closed-fibre projection, its
second leg is global sections on that fibre followed by the point b, and its
orientation is the specified strict-local map c through `specializationDirect`.
It does not quantify over an arbitrary slice map. The point and exactness clauses
are separate named theorems, recorded alongside the main theorem. The natural
comparison is a theorem witness (a natural transformation invertible on D-plus),
with the specified ordinary-mate equations; no arbitrary map is selected by a
definition as a replacement for the canonical construction.

Hypotheses and clauses, in order:

1. A scheme morphism f of finite type is `{X S : Scheme.{u}} (f : X ⟶ S)` with
   `[LocallyOfFiniteType f] [QuasiCompact f]`. There is no Noetherian, separated,
   proper, or finite-presentation assumption. Both the original and every
   base-changed morphism are quantified; the latter finite-type instances follow
   from base change, and impose no condition on the base-change map itself.
2. The coefficient ring is `(Λ : Type v) [CommRing Λ]`. The annihilating integer is
   `(m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)`. This is equivalent to
   m annihilating the ring. There is no `Finite Λ`, `Nontrivial Λ`, or invertibility
   hypothesis. Scheme and coefficient universes u and v remain independent.
3. A complex in D-plus is an object `K : EtaleDerived.{u,v} X Λ` together with
   `ProperFibre.IsBoundedBelow (etaleDatum X) (Coeff Λ) K`, which is exactly the
   standard t-structure plus predicate. All these are the existing derived
   categories and constant-module coefficient lifts, not another derived category.
4. `SliceSpecialization S` binds algebraically closed fields, points a,b, the
   actual map `c : strictHenselizationScheme b ⟶ strictHenselizationScheme a`, and
   `over`, its equation over S. This allows identity specializations and extensions
   of the geometric fields, not just literal equal fields or topological pairs.
5. The three schemes are the existing `s.fibre f`, `s.specialTube f`, and
   `s.genericTube f`; these are precisely the three pullbacks in the node. The
   actual `s.i f` uses `strictHenselizationPointEvaluation`; `s.j f` uses c. The
   generic tube is the entire strict localization at b, never just Spec B.
6. `canonicalSlices f s` is the universal geometric morphism e. The theorem
   `canonicalSlices_points` asserts `IsSpecializationSlice f s (canonicalSlices f s)`.
   This is the existing natural equivalence on every triple generator between the
   stalk at x of e-inverse and the explicit compatible-lift set `slicePoint f s x`;
   it specifies the point (x,b,c), including the orientation, naturally in triples.
7. `slice_exact` asserts `PreservesFiniteLimits` and `PreservesFiniteColimits` for
   the actual constant-module `modulePull` of this geometric morphism. Thus it is
   the exact inverse-image functor required in the node, not an extra exactness
   hypothesis on an unspecified functor.
8. `restricted f s Λ` is `nearbyCycles f Λ ⋙ e.pull (Coeff Λ)`.
   `SliceSpecialization.complex s f Λ` is exactly r_b-star, then Rj_b-star, then
   i_a-star. `ComparisonFamily Λ` is a family of natural transformations from
   restricted to complex. The main theorem supplies α and asserts
   `IsIso ((α f s).app K)` for every bounded-below K. Restricting the natural
   transformation to the full plus subcategory therefore gives the displayed
   natural isomorphism, rather than just isomorphisms of cohomology groups.
   Ambient unbounded maps let its compatibility be stated without choosing a
   boundedness witness for every exact inverse image; invertibility is only
   asserted on D-plus, as in the node.
9. `Compatible Λ α` quantifies every Cartesian scheme square (`IsPullback`) and
   every `SliceChange` above it. That record has the point maps, pointed strict-local
   maps, commuting specializations, induced maps of all three fibre products, and
   their projection/i/j equations. It adds no Cartesian assertion about the j square.
   Its displayed equality is
   `e_T.pull.map β ≫ α_T = ρ.hom ≫ q_a.pull.map α ≫ ordinarySliceComparison`.
   β is the existing `baseChange` of `OrientedNearbyCycles`. The independent
   `ordinarySliceComparison` first uses the i composition comparison, then the
   transpose of the actual j direct-image counit, then the r composition comparison.
   It is not defined by conjugating β with α, and no invertibility of either mate
   is claimed.
10. `rho` comes from the existing generator-normalized module inverse-image square
    and the universal slice square. Its direct-image isomorphism is constrained
    on both projections. `pointExtension_existsUnique` normalizes the second
    projection by the actual b-field map on every skyscraper product projection;
    `globalSquare_existsUnique` uses the unique identification of global sections.
    These uniquely determining theorems justify their chosen definitions. They
    avoid an unconstrained point automorphism or a mere Nonempty choice.
11. `SuccessiveCompatible Λ α` explicitly states the equality for two successive
    Cartesian base changes and compatible specialization diagrams. On its left
    are the two ordinary β maps and α at the final base. On its right are the
    two normalized ρ squares, the pullbacks of α, and the two independent ordinary
    sliced counit mates. Functor maps are displayed, with no implicit equality
    of fields or site universes. `Compatible` also includes the composite square;
    the proof plan specifies mate pasting and coherent inverse-image composition.
12. For detection, the final conjunction quantifies every finite-type f,
    `A : VanishingDerived.{u,v} f Λ` with no boundedness assumption, and `r₀ : ℤ`.
    `sliceVanishing V coeff r₀ A` means exactly that every standard homology
    functor in degree q ≤ r₀ has zero object. Its iff quantifies all
    `s : SliceSpecialization S` on the right, with the actual e-derived inverse
    image. Thus every integer degree cutoff and every slice occurs.

The docstring of `nearbySpecializationSlice` transcribes all eleven DAG proof steps:
construct the global sheaf restriction on triple generators, derive using the
right-derived unit without claiming acyclicity after r-star, identify stalk maps
with the common tube cohomology, use stalk conservativity only for invertibility,
prove the underived counit square on all sections, derive that equality with
normalized units, paste mates, and use conservative triple points for unbounded
cohomology detection. No equality of derived morphisms is inferred from equality
of stalk maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded derived
  categories; the oriented interface realizes these on its transported sites.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleTopology`, `etaleMorphism`,
  `etaleComposition`, `Lift`, `lift`, `p₁`, `p₂`, `squareLift`, `squareMorphism`,
  `squareModules`, `etaleDatum`, `vanishingDatum`, `Coeff`, `EtaleDerived`,
  `VanishingDerived`, `moduleMorphism`, `nearbyCycles`, `baseChange`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationScheme` and
  its structural map; `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`:
  the canonical closed point and its factorization over the base. Geometric
  points use the recorded `Spec`, `Field`, `IsAlgClosed` formulation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, with Scheme pullbacks and the induced maps.
- `Sheaf.Paper.GeneralNearbySliceTest`: only the data definitions registered in
  the new existing-definition node below, including `SliceSpecialization`,
  `SliceChange`, `complex`, `ordinarySliceComparison`, `IsSpecializationSlice`,
  `sliceModules`, `sliceSquare`, and `sliceVanishing`. Neither its theorem
  `general_nearby_slice_test` nor its `GeneralNearbySliceStatement` is used.
- `Sheaf.Paper.OrientedProperFibreExchange`: `ProperFibre.fibreGlobal`,
  `fibreFactor`, `specializationDirect`, `pointComposition`, `IsBoundedBelow`.
  Its already landed node is added to stmt_deps. A graph traversal of the union
  of statement and proof edges finds no path from that node back to this item.
- The published modules of all stated proof dependencies are imported without
  `public`, in accordance with the stage-2 convention. Mathlib proof matches
  include affine morphism permanence, D-plus injective representatives,
  K-injective localization, finite-limit preservation, and mate pasting.

Edge cases checked before and during writing: empty X or S (all definitions and
quantifiers remain meaningful), the zero coefficient ring with m=1, infinite
rings of bounded torsion, residue characteristic dividing m, identity
specializations, nontrivial and transcendental algebraically closed field
extensions, identity and arbitrary non-finite-type base-change morphisms,
negative cutoffs r, and unbounded A. No choice of one pair replaces the all-slices
test. Empty fibres give the unique global-sections identification. Independent
u and v are retained by the existing AsSmall/ULift site and coefficient transport.

Searches (msearch.py, Q91/item, actual logged results):

- LeanFinder, `geometric specialization slice oriented nearby cycles strict localization`:
  eight results about specialization/localization, none the slice theorem.
- Loogle, `CategoryTheory.GeometricMorphism, AlgebraicGeometry.Etale`: zero hits;
  service reports unknown `CategoryTheory.GeometricMorphism`, so not treated as
  evidence that no such project notion exists.
- Mathlib grep, `nearbyCycles|specializationSlice` in CategoryTheory: no hits.
- LeanSearch, `nearby cycles specialization strict localization`: eight results
  about stalk specialization/localization, none the theorem.
- LeanSearch, `Geometric specialization as a pointed map between strict localizations with compatible base change diagrams`:
  eight results about prime/stalk specialization, no compatible geometric slice data.
- LeanFinder, `Geometric specialization diagram of strict localizations and sliced nearby cycle complex`:
  eight unrelated specialization/localization results.
- Mathlib grep, `SliceSpecialization|SliceChange|ordinarySliceComparison`: no hits.
- Direct upstream WeilConjectures searches for the item id, nearby/specialization
  names and the specialization-data declarations: no exact item or data declaration.
- Direct lean/Sheaf and DAG searches found the existing data in
  `GeneralNearbySliceTest` and the distinct geometric-generic-fibre slice theorem.
  Those definitions are reused. The latter theorem uses a geometric generic point
  and finite/invertible coefficients and is not this full strict-local assertion.
- `blueprint_refs.py search 'geometric specialization'`: zero nodes; broader
  `search 'specialization'`: ten blueprint nodes, none defining the requisite data.
  `blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`.

The original node has an inherited metadata discrepancy: `created.item` names
`lem-trf-nearby-proper-source-exchange`. Its review records this known issue.
That field is outside the stage-2 worker's authorized delta and remains unchanged.
There is no mathematical statement dispute or statement correction.

Validation: `scompile.py` compiled both the sandbox renaming and the actual library
module successfully, with no warnings or errors. All universes and binders are
explicit (`autoImplicit false`). The final dry run and delivery results are below.

## New nodes

`def-trf-specialization-slice-data` registers the independent geometric-specialization
data, compatible pointed change diagrams, their actual pullback maps and sliced
complex, the independent counit-mate comparison, the oriented-point criterion, and
the associated slice-family/module/vanishing notation. Source: ILO Exposé XI
§§1.8–1.9, 2.2–2.3, 4.3 and Orgogozo §1/Lemma 3.1.1. The three prescribed Mathlib
search kinds and upstream/project/DAG searches above find no independent definition
node. The Lean data already exist as auxiliary definitions in the landed module
`Sheaf.Paper.GeneralNearbySliceTest`, so this is `existing: true`, with no new Lean
file and no copied definitions. Every listed declaration was read in full. The
record explicitly excludes the downstream theorem. Its statement dependencies are
the already recorded geometric points, strict localizations, fibre products, and
oriented-nearby/constant-module constructions. In particular there is no edge to
`lem-trf-general-nearby-slice-test`, whose proof uses this item; this records the
independent data without a reverse theorem dependency.

## Second reading by Q91

A separate second pass by the same worker was made with the node, source interfaces,
and Lean file open. The dispatcher explicitly forbids starting other agents; no
independent reader was invented. This pass found and repaired the following issues:

- A first draft duplicated the specialization and compatible-diagram structures.
  Broader project search found the landed definitions; the duplicates were removed
  and the existing declarations reused and independently recorded as above.
- The second projection of a slice square cannot be fixed by an arbitrary point
  isomorphism. Its field-extension comparison now reindexes each actual skyscraper
  product, and uniqueness fixes both projections of the universal square.
- Section parameters unused in inferred helper signatures were removed from calls;
  every derived category and coefficient lift was checked with explicit u/v.
- The point formula is now an explicit named theorem, and the exactness statement
  applies to the actual module inverse image.
- The final cohomology test uses the existing standard-homology predicate, with
  arbitrary unbounded A and every integer r; the generic side stays the full
  strict localization. No finite-ring or invertible-integer assumption crept in.

The rereading checked the new definition record against every listed existing
signature and checked that it has no reverse theorem edge. The main comparison
uses the dependency's β and the independently constructed j-counit γ, and the
pasted equality displays the actual functor maps. All definitions have real data;
choices from postponed theorems are made only where their normalized statements
uniquely determine the selected isomorphism. No definition chooses α arbitrarily.

Final validation: `deliver2.py Q91 lem-trf-nearby-specialization-slice --no-push`
returned `OK (dry run)` for commit `432f737c9a`: preflight passed and both the
new module and existing-declaration checks compiled. No proof or live library was
modified directly. Declaration-name searches in `dag/lean_names_upstream.json`,
Mathlib, upstream WeilConjectures, and the project found no collisions for the
new `SpecializationSlice` namespace declarations.
