## Worker report

The module `Sheaf.Paper.OrientedProductPointsConservative` states
`AlgebraicGeometry.OrientedNearbyCycles.orientedProduct_points_conservative`.
Its only postponed proof is this theorem. All six helper definitions have real data.
The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- The schemes and their arbitrary morphism are `{T B : Scheme.{u}} (f : T ⟶ B)`.
  There is no quasi-compactness, separation, nonemptiness, or finiteness hypothesis.
- The arbitrary commutative coefficient ring is `(Λ : Type v) [CommRing Λ]`.
  `Coeff.{u,v} Λ` is precisely the dependency's canonical `ULift` of Λ into the
  common site/coefficient universe `max (u + 1) v`. Its ring equivalence with Λ
  is the prescribed coefficient size transport, not a restriction on the ring.
- The topos is exactly `VanishingTopos.{u,v} f`, presented by the already defined
  `vanishingDatum f`. Its topology, projections, and universal lift are reused.
- Every geometric point x of T is quantified by `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)`; y has independent field Ξ and the
  corresponding binders over B. These are the inline geometric points of
  `def-weil-geometric-point`. No same-field condition is imposed.
- `geometricEtalePoint` transports Mathlib's `Scheme.pointSmallEtale` stalk and
  skyscraper adjunction through `etaleSheafEquivalence` and `punctualEquivalence`.
  The former is Mathlib's sheaf equivalence for the dependency's `AsSmall` site.
  The latter is evaluation on the one-object trivial site, hence an explicit
  presentation of sets. Both functors and their adjunction are constructed.
- The specialization c is an arbitrary natural transformation
  `((geometricEtalePoint y).comp (identity _)).direct ⟶
  ((geometricEtalePoint x).comp (etaleMorphism f)).direct`.
  Thus its orientation is exactly `y ⇒ f(x)` under the dependency's definition
  of a 2-morphism. It is not required to be invertible.
- `triplePoint f x y c` is the morphism of the existing `lift` with this cone.
  The lift carries both projection identifications and the compatibility equation;
  it is not a choice from the class of arbitrary points or functors.
- `tripleModules` applies the existing `moduleMorphism` to this geometric morphism.
  Its `modulePull (Coeff Λ)` is the specified exact inverse image, with the
  canonical constant-ring identification. Its target is module sheaves on the
  punctual site, equivalently Λ-modules. Using this presentation preserves and
  reflects isomorphisms and avoids introducing a second module inverse image.
- The first conjunct quantifies every `a : F ⟶ G` of
  `(vanishingDatum f).modules (Coeff Λ)` and states `IsIso a ↔ ∀ Ω Ξ x y c, ...`.
  The tested map is exactly `((tripleModules f x y c).modulePull (Coeff Λ)).map a`.
  `Site.modules` unfolds to the existing `SheafOfModules` of the constant ring.
- The second conjunct quantifies every `a : K ⟶ L` in `VanishingDerived f Λ`.
  Its right side uses `((tripleModules f x y c).pull (Coeff Λ)).map a`.
  `Morphism.pull` is the existing exact functor's `mapDerivedCategory`; the
  dependency's `VanishingDerived` is the actual unbounded `DerivedCategory`.
  No boundedness, truncation, or cohomological-dimension assumption appears.
- Both clauses are equivalences, including preservation as well as reflection.

Dependency declarations read and reused:

- `def-trf-oriented-nearby-cycles`: `Sheaf.Paper.OrientedNearbyCycles`;
  `EtaleSite`, `etaleTopology`, `etaleMorphism`, `VanishingTopos`,
  `vanishingDatum`, `Lift`, `lift`, `sheaf_isTopos`, `moduleMorphism`, `Coeff`,
  and `VanishingDerived`. In particular `lift` selects the compatible universal
  cone, and `moduleMorphism` uses the canonical constant-coefficient lift.
- `lem-trf-oriented-product-universal`:
  `Sheaf.CategoryTheory.Sites.OrientedProductUniversal`;
  `CategoryTheory.OrientedProduct.universal`, `IsUniversal`, and `paste`,
  as specialized by the nearby-cycle dependency's `orientation_universal`/`lift`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`, with inline `Spec (.of Ω) ⟶ X` and the signature/docstring of
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
  Its underlying Mathlib `SheafOfModules` and abelian instance are exactly the
  ones used by `Site.modules` and `VanishingDerived`; there is no copied category.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`, through the dependency's standard-universe derived category.

The stated proof dependencies have direct non-public imports of
`Sheaf.CategoryTheory.Sites.GeometricMorphism`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, and
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
The remaining proof dependencies are already public statement dependencies.
The three proof nodes `lem-trf-etale-topos-points-geometric`,
`lem-trf-finitary-site-enough-points`, and `lem-trf-oriented-affine-slice-site`
have neither a Lean record nor a Mathlib match on the read base, so there is no
module to import for them. They are used only by the postponed proof, whose
docstring records all seven DAG steps and their uses.

Edge cases checked before drafting: if T is empty there is no x, so both pointwise
conditions are vacuous. Every triple then has the empty type-(a) cover, so its
module-sheaf category and derived category are zero and all maps are invertible.
If B is empty a morphism f forces T empty too. The zero coefficient ring is
allowed. Arbitrary nonseparated and non-quasi-compact schemes are retained;
finite-cover arguments apply only to affine slices in the proof. Unbounded
complexes in both directions and every integer cohomological degree are retained.
Identity specializations and noninvertible specializations are both quantified.

Searches made before drafting (all through the prescribed tools or read-only rg):

- `msearch.py leanfinder`, query “Geometric points specialization triples jointly
  detect isomorphisms on sheaves of modules on an oriented product of etale topoi”:
  eight hits, including `Scheme.Modules.Hom.isIso_iff_isIso_app` and results about
  specializing maps and spreading out; none concerns the oriented-product points.
- `msearch.py loogle`, query `"oriented"`: twelve hits for order-comparison classes,
  no oriented-product topos statement.
- `msearch.py grep`, query `oriented[Pp]roduct|vanishing topos`: zero Mathlib hits.
- `msearch.py leansearch`, query “Stalks at specialization triples detect
  isomorphisms on oriented product module sheaves”: eight geometric/topological
  stalk isomorphisms, no matching theorem.
- `rg` of the upstream `WeilConjectures` sources for oriented-product names,
  “oriented product”, “vanishing topos”, and the exact item id: no matching statement.
- `rg` of `lean/Sheaf` located the recorded `OrientedNearbyCycles` module and
  `GeometricStalkToposPoint`, plus the existing stalk/skyscraper point in
  `LocalOrientedProjectionArrows`. The latter is specialized to one coefficient
  universe and the original étale site; the helper here explicitly transports
  the same Mathlib stalk/adjunction to the dependency's common universe and site.
  Searches for the new full names found no previous declarations; unrelated
  private `triplePointedObj` helpers concern strict-henselization ring triples.
- `rg` of `dag/lean_names_upstream.json` for the exact item id: no hit.

The source PDF was read locally: XI 1.8 explicitly uses a punctual topos and the
orientation `gy → fx`, and XI 1.10(b) identifies the localized oriented product.
The proof's affine-slice argument follows the reviewed node; its `source.place`
still mentions XI 2.7 and whole-site coherence, but the node's reviewed proof
and `split_report` already correct this attribution to XI 1.10(b) and the
finite-cover construction in XI 2.5. No statement correction is required.
No mathematical dispute, new node, or dependency-interface repair is needed.

Validation: every delivered Lean file is compiled through `scompile.py`, with
explicit universe and variable binders. The only theorem is left as `sorry`.
The required delivery dry run and push follow the clean compile.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
