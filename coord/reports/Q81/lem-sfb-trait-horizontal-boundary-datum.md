## Worker report

The delivery states `AlgebraicGeometry.TraitHorizontalBoundary.exists_horizontal_boundary` in
`Sheaf.AlgebraicGeometry.TraitHorizontalBoundaryDatum`. Its proof is `sorry`. Two helpers in the
same owning module, `lineIsoAt` and `IsLineCocycle`, contain real constructions and no postponed
proofs: they express the last clause using the already published transport presentation of
scheme descent. There are no new independent notions, new nodes, dependency repairs, or
statement corrections.

Source checked: BLR, *Néron Models*, 6.5 Theorem 1 proof, case (a), printed p.160, PDF p.166,
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf . The
paragraph chooses the generic effective divisor, takes its schematic closure, identifies its
pullbacks under the datum, and extends the datum to the associated line. The module docstring
records all twelve steps of the node's proof, including the saturation argument needed to show
that the specified closure, with its multiplicities, is Cartier.

Hypothesis-by-hypothesis correspondence:

- The rings B and C are `Type u` with `CommRing`, `IsDomain`, and
  `IsDiscreteValuationRing`. `Algebra B C` specifies the ring map, and
  `Module.FaithfullyFlat B C` states its faithful flatness.
- K and L are fields with `IsFractionRing B K` and `IsFractionRing C L`, respectively.
  Mathlib defines this as localization at the nonzerodivisors; for the domains here those
  are precisely the nonzero elements. `Algebra K L`, `Algebra B L`, and the two scalar towers
  specify the unique compatible extension of the ring map to fraction fields. These are
  structural choices, not an extra restriction on the faithfully flat DVR map.
- S and S' are literally `Spec (.of B)` and `Spec (.of C)`. The cover map is
  `Spec.map (CommRingCat.ofHom (algebraMap B C))` throughout.
- `X : Over (Spec (.of C))` is X' over S'. Its structure map has `Smooth`, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances. `IsSeparated` is the existing class
  whose field says that the diagonal is a closed immersion, as explicitly required by the
  node. The last two classes together mean finite type.
- `α : Over.DescentDatum ... X` is the recorded datum, including its identity, naturality,
  and cocycle. No second scheme descent definition is introduced.
- `Xη`, `r`, `hr` display the generic fibre by an arbitrary cartesian-square presentation.
  `X₀`, `q`, `hq` display the specified generic model and its scalar extension to L.
  `IsPullback` witnesses express the given base-change isomorphisms, not extra geometric
  assumptions. `hgeneric` says on every scheme-valued pair of generic points that α's
  transport identifies them exactly when their q-images in X₀ coincide. Thus the given
  datum on the generic fibre is the one from the specified X₀, rather than merely requiring
  an unrelated isomorphism of its underlying scheme with a scalar extension.
- `U : Over (Spec (.of B))` and `[IsAffineHom U.hom]` mean U is affine over S. Since S is
  affine, U is affine as an absolute scheme as well.
- `W : X.left.Opens` is U', and `[IsAffine W.toScheme]` is its stipulated affineness.
  `uW` and `huW` exhibit it as U base-changed to S'. `hrestricted` identifies its restricted
  transport with the one induced by U. This also implies invariance: for a point of W and
  a second base point with the same image in S, the cartesian square supplies the unique
  second point of W with the same U-image; `hrestricted` identifies it with α's transport.
  Thus neither effectivity of the restricted datum nor invariance is lost.
- `hdense` quantifies over every algebraically closed field Ω in the same universe as C
  and every geometric point `s : Spec Ω ⟶ Spec C`. The displayed dense subset is the inverse
  image of W under the projection of `pullback X.hom s`, exactly density in every geometric
  fibre. Empty fibres are permitted. The common universe can always be enlarged and does
  not quantify over fields too small for the coefficients.
- `UK`, `v`, `hv` are U_K, displayed by its base-change square. `iK` is its open immersion
  into X₀ and `hiK` says it is over K. `hopen` spells out the induced-open compatibility:
  for a point a of W and an L-point l above the same S' point, b is the corresponding UK
  point and c the corresponding generic-fibre point, and `b ≫ iK = c ≫ q`. Their cartesian
  squares uniquely determine b and c; this is the commutative base-change square of the two
  open immersions, tested universally. There is no freely chosen comparison morphism.

Conclusion-by-conclusion correspondence:

- `D₀ : X₀.left.IdealSheafData` and `D₀.IsInvertible` mean the generic effective Cartier
  divisor, using the recorded regular-principal-ideal definition.
- `(D₀.support : Set X₀.left) = (Set.range iK)ᶜ` states its exact support, including the
  possibility of the empty divisor.
- `D' : X.left.IdealSheafData` is the schematic closure, specified on every affine open V
  by the literal kernel of `((D₀.comap q).subschemeι ≫ r).app V.1`. Here `D₀.comap q` is
  the full scalar-extended closed subscheme, and its inclusion followed by r is j in the
  node. This avoids confusing Mathlib's largest quasi-coherent subideal `Hom.ker` for a
  general morphism with the raw sheaf kernel: the displayed affine-ideal equations assert
  the latter exactly. No radical, reduced subscheme, support-only closure, or arbitrary
  Cartier extension replaces the specified schematic closure.
- `D'.IsInvertible` and its support equation say the closure itself is Cartier and its
  support is exactly X' minus U'.
- `D'.comap (pullback.fst ...) = D'.comap α.toHom` is equality of the full two pulled-back
  ideals on the universal transport scheme `X' ×_S S'`. This scheme is canonically the
  first pullback of X' to `S' ×_S S'`; the second projection to X' is `α.toHom`. Therefore
  the equation is precisely the node's identification of the two closed subschemes by α,
  including multiplicities, not merely invariance of their supports.
- `Scheme.Modules.dual D'.toModules` is literally the recorded associated line O_X'(D').
  Its `IsInvertible` conjunct states the requested invertibility.
- The existential φ is an actual isomorphism of the tensor pullbacks of that specified
  line along the two universal transport maps. `IsLineCocycle` tests its twofold composite
  against the direct transport on all triples of base points and a scheme-valued point of
  X'. `lineIsoAt` is the pullback of φ along the unique universal lift, using the published
  section-normalized tensor-pullback composition comparisons. The final equality transport
  uses precisely `α.transport_transport`. Testing on the universal triple gives the usual
  triple-cover cocycle, and every test is its pullback. Because φ is already a sheaf-module
  isomorphism on the universal overlap, no independent naturality assumption is needed.
- There is no group datum, ampleness, nonemptiness, connectedness, irreducibility, or
  nonempty-special-fibre condition in the theorem.

Dependency declarations used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; the imported
  `QuasiCompact` class supplies its finite-type companion.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`, `toHom`,
  `transport`, `transport_transport`, and `transport_left_eq_lift_toHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `...Separated`:
  `IsClosedImmersion`, `IsSeparated` (the latter explicitly defined by the diagonal).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its published convention is
  `Limits.pullback`, equivalently an `IsPullback` square and its compatible projections.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: `IdealSheafData.toModules`,
  `Scheme.Modules.dual`, and the invertibility theorem for the dual ideal.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback` and
  `tensorPullbackSectionComp`. The latter's canonical normalization is used in `lineIsoAt`.
- Mathlib's `Scheme.IdealSheafData.comap`, `.support`, `.subschemeι`, and affine `.ideal`
  are used directly. All recorded statement dependencies are imported publicly; all
  recorded proof-dependency modules available in the input node are imported normally.

Edge cases checked before and after drafting: empty X', empty X₀, empty geometric fibres,
empty special fibre, U' equal to X', and the top ideal giving the empty Cartier divisor.
The generic scheme need not be integral or connected, nor geometrically connected. The
node's componentwise argument still applies. No characteristic or ramification bound was
introduced, and arbitrary faithfully flat DVR maps, not just finite or unramified ones,
are allowed. Algebraic closure fields and test schemes use the common universe of the
coefficient rings, with explicit universe and variable binders and disabled auto implicits.

Searches made with msearch.py (2026-10-24), recorded in searches.jsonl:

- LeanSearch: "effective Cartier divisor horizontal schematic closure descent datum over
  discrete valuation ring". Eight hits include `IdealSheafData.glueDataObj` and
  `IsClosedImmersion.overEquivIdealSheafData`, but none states this theorem.
- LeanFinder: "horizontal boundary datum trait finite boundary". Eight unrelated hits
  about composition, cube, and manifold boundaries.
- LeanFinder: "effective Cartier divisor schematic closure smooth trait and descent datum".
  Eight hits concerning ideals, closed subschemes, and smoothness, but no theorem matching
  the trait boundary and descent assertions.
- Loogle: "Boundary datum, Horizontal, Trait"; no hits, unknown identifier `Boundary`.
- Loogle: "Scheme.IdealSheafData, IsDiscreteValuationRing"; no hits, unknown identifier
  `Scheme.IdealSheafData`.
- Mathlib grep: "horizontal.*(Cartier|boundary)|boundary.*datum|exists_horizontal_boundary"
  in AlgebraicGeometry: zero hits. The preliminary grep used an erroneous nested Mathlib
  subdirectory; this proper AlgebraicGeometry search supersedes it.
- Project/upstream rg for "horizontal boundary", "HorizontalBoundary", "boundary datum",
  the exact node id, `exists_horizontal_boundary`, `lineIsoAt`, and `IsLineCocycle` found
  no existing trait-boundary statement or helper. Other boundary datum hits concern Weil
  inertia and unrelated horizontal differentials. The ideal and transport APIs above are
  reused instead of copied. The recorded upstream name index was also searched.

Validation: the only postponed proof is the named theorem. Both helper definitions have
real data. The first cocycle elaboration hit the default heartbeat bound; factoring that
same expression into `IsLineCocycle` and annotating its endpoint type avoids unfolding the
large ring-specific signature during elaboration. The limit was not increased. Compilation
and delivery preflight are run only through the prescribed server wrappers.

Completed validation: scompile.py returned exit code 0 for both the module-mode sandbox
probe and the actual library module, with no errors or warnings. deliver2.py --no-push
returned OK: the delivery commit passes the server preflight and per-file compilation.
The server wrapper waited for compiler capacity; the per-file limit was unchanged.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
