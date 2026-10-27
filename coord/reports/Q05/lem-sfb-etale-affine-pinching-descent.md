## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAffinePinchingDescent` states
`AlgebraicGeometry.isPushout_of_etale_affine_pinching_exact`, with its proof `sorry`.
It also constructs the owning statement's canonical tensor comparison
`AlgebraicGeometry.pinchingTensorComparison` with real ring-homomorphism data.
This helper is listed in `lean.declarations` and carries the item's source and
blueprint docstring. It is a canonical map belonging to this theorem, as authorized
by the missing-helper rule; it introduces no independent notion or new DAG node.
The node's mathematical statement and dependencies are unchanged.

Sources read: Stacks Project, `more-morphisms.tex`, labels
`lemma-basic-example-pushout` (0ET0) and `lemma-pushout-fpqc-local` (0BMP).
The first proves the scheme pushout for the matching-pairs ring with one
surjective map. The second descends a colimit from an fpqc cover and its
pairwise overlaps using representable descent (023Q). The node's eight-step
argument supplies the stated exact-sequence and flat-base-change refinements;
the theorem docstring records all eight steps and their named dependencies.
The item is an auxiliary node, with `blueprint.is = null`.

Hypotheses, clause by clause:

- The schemes `X,C,N` are `{X C N : Scheme.{u}}`. Their given maps are
  `ν : C ⟶ X`, `i : N ⟶ X`, with precisely `[IsFinite ν]` and
  `[IsClosedImmersion i]`. The scheme B is the chosen `pullback ν i`, with
  `pullback.fst ν i` and `pullback.snd ν i` as its projections.
- The chart index is `{A : Type v}`, without `Finite`, `Small`, `Nonempty`,
  or a relation between `v` and `u`. The chart rings `P,E,T,D : A → Type u`
  have their respective commutative-ring instances. The structure maps out
  of `P a` are its three `Algebra` instances; the diagram maps are the
  actual `P a`-algebra homomorphisms `α a` and `β a`.
- The maps `q a : Spec (CommRingCat.of (P a)) ⟶ X` have `[Etale (q a)]`.
  They are affine source charts, rather than an extra assumption that the
  morphisms themselves are affine. Joint surjectivity is exactly
  `hcover : ∀ x : X, ∃ a, ∃ y, q a y = x`.
- The maps `c a : Spec (E a) ⟶ C` and `n a : Spec (T a) ⟶ N`
  are the chart projections. `hC` and `hN` are `IsPullback` statements with
  `ν,q a` and `i,q a`, whose other projections are `Spec.map` of the
  respective algebra maps. Thus these are the specified affine inverse
  images, with their maps, not arbitrary affine schemes isomorphic as
  abstract objects. Supplying these maps and pullback witnesses is exactly
  the data of choosing affine presentations of those inverse images.
- `hB` is `IsPullback (Spec.map α) (Spec.map β)` over the displayed maps
  `Spec E → Spec P` and `Spec T → Spec P`. By the fibre-product universal
  property, their source `Spec D` is the inverse image of the actual B.
  This is the canonical projection-compatible identification. There is
  no independently chosen or unspecified map from B.
- The map `P a → E a × T a` is explicitly
  `p ↦ (algebraMap (P a) (E a) p, algebraMap (P a) (T a) p)`.
  `hinj` gives exactness at the first P term, including the initial zero.
  `hexact` is `Function.Exact` of that map and
  `z ↦ α a z.1 - β a z.2`, exactly kernel = image at the middle term.
  Finite direct sum and direct product of these two modules have the
  same underlying module, hence `E a × T a` renders the displayed `⊕`.
  The algebra homomorphisms make both underlying additive maps P-linear.
  `hsurj` is surjectivity of that difference map, giving exactness at D
  and the final zero. `hα` separately states surjectivity of α, as in
  the node, even though it also implies the difference-map surjectivity.

Conclusions, clause by clause:

- The first conjunct is
  `IsPushout (pullback.fst ν i) (pullback.snd ν i) ν i` in `Scheme.{u}`.
  Mathlib's `IsPushout` is the colimit universal property, including
  compatible maps into every scheme Z and their unique extension.
  It is not merely the property for affine target schemes.
- The second conjunct quantifies over every `V : X.Opens`. It uses the
  actual inclusion `V.ι`, the two inverse images `pullback ν V.ι` and
  `pullback i V.ι`, their maps `pullback.snd`, and their fibre product
  over V. This is precisely the inverse-image square. Its top-left
  corner canonically identifies with `B ×[X] V` by the pullback universal
  property; using the iterated pullback requires no extra hypothesis.
- The third conjunct repeats this square over every `X' : Scheme.{u}`
  and `f : X' ⟶ X` subject only to `Flat f`. Neither affineness,
  quasi-compactness, separatedness nor quasi-separatedness is imposed
  on the new base. The same canonical iterated pullback identifies
  the top-left corner with `B ×[X] X'`.
- The fourth conjunct quantifies over each chart and every commutative
  algebra `H : Type (max u w)` with `Module.Flat (P a) H`. Using
  `max u w` keeps larger test algebras and avoids a potentially vacuous
  small test universe. With `w = u` it includes all algebras in the
  chart universe. The target of `pinchingTensorComparison` is exactly
  Mathlib's explicit `CommRingCat.pullbackCone` point for the maps
  `id_H ⊗ α` and `id_H ⊗ β`. Its underlying ring consists of the
  matching pairs in `(H ⊗[P] E) × (H ⊗[P] T)`, with componentwise
  operations. Its construction pairs the two `includeLeftRingHom`
  maps and restricts their codomain to this equalizer subring. Therefore
  the comparison is exactly `h ↦ (h ⊗ 1, h ⊗ 1)`. The small `simp`
  proof verifies membership; there is no deferred data or arbitrary
  choice. `Function.Bijective` of this specified ring homomorphism
  says it is a ring isomorphism, and retains its canonical normalization.

Dependency declarations used and sources opened:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map` (`def-pc-scheme`,
  `def-weil-affine-spectrum`). These give the ambient category and charts.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (`def-weil-finite-integral-morphism`); the integral alternative of that
  definition is not an additional hypothesis of this item.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (`def-weil-closed-immersion`).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  and their universal property (`def-pc-fibre-product`), provided by
  `Mathlib.AlgebraicGeometry.Pullbacks` together with the scheme instances.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (`def-weil-etale-morphism`).
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `IsColimit`
  (`def-weil-pbc-category-colimit`); the specialized square form used here
  is `CategoryTheory.IsPushout`, available through the pullback imports.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` and the actual open subschemes
  (`def-weil-open-immersion`); `V.ι` supplies the inclusion.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (`def-weil-flat-morphism`), together with its base-change instances and
  affine criterion, as recorded for the proof dependencies.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`
  (`def-weil-pbc-module-tensor-product`), available through the public
  tensor-map import. Algebra tensor products use the same module tensor
  construction, equipped with its canonical commutative-ring structure.
- The helper uses `Algebra.TensorProduct.map`, `includeLeftRingHom`,
  `RingHom.eqLocus`, `RingHom.codRestrict`, and the explicit
  `CommRingCat.pullbackCone` from
  `Mathlib.Algebra.Category.Ring.Constructions`.

All already stated proof dependencies have their corresponding imports:
flat tensor exactness (`Mathlib.RingTheory.Flat.Basic`), tensor right
exactness (`Mathlib.LinearAlgebra.TensorProduct.RightExactness`), tensor
product/product distribution (`Mathlib.RingTheory.TensorProduct.Pi`),
affine fibre products (`Mathlib.AlgebraicGeometry.Pullbacks`),
`AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`
(`Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout`), flat ring-map
composition (`Mathlib.RingTheory.RingHom.Flat`), flat scheme-map base change
and affine criterion (`Mathlib.AlgebraicGeometry.Morphisms.Flat`), affine
opens basis (`Mathlib.AlgebraicGeometry.AffineScheme`), scheme-morphism
gluing (`Mathlib.AlgebraicGeometry.Gluing`), small étale site and its fpqc
comparison (`Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` and its public
étale-site import), and fpqc covering axioms/representable descent
(`Mathlib.AlgebraicGeometry.Sites.Fpqc`). The affine pinching theorem's
full signature and proof docstring were read before writing this statement.

Edge cases checked mathematically before writing:

- Zero rings have `CommRing` instances and are admitted in every chart
  and tensor factor; no `Nontrivial` hypothesis occurs.
- An empty index type is admitted. `hcover` then forces X to be empty;
  schemes with maps to X are empty, so all pushout assertions hold.
- Empty charts are allowed within a nonempty family. The coverage
  condition requires only their union to cover X, not each chart to
  have a point.
- `V = ⊥` gives the empty inverse-image square, which is a pushout.
  `V = ⊤` retains the full square.
- Identity flat base change recovers the original assertion; an empty
  new base is allowed. No conditions exclude non-affine new bases.
- The flat zero P-algebra H is allowed; its tensor factors and matching
  ring are zero, so the comparison is bijective. No flatness of E, T,
  or D over P is assumed or used in the proof plan.
- `Type v` allows arbitrary cover cardinality independently of the
  universe of the schemes, and `Type (max u w)` retains large H.

Searches for an existing exact statement and canonical helper:

- `msearch.py` LeanFinder: "Etale local affine pinching exact difference
  sequence gives pushouts of schemes stable under flat base change".
  Eight hits, including étale/flat base-change stability and pullbacks
  in the small étale category; none states this pushout descent theorem.
- `msearch.py` Loogle: `"IsPushout", "AlgebraicGeometry"`.
  Two hits: `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` and
  `AlgebraicGeometry.isPushout_appTop_of_isPullback`. These give scheme
  pullbacks from ring pushouts or ring pushouts from scheme pullbacks;
  neither is a scheme pushout assertion for closed pinching.
- `msearch.py` LeanSearch: "An affine etale local exact pinching square
  of schemes is a pushout preserved by flat base change". Eight hits:
  a general `Square.IsPushout` predicate, local morphism properties,
  flatness and its stability; no exact theorem or canonical helper.
- `msearch.py` grep: `pinching|[Pp]ushout`, subdirectory
  `AlgebraicGeometry`. It found gluing along open immersions and the
  affine fibre-product API, not the asserted closed-pinching descent.
- Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf`, by pinching,
  descent and the item id: the affine closed-pinching theorem is already
  present and reused as a proof dependency. `PinchingLineData` concerns
  Zariski-local matching-pair hypotheses and invertible-sheaf patching;
  it neither defines this tensor comparison nor states this theorem.
- Direct name search in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` found neither newly declared name.
  The withdrawn `CompactObject.lean` example has no declarations left;
  its node now records the upstream definition, so its obsolete module
  was not used as a source of declarations.

Validation: the required `scompile.py` compiled the module both under its
sandbox name and its final library name, cleanly, in 7.1 and 7.9 seconds.
There are no auto-bound implicit variables (`autoImplicit false`), no
file-local notation or instance, and no line longer than 100 characters.
No statement correction, dependency repair, or disputed statement was needed.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
