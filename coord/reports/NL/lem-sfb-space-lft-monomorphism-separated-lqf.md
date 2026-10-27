## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLftMonomorphismSeparatedLqf` states
`AlgebraicGeometry.AlgebraicSpace.separated_and_chartwise_isLocallyQuasiFinite_of_lft_monomorphism`.
It has one theorem, with `sorry` as its entire proof; no definitions or helper theorems
are added. Only the assigned node's `lean` field is changed. There is no statement
correction, disputed statement, new node, or dependency repair.

The full correspondence with the node is as follows.

- The base scheme is `{S : Scheme.{u}}`. The scheme `T` with its given map to `S`
  is bundled as `(T : Over S)`. This permits every base and every target, including
  empty schemes, with no separatedness or finiteness assumption on either.
- The explicit universe `u` is arbitrary. `Scheme.{u}`, the category `Over S`, and
  `Type u`-valued functors have exactly the universes of the recorded algebraic-space
  interface. `def-weil-size-convention` is a metatheoretic convention and has no
  declaration to import. Scheme tests use the same scheme universe, not a separate
  smaller universe that could make the hypothesis vacuous.
- `(X : AlgebraicSpace S)` is the dependency's full subcategory of fppf sheaves with
  representable diagonal and representable surjective étale scheme atlas. `X.obj.obj`
  is its underlying presheaf. No schematicity or chosen presentation is assumed.
- `(f : X.obj.obj ⟶ yoneda.obj T)` is precisely a natural transformation of functors
  on schemes over `S`, hence the specified `S`-morphism. Yoneda has
  `(yoneda.obj T).obj (op H) = (H ⟶ T)`, the morphisms over `S`, as required by `h_T`.
  A transformation between these sheaf presheaves is exactly a sheaf morphism;
  no sheaf structure is discarded by expressing the map in the full presheaf category.
- `hmono : ∀ H : Over S, Function.Injective (f.app (op H))` is the stipulated
  injectivity on `X(H) → h_T(H)` for every `S`-scheme, without a surjectivity condition.
- `hft` quantifies over every `(V : Over S)` and every natural transformation
  `e : yoneda.obj V ⟶ X.obj.obj`. `IsEtale e` is the recorded representable étale
  condition; it includes representability. These are all such charts, and they
  need not themselves be surjective, affine, finite, or quasi-compact.
- `yoneda.preimage (e ≫ f) : V ⟶ T` is the canonical scheme morphism corresponding
  to the composite `h_V → X → h_T`, using full faithfulness of Yoneda. Its `.left`
  is the underlying scheme morphism. `LocallyOfFiniteType` on precisely this map
  renders the local-finite-type assumption, with no finite-presentation replacement.
- The first conclusion is
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f)`.
  Here `pullback.diagonal f : X.obj.obj ⟶ pullback f f` is the actual relative
  diagonal, not the absolute diagonal. By the dependency's definition, for every
  scheme `W` over `S` and every `h_W → pullback f f`, its pullback is represented
  by a scheme `U` over `S` with projection `p : U ⟶ W` whose `.left` is a closed
  immersion. This is exactly the node's meaning of separatedness, including
  representability of each base change.
- The second conclusion quantifies again over every scheme `V` and every
  representable étale chart `e`. It asserts
  `Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (e ≫ f)).left`.
  The recorded Stacks predicate means quasi-finite at every point, including the
  finite-type affine-neighbourhood condition; it is not Mathlib's weaker
  `LocallyQuasiFinite` predicate alone. The conjunction supplies exactly the two
  conclusions of the node, without quasi-compactness or global quasi-finiteness.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-size-convention`: its recorded convention, implemented by explicit
  universe polymorphism; no module/declaration exists or is needed.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and `AlgebraicSpace.IsRepresentableWith`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  declaration `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  declaration `AlgebraicGeometry.IsClosedImmersion`.
- `pqf-def-quasifinite`: `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`,
  declarations `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and its defining
  `IsQuasiFiniteAtPoint`.

All recorded proof dependencies with declarations are also imported, using plain
imports when needed only by the proof. `def-weil-etale-morphism` is Mathlib's
`AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
`def-weil-pbc-formally-unramified-morphism` and the two Mathlib-matched implication
nodes use `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`, notably
`AlgebraicGeometry.FormallyUnramified`, its open-diagonal instance,
`FormallyUnramified.hom_ext`, `FormallyUnramified.of_hom_ext`, and
`FormallyUnramified.isOpenImmersion_diagonal` (the local version has an unnamed
first instance). `lem-weil-pbc-unramified-quasi-finite-at-points` is
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified` in
`WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`.
The scheme and space definitions shared with the proof are already public imports.
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` supplies the relative
presheaf diagonal API. The theorem docstring includes all four DAG proof steps,
including the maps and base used in infinitesimal uniqueness.

Source checked: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-monomorphism-loc-finite-type-loc-quasi-finite` (Tag 0463), lines 5360–5391.
It states the general algebraic-space-target result; the assigned node is its
scheme-target specialization. The dependency's Stacks 01TD predicate was read in
full to retain local finite type. The prescribed CompactObject example is now
withdrawn; its recorded upstream replacement
`WeilConjectures.CategoryTheory.CompactObject` was read for the current module
header and docstring conventions. No missing or unusable interface was found.

Edge cases checked before writing: empty source and empty chart; empty target
(which forces the corresponding sections/source to be empty); identity maps;
non-surjective monomorphisms such as open immersions; non-affine targets;
non-quasi-compact and disconnected charts. The quantifiers and conjunction impose
no nonemptiness, quasi-compactness, finite type, or finite-fibre cardinality bounds.
For a monomorphism the diagonal is an isomorphism, so the first clause holds even
without the finite-type assumption; local finite type is needed for the second.
Étale charts of a monomorphism have unique infinitesimal lifts by the argument
recorded in the node, so the chart conclusion does not erroneously require that
the chart itself be monic.

Searches (2026-10-24):

- `msearch.py ... leanfinder`, query `A locally finite type monomorphism of algebraic
  spaces into a scheme is separated and chartwise locally quasi-finite`: 8 hits,
  including `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib `LocallyQuasiFinite`,
  and scheme immersion/finite-morphism instances; no algebraic-space theorem.
- `msearch.py ... loogle`, query
  `AlgebraicGeometry.LocallyOfFiniteType, CategoryTheory.Mono`: 0 hits.
- `msearch.py ... grep`, query
  `monomorphism.*quasi.finite|isSeparated_of_mono|AlgebraicSpace`, restricted to
  Mathlib `AlgebraicGeometry`: 1 hit,
  `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:61`, the scheme-only
  `IsSeparated.isSeparated_of_mono`. It does not state this result.
- `msearch.py ... leansearch`, query `A locally finite type monomorphism of algebraic
  spaces is separated and locally quasi-finite`: 8 hits, including that same
  scheme-only separatedness instance, scheme finite-type/quasi-finite constructors,
  and scheme quasi-separatedness instances. None handles a space source.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf`, query
  `lft_monomorphism|monomorphism.*quasi.finite|mono.*locallyQuasiFinite|mono.*isLocallyQuasiFinite`:
  only `AffineEtaleRelationSeparatedQuasiFinite.lean:36`, a specialized theorem
  for a relation of schemes; its full signature was read, and it is not this node.
- `grep -rn lem-sfb-space-lft-monomorphism-separated-lqf lean/WeilConjectures`:
  no hits. The corresponding project search finds a proof-plan reference in
  `EtaleSheafSpaceAtlasBootstrap.lean`, not an existing declaration of this theorem.
- Broader searches of `IsRepresentableWith` and space separatedness in the project
  found existing interfaces and neighboring statements, including
  `SpaceSeparatedLqfPermanence` and `SeparatedEtaleSpaceScheme`; these were read
  to confirm the same relative-diagonal and chart conventions. No second
  definition of a notion is needed.

Validation: `scompile.py NL lem-sfb-space-lft-monomorphism-separated-lqf` compiled
this module in both sandbox and library modes on the server, within 2 seconds
per file, with no errors or unexpected warnings. Auto-bound implicits are disabled;
all variables and the universe are explicitly bound. Delivery preflight is run
with the prescribed `deliver2.py --no-push` before pushing.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
