## Worker report

The item module is `lean/Sheaf/AlgebraicGeometry/Picard/ArrowIsoTensorPullbackCounit.lean`.
Its declaration is `AlgebraicGeometry.nonempty_arrowIso_tensorPullback_directImageCounit`.
It states the arrow isomorphism, with `sorry` as its only proof. The item's natural-language
statement is unchanged. Its `stmt_deps` gains the already landed definition
`def-pc-module-pullback` and adjunction node `lem-pc-module-pullback-adjunction`, used explicitly
in the signature. There are no new nodes and no statement correction.

Each hypothesis and clause is rendered as follows:

- A field `k`: `{k : Type u} [Field k]`, with explicitly declared `universe u`.
- A scheme over `k`: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`, with structure map
  `X ↘ Spec (.of k)`.
- Smooth projective curve: `[(X ↘ Spec (.of k)).IsSmoothProjectiveCurve]`. This is the recorded
  class, incorporating the integral, separated, finite-type, dimension-one curve convention,
  smoothness, and projectivity. No properness or relative-dimension hypothesis is added.
- Geometrically integral structure morphism:
  `[GeometricallyIntegral (X ↘ Spec (.of k))]`.
- Rational point: `(σ : Spec (.of k) ⟶ X)` and
  `(hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))`. This is exactly a section; no
  separable-closedness assumption on `k` is imposed. The recorded `baseChangeFieldPoint`
  constructs induced sections for field extensions, and is not the definition of a general
  section or of an arbitrary scheme base change. Here the section and its equation are
  explicit binders, as accepted by `picardFunctorNormalized`.
- Injective resolutions on every `X_T`: the instance binder
  `[∀ T : Over (Spec (.of k)), HasInjectiveResolutions
    (pullback (X ↘ Spec (.of k)) T.hom).Modules]`. Its category has the standard Abelian
  structure; `HasInjectiveResolutions` means every object admits an `InjectiveResolution`.
- Schemes `T,T'` and a morphism over `k`: `{T T' : Over (Spec (.of k))} (i : T' ⟶ T)`.
- `ℒ ∈ F(T)`: `(ℒ : picardInvertibleDirectImageClasses (X ↘ Spec (.of k)) σ hσ T)`.
  The subtype contains a normalized Picard class `ℒ.1`, with derived-image condition `ℒ.2`.
  It contains no chosen trivialization or chosen derived-image isomorphism.
- The module represented by the class: `M := (fromSkeleton _).obj ℒ.1.1.val`.
- The induced base-change map: `iX := baseChangeMap (X ↘ Spec (.of k)) i`.
- Structure maps on the two base changes: `fT` and `fT'` are the corresponding `pullback.snd`.
- Both counits are the `.counit.app` components of
  `Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction fT)` and the analogous
  adjunction for `fT'`. This pins them to the canonical tensor-pullback adjunction, as the
  stage-2 conventions require.
- Pullback of the first counit: `(Scheme.Modules.tensorPullback iX).map (adjT.counit.app M)`.
- Counit of the pulled-back module:
  `adjT'.counit.app ((Scheme.Modules.tensorPullback iX).obj M)`.
- Isomorphic as arrows: `Nonempty (Arrow.mk (...) ≅ Arrow.mk (...))`. This asserts existence
  of an arrow isomorphism, exactly the node's conclusion, without additional constraints
  on a chosen isomorphism. Using the actual pulled-back module is equivalent to using a
  chosen representative of its Picard class, by naturality of the counit under module
  isomorphisms; it avoids relying on the source's older `Pic.map` pullback implementation.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`:
  `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve` (also read its `IsCurveOverField`
  and `IsProjective` parents).
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, `CategoryTheory.HasInjectiveResolutions`.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`:
  `AlgebraicGeometry.picardFunctorNormalized`; also read `picardFunctor` (the fppf-sheafified
  functor, not the normalized kernel whose elements are used here).
- `WeilConjectures.AlgebraicGeometry.DensePoints`:
  `Scheme.Hom.baseChangeFieldPoint`, read as recorded for the rational-point dependency;
  the theorem uses explicit general section data instead of restricting to field extensions.
- `WeilConjectures.AlgebraicGeometry.Picard.Representability`:
  `AlgebraicGeometry.IsInvertibleDirectImage`, and the old
  `AlgebraicGeometry.picardFunctorInvertibleDirectImage` (read, with record repaired below).
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`.
- Dependency module of this delivery:
  `Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses`,
  `AlgebraicGeometry.picardInvertibleDirectImageClasses`.

Edge cases checked before writing: the curve itself cannot be empty because it is integral
of dimension one, but `T` and `T'` can be empty. The formula still makes sense in their module
categories; no `Nonempty T.left` is imposed. Identity maps give the same counit up to identity
pullback, and arbitrary nonflat base-change maps are allowed. Fields in every characteristic
are allowed, with no algebraic or separable closedness. `u` is arbitrary, and all schemes and
module categories use the same universe as the recorded Picard definitions: there is no
smaller independent test-scheme universe that could make the resolution hypothesis vacuous.
The subtype excludes the zero module on a nonempty scheme through invertibility, while the
empty-scheme case is retained. The conclusion uses the actual pulled-back module and thus
needs no additional injective-resolution binder for `T` itself.

Searches made (2026-10-11):

- `msearch.py ... leanfinder` query "pullback of direct image adjunction counit is isomorphic
  as an arrow to counit after base change": eight results, all generic `Over` counit and
  composition lemmas; none is this Picard tensor-pullback statement.
- `msearch.py ... loogle` query
  `CategoryTheory.Arrow, AlgebraicGeometry.Scheme.Modules.tensorPullback`: zero results,
  unknown identifier for the project's tensor pullback.
- `msearch.py ... grep` query `arrowIso.*[Cc]ounit|[Cc]ounit.*[Bb]ase[Cc]hange`, in
  `AlgebraicGeometry`: zero Mathlib matches.
- `msearch.py ... leansearch` query
  "base change direct image counit tensor pullback module sheaves": service unavailable,
  Internal Server Error. This is recorded as unavailable, not as absence of a match.
- `rg` of the same counit pattern in `WeilConjectures` found
  `AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit` in `Picard/ZeroScheme.lean`.
  Read its full binders, docstring, and `Pic.directImageCounit`. It assumes smooth relative
  dimension one and properness, and its counit and arrow use `Modules.pullback`, whereas
  this project's explicit convention requires the recorded `Modules.tensorPullback`.
  It is not a declaration of the exact statement with the mandated definitions.
- `grep -rn 'lem-pc-arrow-iso-pullback-counit' WeilConjectures`: zero matches.
- `rg` in `lean/Sheaf` for the counit pattern: zero matches. Tensor-pullback searches find
  and reuse the landed `TensorPullback` and `TensorPullbackAdjunction` modules.
- `rg` for both proposed declaration names in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: zero matches.
- `rg` of `picard.*[Cc]lasses|InvertibleDirectImage.*(obj|Set)|def.*[Ff]unctor.*[Ii]nvertible`
  in the source and `lean/Sheaf`: only the source's stronger bundled subfunctor record;
  no independent pointwise assignment declaration.

No STATEMENT-DISPUTED fault. The item retains the source's mathematical counit comparison;
implementation differences and the dependency-record issue are described explicitly here.
The two modules compile together cleanly on the server (2.5 seconds, no warnings).

## Dependency modules

`def-pc-f-subfunctor`: the old `picardFunctorInvertibleDirectImage` requires `[IsProper f]`
to construct the bundled stable `Subfunctor`. The dependency node expressly defines only
`T ↦ F(T)` and leaves stability to a separate theorem. The recorded smooth-projective-curve
class contains projectivity but supplies no `IsProper` instance, so directly using the old
record would introduce a further hypothesis just to type the statement. The dependency
module `Picard/InvertibleDirectImageClasses.lean` defines precisely the pointwise subset of
`(picardFunctorNormalized f σ hσ).toFunctor.obj (op T)` using the existing predicate
`IsInvertibleDirectImage f T L.1`. There is no new direct-image condition, normalized Picard
functor, trivialization data, or stability proof. Its field, scheme, smooth-projective curve,
section, resolution, and test-scheme binders match the dependency's objects; its sole clause
is membership in the already recorded derived-image predicate. The node copy changes only
`lean`, including the required explanatory `note`.

The source was read directly at
[Stacks Project, Lemma 44.6.2 (Tag 0B9V)](https://stacks.math.columbia.edu/tag/0B9V),
which starts with exactly this pointwise subset before asserting stability and openness.
The local Stacks files are not present on this machine. This is a dependency-record repair
under brief-stage2 §1(B), not a new definition node: the notion already has its DAG node.

## Second reading by E1

I independently read the item node, its two delivered Lean modules, all statement-dependency
node records, and the declarations underlying the curve, normalization, direct-image
condition, base-change map, tensor pullback and canonical adjunction. No mathematical
mismatch was found; the Lean and node signatures are retained. This reading adds only this
review report and independent search evidence.

The checklist extracted from the node, matched clause by clause:

| Node object, hypothesis or conclusion | Lean rendering | Verdict |
| --- | --- | --- |
| Field k | `{k : Type u} [Field k]` | Exact; no closedness or characteristic restriction. |
| Scheme X over k | `{X : Scheme.{u}} [X.Over (Spec (.of k))]` | Exact; structure map is `X ↘ Spec (.of k)`. |
| Smooth projective curve | `[(X ↘ Spec (.of k)).IsSmoothProjectiveCurve]` | Exact recorded class, not the weaker upstream `IsCurve`. |
| Geometrically integral structure morphism | `[GeometricallyIntegral (X ↘ Spec (.of k))]` | Exact integral clause of the recorded geometrical-properties node. |
| Rational point sigma | `(σ : Spec (.of k) ⟶ X)` with `hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 _` | Exact section; its equation is essential, not a bare morphism. |
| Injective resolutions on every X_T | `[∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]` | Exact universal assumption; the category is modules on X_T, not on T. |
| Arbitrary k-schemes T and T' and morphism i | `{T T' : Over (Spec (.of k))} (i : T' ⟶ T)` | Exact; Over enforces commutation with structure maps; i need not be flat. |
| Class L in F(T), inside normalized Picard classes | `(ℒ : picardInvertibleDirectImageClasses (X ↘ Spec (.of k)) σ hσ T)` | Exact nested subtype, no chosen trivialization or derived-image isomorphism. |
| Module represented by that class | `M := (fromSkeleton _).obj ℒ.1.1.val` | Correct representative of its isomorphism class. |
| Induced map i_X and f_T, f_T' | `baseChangeMap (X ↘ Spec (.of k)) i` and the two `pullback.snd` | Correct fibre products and projection directions. |
| Counit f_T^* f_T,* L to L | `adjT.counit.app M` where `adjT := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction fT)` | Correct canonical tensor-pullback/pushforward counit. |
| Pull that arrow back along i_X | `(Scheme.Modules.tensorPullback iX).map (adjT.counit.app M)` | Correct map of the whole arrow, including its source and target. |
| Counit on the pulled-back object | `adjT'.counit.app ((Scheme.Modules.tensorPullback iX).obj M)` | Correct actual module i_X^* L; choosing the Picard representative instead changes the arrow by naturality under an isomorphism. |
| Existence of an isomorphism of these arrows | `Nonempty (Arrow.mk (...) ≅ Arrow.mk (...))` | Exact existential arrow isomorphism, with no additional coherence clause omitted or added. |

The source place of the item is ZeroScheme.lean:156-175, not a Stacks statement.
I read the surrounding section variables at lines 102-105: the source assumes a field,
`X.Over`, smooth relative dimension one, properness and geometrical integrality, and the
explicit theorem assumes the section and resolutions. The node expresses the curve using
its own recorded smooth-projective-curve convention. Reading SmoothProjectiveCurve.lean,
Variety.lean and Morphisms/Projective.lean confirms integral, separated, finite type,
dimension exactly one, smooth and projective; no hidden genus or separably closed field
binder occurs in this statement. The theorem docstring faithfully records both proof
steps of the node: derived base change gives the canonical direct-image comparison
isomorphism, and the composition isomorphism and adjunction triangle give the arrow square.

Dependency-module reading (H13): `def-pc-f-subfunctor` defines only the assignment F(T),
not its stability. I read the Stacks source `pic.tex`, `lemma-check-conditions` and
`lemma-define-open`, including the preceding paragraph identifying normalized Picard
classes with invertible modules trivial along sigma_T. The source assumes a field and a
smooth projective curve with a rational point; it does not assume a separably closed field.
The delivered `picardInvertibleDirectImageClasses` uses exactly the recorded
`picardFunctorNormalized` object and `IsInvertibleDirectImage f T L.1`. The latter's full
definition in Representability.lean:99-110 asks for invertibility of the zeroth right
 derived pushforward and zero positive right derived pushforwards. For a module in degree
zero, these are exactly the stated derived-image condition: negative cohomology vanishes,
and a complex with just its zeroth cohomology is isomorphic to that module in degree zero.
There is no duplicate condition or additional trivialization. The old dependency record
at Representability.lean:185-194 constructs a stable bundled Subfunctor and requires
`[IsProper f]`; the delivered pointwise definition avoids requiring this additional
instance, which the recorded projectivity class does not automatically supply. Its
explanatory `lean.note` is accurate. There are no new nodes or statement corrections.
The Stacks source was read at
https://raw.githubusercontent.com/stacks/stacks-project/master/pic.tex and checked against
https://stacks.math.columbia.edu/tag/0B9V because local .tex files are absent.

I also read the actual `InjectiveResolution` and `HasInjectiveResolutions` signatures,
Mathlib's `GeometricallyIntegral`, the recorded rational-point `baseChangeFieldPoint`,
`sectionBaseChange` and `baseChangeMap`, and the tensor-pullback and adjunction modules.
The rational-point record specializes induced sections to field extensions; the present
statement needs only the explicit general section and uses the normalized Picard
signature directly, so no missing specialized declaration is needed. The adjunction
existence theorem pins its unit to the canonical sectionwise tensor formula; choosing
this witness pins the counit accordingly. The modules use standard module categories
and Abelian instances, not chosen alternative instances.

Edge cases: arbitrary nonflat i is permitted. T or T' may be empty and zero objects
remain available in their module categories; the curve X itself is excluded from being
empty by the node's integral dimension-one condition. There is no index-set binder or
integer n in this item. The degree-zero part of the dependency predicate is separate
from its `∀ q : ℕ, 0 < q` clause, so q = 0 is not accidentally killed. No characteristic
or genus restriction occurs. Every universe is explicitly bound by u (v in the dependency),
and test schemes use the same universe as the field and X, consistently with recorded
Picard definitions; increasing this universe covers larger schemes. No independent
smaller test universe makes the universal hypothesis vacuous.

Independent searches, using different wording from the first worker:

- LeanFinder: `cohomology base change compatibility of evaluation morphisms of line bundles`.
  Eight hits, generic section/evaluation and group-cohomology identities; no exact match.
- Loogle: `CategoryTheory.Arrow, CategoryTheory.Adjunction.counit`.
  Two generic Leibniz-adjunction component identities; neither concerns this family or F(T).
- LeanSearch: `invertible pushforward line bundle evaluation map base change isomorphism`.
  Service unavailable (Internal Server Error); recorded as unavailable, not absence.
- Direct rg over Mathlib/AlgebraicGeometry, source WeilConjectures/AlgebraicGeometry and
  repository lean/Sheaf with `counit.*([Bb]ase[Cc]hange|[Pp]ullback)` and its reversed pattern,
  and `picard.*[Cc]lasses`. Mathlib has generic pullback adjunctions; the project has closed
  immersion counit results. Neither states this comparison. The source ZeroScheme theorem
  and `Pic.directImageCounit` use the older `Modules.pullback`, not the mandated
  `tensorPullback`; they cannot be recorded as an exact existing statement here.
- Exact names of both delivered declarations were searched across Mathlib, upstream
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json; neither already exists.
  Reading Representability.lean confirms its bundled F is the only related pointwise
  assignment, and it needs the unusable extra instance discussed above.

H5/H6/H8/H9: the dependency definition has genuine data and no sorry; the item's only
proof is `by sorry`; both modules and both declarations have their own source and blueprint
docstrings. The theorem docstring contains the entire two-step proof. No unbound variables,
new axioms or declaration-name collisions were found. Both node `lean.statement` fields
retain the exact declaration signatures. Both delivery modules compiled together on the
server in dependency order in 2.3 seconds, exit code 0, with no errors or warnings.
