## Worker report

The main module is `Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange`, declaration
`AlgebraicGeometry.nonempty_arrowIso_moduleBaseChange_counit`. It states only the requested
arrow isomorphism; its proof is `sorry`. No definition has sorried data. The item's statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the already
landed `lem-pc-module-pullback-adjunction`, which supplies the canonical adjunction used.

Hypotheses and clauses matched individually:

- The separably closed field is `{k : Type u} [Field k] [IsSepClosed k]`.
- The curve over this field is `{X : Scheme.{u}}` with the explicit structure morphism
  `f : X ⟶ Spec (.of k)` and `[f.IsSmoothProjectiveCurve]`. This is the recorded curve
  definition, including integrality, separation, finite type, dimension exactly one,
  smoothness and projectivity. No properness or geometric-integrality hypothesis is added.
- The rational point is `σ : Spec (.of k) ⟶ X` with
  `hσ : σ ≫ f = 𝟙 (Spec (.of k))`, exactly a section.
- Injective resolutions on every base change are
  `[∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules]`.
- The two arbitrary k-schemes and their k-morphism are
  `{T T' : Over (Spec (.of k))} (i : T' ⟶ T)`.
- Membership `ℒ ∈ F(T)` is the subtype binder
  `(ℒ : picardInvertibleDirectImageClasses f σ hσ T)` in the dependency module below.
  Its underlying normalized class is `ℒ.1`, and the underlying Picard class is `ℒ.1.1`.
  The stored membership proof is exactly `IsInvertibleDirectImage f T ℒ.1.1`:
  invertible R⁰ image and zero positive derived images. Thus the degree-zero derived-image
  clause is present, not an additional premise and not merely invertibility of f_*ℒ.
- `X_T` and `X_{T'}` are `pullback f T.hom` and `pullback f T'.hom`, and the two structure
  maps are `pullback.snd f T.hom` and `pullback.snd f T'.hom`.
- `i'` is the existing `baseChangeMap f i`. The recorded
  `Scheme.Modules.moduleBaseChange f i` is precisely `tensorPullback (baseChangeMap f i)`.
- The sheaf representing the class is `L := (fromSkeleton _).obj ℒ.1.1.val`.
  Its actual tensor pullback is `L' := (moduleBaseChange f i).obj L`; no new choice of a
  Picard representative is substituted for this module.
- The adjunction arrow `f_T^* f_{T,*} L ⟶ L` is `adj.counit.app L`, where `adj` is
  `Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f T.hom))`.
  Its source is tensor pullback of pushforward, by the type of that adjunction.
- Its pullback arrow is `(moduleBaseChange f i).map (adj.counit.app L)`.
- The second arrow is `adj'.counit.app L'` for the identical canonical adjunction construction
  over `T'`. The conclusion `Nonempty (Arrow.mk (...) ≅ Arrow.mk (...))` expresses existence
  of an isomorphism of arrows, including isomorphisms on both sources and targets making
  the counit square commute. It asserts the node's existence claim, without specifying
  extra identity requirements for the target component.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (all separable polynomials split).
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`:
  `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`:
  `Scheme.Hom.baseChangeFieldPoint` was read; its input rational point is a section.
  Our section binders express that notion directly, without introducing a second definition.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `InjectiveResolution` and `HasInjectiveResolutions` (resolution existence for every object).
- `WeilConjectures.AlgebraicGeometry.Picard.Representability`:
  `picardFunctorInvertibleDirectImage`, `isOpenImmersion_picardFunctorInvertibleDirectImage_ι`
  and `IsInvertibleDirectImage` were read; the objectwise condition is reused in the dependency
  module. The open-immersion theorem is not needed to state the arrow isomorphism.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage`:
  `Scheme.Modules.IsFiniteLocallyFreeInDegree` and
  `isFiniteLocallyFreeInDegree_zero_one_iff` were read. They identify the existing
  `IsInvertibleDirectImage` condition with rank one in degree zero. No new cohomology notion.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` was read; no separate invertible-module hypothesis is added
  because the input Picard class and F-membership already encode the necessary invertibility.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`:
  `Scheme.Modules.moduleBaseChange`, using the existing `baseChangeMap` from
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`.
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`, fixing the canonical sectionwise unit.

Edge cases checked before writing: T or T' may be empty; there is no Nonempty base assumption,
so invertibility of the zero sheaf on the empty scheme is allowed. The curve X itself is
nonempty by integrality/dimension one, as in the node. All characteristics are allowed;
separably closed is not strengthened to algebraically closed. Identity i and arbitrary,
including nonflat, base morphisms are allowed. No genus or positivity hypothesis is imposed.
Every universe and variable is explicitly bound. There is one scheme/ring universe u, so
quantification over base schemes includes Spec k and all k-schemes in that universe.

Searches (2026-10-11):

- `msearch.py ... leanfinder` with “base change of the adjunction counit for pushforward of an
  invertible module with derived direct image invertible in degree zero”: eight generic
  sheaf adjunction hits, none the requested geometric statement.
- `msearch.py ... loogle 'CategoryTheory.Arrow, CategoryTheory.Adjunction.counit'`: two
  Leibniz-adjunction counit component hits, no match.
- `msearch.py ... grep 'arrowIso.*pullback.*[Cc]ounit|[Cc]ounit.*base[Cc]hange'`: no Mathlib hits.
- `msearch.py ... leansearch` with “adjunction counit commutes with base change for invertible
  derived direct image”: service unavailable, Internal Server Error.
- `rg` of WeilConjectures, Sheaf and the upstream name index found the source
  `nonempty_arrowIso_pullback_directImageCounit` in ZeroScheme.lean:165, read in full with
  its docstring and section hypotheses. It uses the older `Modules.pullback` and
  smooth-relative-dimension-one/proper/geometrically-integral hypotheses, and therefore
  does not directly state this node with the required recorded tensor pullback convention.
  Other hits concern étale sheaves, not O_X-modules. Grepping the node id in source found no
  corresponding declaration tagged with this id.
- `rg` for both proposed new declaration names in Mathlib, WeilConjectures and Sheaf found
  none. Existing F declarations and their signatures were read before writing the dependency.

Both delivered modules were compiled together by scompile.py on the server, cleanly in 2.4 s.
No STATEMENT-DISPUTED finding and no correction to the item's mathematical statement.

## Dependency modules

`def-pc-f-subfunctor` is supplied by
`Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses`, declaration
`AlgebraicGeometry.picardInvertibleDirectImageClasses`. The recorded declaration is a bundled
Subfunctor whose construction already invokes stability and whose signature demands Flat,
IsProper and LocallyOfFinitePresentation instances. The node explicitly asks only for the
objectwise assignment, before stability is proved. Under its exact recorded smooth projective
curve class, IsProper cannot currently be inferred (the recorded projective-proper declaration
is only properness of projective space). Adding a properness binder to the main statement
would change its hypotheses. The replacement records just the subsets, under the existing
curve definition, reusing the existing normalized Picard functor and the existing
IsInvertibleDirectImage predicate; it does not redefine module pullback or cohomology.

For each clause of this dependency: k and X over k are its field, scheme and f binders;
`[f.IsSmoothProjectiveCurve]` is the given curve condition; σ and hσ are the section;
T is an arbitrary object of Over Spec k; the ambient set is exactly the normalized Picard
functor at op T; membership is exactly the existing derived-image predicate on L.1.
The resolution family is the source predicate's prerequisite for forming its right derived
functors. Stability under pullback and the open-immersion conclusion are intentionally not
bundled: the node explicitly reserves them for lem-pc-f-open-subfunctor. The associated
action on normalized classes remains the existing picardFunctorNormalized action. Stacks
Tag 0B9V was opened at https://stacks.math.columbia.edu/tag/0B9V and agrees with this assignment.
Only this dependency's lean record changes; every other field is preserved.

## Second reading by K1

Read the item node, both delivered modules, every statement dependency's node and
recorded declaration, and the source theorem in ZeroScheme.lean:143–175 together with
its section hypotheses at lines 103–109. Also read Representability.lean:99–108,
186–194, Picard/Defs.lean:228–238, DirectImage.lean:521–549, DensePoints.lean:221–234,
the curve/variety/projective classes, BaseChangeConventions and TensorPullbackAdjunction.
The Stacks source was fetched read-only into sandbox scratch `pic.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/pic.tex; read
`lemma-check-conditions`, its following normalized-Picard convention, and
`lemma-define-open` (lines 929–986). Tag 0B9V was also checked at
https://stacks.math.columbia.edu/tag/0B9V. No mathematical mismatch was found.

Object/hypothesis/conclusion checklist, recorded before the verdict:

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| A separably closed field k | `{k : Type u} [Field k] [IsSepClosed k]` | Exact: the recorded polynomial-splitting definition, not algebraic closure. |
| X a smooth projective curve over k | `{X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]` | Exact: opened class extends IsCurveOverField, Smooth f, IsProjective f; the curve class includes integral X, separated/finite-type f and dimension exactly one. |
| A k-rational point σ | `σ : Spec (.of k) ⟶ X`, `hσ : σ ≫ f = 𝟙 _` | Exact section of the structure morphism, as the rational-point dependency defines. |
| Injective resolutions for every base change | `[∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules]` | Exact family, with no restriction to affine or nonempty T. Opened Mathlib's resolution and resolution-existence definitions. |
| Arbitrary k-schemes T, T' and k-morphism i | `{T T' : Over (Spec (.of k))} (i : T' ⟶ T)` | Exact: Over morphisms include the commutativity with the base. |
| ℒ belongs to F(T) | `ℒ : picardInvertibleDirectImageClasses f σ hσ T` | Exact subtype: ℒ.1 is normalized and ℒ.2 is IsInvertibleDirectImage f T ℒ.1.1. |
| Derived image invertible in degree zero | The reused IsInvertibleDirectImage predicate has invertible `(pushforward _).rightDerived 0` and `∀ q : ℕ, 0 < q → IsZero (...)` | Exact for a sheaf in degree zero: no negative cohomology; all positive degrees vanish. DirectImage's zero/rank-one equivalence confirms this characterization. |
| X_T, X_T', f_T, f_T' | `pullback f T.hom`, `pullback f T'.hom`, and their `pullback.snd` maps | Exact scheme fibre products and projections, not merely their points. |
| i' the base change of i | `baseChangeMap f i`, through `Scheme.Modules.moduleBaseChange f i` | Exact: opened moduleBaseChange body is tensorPullback of this map. |
| ℒ as a module and i'^*ℒ | `L := (fromSkeleton _).obj ℒ.1.1.val`; `L' := (moduleBaseChange f i).obj L` | Exact representative and actual tensor pullback; no replacement by an unrelated line bundle. |
| f_T^* f_T,*ℒ → ℒ | `adj.counit.app L`, with adj chosen from exists_tensorPullbackAdjunction of pullback.snd | Exact canonical tensor/direct-image adjunction; opened its pinned unit formula. |
| Pullback of that arrow | `(moduleBaseChange f i).map (adj.counit.app L)` | Exact map on arrows of tensor pullback along i'. |
| Adjunction arrow for the pulled-back module | `adj'.counit.app L'` | Exact counit of the same construction for f_T'. |
| These arrows are isomorphic | `Nonempty (Arrow.mk (...) ≅ Arrow.mk (...))` | Exact existence of an arrow isomorphism; the node does not prescribe either component. |

The source theorem uses smooth relative dimension one, properness and geometric
integrality. These follow mathematically from the item's recorded smooth projective
curve with rational point over a separably closed field; they are not extra hypotheses
to add. Its old Modules.pullback convention is not the recorded tensorPullback, so
that declaration cannot be attached as an exact existing statement. The source selects
a skeleton representative of the pulled-back Picard class, whereas this node explicitly
asks for the counit on the pulled-back module itself. These are isomorphic modules;
the delivered arrow statement directly uses the latter as the node requests.

Dependency-module second reading (H13): def-pc-f-subfunctor explicitly defines only
the objectwise assignment. The supplied Set is a subset of the existing
picardFunctorNormalized at op T; its normalization is precisely the kernel condition
in Picard/Defs.lean and Stacks pic.tex. Its membership is the existing derived-image
predicate, with no private cohomology or invertibility definition. The old bundled
picardFunctorInvertibleDirectImage requires Flat, IsProper and LocallyOfFinitePresentation
instances and already supplies stability. The recorded curve class has no IsProper
instance available merely by unfolding its signature, so the old declaration is unusable
under these exact binders. The replacement assignment does not assert stability or open
representability: these remain the separate dependency lemma. Its field, curve, section,
resolution family and arbitrary T are correct; no separable-closure assumption is added
to this definition. Its node changes only lean, with an explanatory note. No new node
is present, and neither node has a stage-2 statement correction.

Edge cases: empty T and T' are allowed, with the zero module invertible on the empty
scheme; zero modules on a nonempty base cannot satisfy the invertible R⁰ condition.
An empty X is excluded by the node's integral dimension-one curve, not by a new binder.
Identity and nonflat i are allowed. Degree zero is retained rather than suppressed by
the positive-degree quantifier. All characteristics are included. There is no index-set,
genus, or natural-number parameter to restrict. Universe u is arbitrary and is shared
by k, X and test schemes: it includes Spec k and hence has no smaller-test-universe
vacuity. All variables/universes are bound and all quantifiers have the node's order.

Independent searches, using different terms from the worker:

- LeanFinder: `line bundle evaluation morphism compatible with change of base`:
  eight generic section/restriction/evaluation hits, no geometric arrow statement.
- Loogle: `CategoryTheory.Arrow, CategoryTheory.Adjunction`: four Čech/Leibniz
  adjunction hits, no matching statement or F assignment.
- LeanSearch: `Picard classes with invertible zeroth direct image and vanishing higher
  direct images`: Internal Server Error; recorded as unavailable, not as a negative hit.
- Mathlib grep via msearch: `evaluation.*base[Cc]hange|base[Cc]hange.*evaluation|[Cc]ounit.*pullback`:
  generic category/shift adjunctions only. Direct rg of Mathlib, WeilConjectures and
  repository Sheaf for arrow/counit/base-change variants and the new declaration names
  found only the upstream ZeroScheme theorem discussed above. Read that theorem in full.
  Searched the upstream name index as well. The existing F predicate and bundled
  subfunctor were opened and reused/checked, respectively, rather than inferred by name.

H5/H6/H8/H9: the only new theorem has proof sorry; the Set definition contains real
data and no sorry. Both headers and declaration docstrings cite their source and node.
The theorem docstring reproduces the node's single proof step and its two dependencies.
The imports supply notions used by each file; names have no Sheaf prefix and do not
collide. Both lean.statement records match their signatures verbatim. No code or node
repair was necessary; the second reading adds this audit only.

Validation: compiled both delivered modules together, dependency first, with scompile.py;
exit 0, 2.4 seconds, no errors or warnings. The first local invocation used repository-relative
paths and failed before compilation; rerunning from the sandbox resolved the path mistake.
