## Worker report

This repairs immutable returned head `4fc9d64fe0e7`. The retained sandbox already held
some repairs; this revision adds the actual support-composition normalization, explicit
nested-summand equation, all-compactification identity normalization, and full eight-step
proof docstring. The node was refreshed from the current shared node, changing only `lean`.
Its mathematical statement, dependencies and proof are unchanged.

The module states `AlgebraicGeometry.Etale.quasifiniteCompactSupportExact`. Its only proof
is `by sorry`; there is no new definition or axiom. The correspondence below uses final
module lines 223–357.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A finite commutative ring | `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` (224). |
| Noetherian schemes V, T, B | `Scheme.{u}` and the three `IsNoetherian` instances (225–226). Mathlib's locally Noetherian plus quasi-compact convention equals the stated finite affine-cover convention. |
| Composable separated finite-type quasi-finite maps | `h : V ⟶ T`, `e : T ⟶ B`, their `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` instances, and `hhq : h.IsQuasiFinite`, `ehq : e.IsQuasiFinite` (227–230). |
| Constant-A module sheaves on the small étale sites | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` (231–237), the recorded six-functor encoding. |
| The proper-support functor | `L`, with `ι f : L f ⟶ lowerStar ... f` (231–237), is characterized by the injective image condition (265–284), exactly as in `properSupportSheafComposition`. |
| Sections on the base change | `F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))` (270–271); this API orders the product as test-object × target source. |
| Closed set of nonzero geometric germs | `T₀ : TopologicalSpace.Closeds ...`, with `v₀ default ∈ T₀ ↔ ...toPresheafFiber ... s ≠ 0` for every separably closed field point (273–282). |
| Reduced induced support proper over the test object | `IsProper ((Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫ pullback.fst V.hom f)` (283–284). |
| Exactness | Existential additive, finite-limit-preservation and finite-colimit-preservation witnesses for `L h`, `L e`, `L (h ≫ e)` and `L (𝟙 T)` (241–249, 259–261). These are conclusions, bound before using the termwise derived API. |
| Every compactification has c_h : Rr_*Dj_! ≅ D(h^supp_!) | `c_h : ∀ c : Compactification h, rightDerivedLowerShriekOfCompactification ... c ≅ @Functor.mapDerivedCategory ... (L h) hA hL hC` (250–252); the analogous `c_e` and `c_he` families are at 253–258. No boundedness restriction occurs. |
| Independence under the specified proper-refinement comparisons | Equations (285–293) compose `rightDerivedLowerShriekOfCompactificationIso A c d` with the comparison at d and identify it with the comparison at c. |
| σ is the identification of the same underlying sections with proper support | `σ : L h ⋙ L e ≅ L (h ≫ e)` and its component equation after composing with `ι (h ≫ e)` (297–302), exactly the normalization in `properSupportSheafComposition`. Injectivity of ι determines this map. |
| c_eh ∘ α = D(σ) ∘ (c_e D(h^supp)) ∘ (Re_! c_h) | Equality of the specified natural isomorphisms (303–318). The left side is `unboundedEtaleLowerShriekCompIso A h e` followed by the chosen-compactification realization of `c_he`. The right side applies `c_h` under Re_! (`isoWhiskerRight`), then `c_e` after D(L h) (`isoWhiskerLeft`), the inverse `mapDerivedCategoryCompIso`, and `mapDerivedCategoryNatIso σ`. |
| Every separated finite-type étale map has proper-support functor canonically equal to sum extension | The family `o f : etaleLowerShriek ... f ... ≅ L f` for all Noetherian source/target schemes (238–240), and its equation after composing with ι, equal to `etaleLowerShriekToLowerStar ... f F` (342–346). Local finite type follows from étaleness. |
| Étale σ sends a nested summand to the composite-lift summand | Explicit equality of module maps (319–341), under `[Etale h] [Etale e]`: insert using the h adjunction unit, apply o h, insert using the e adjunction unit, apply o e, then σ. The right side inserts the original section using the h≫e unit and o(h≫e). `Over.mapComp` transports the test object between parenthesizations. |
| Identity compactification gives the identity comparison | The ordinary identification is fixed by `i_id.hom = ι (𝟙 T) ≫ (lowerStarId ... T).hom` (347–349). The derived equation (350–357) equals exactly `unboundedEtaleLowerShriekId A T`, using `c_id (Compactification.ofIsProper (𝟙 T))`, `mapDerivedCategoryNatIso i_id`, and `mapDerivedCategoryIdIso`. |
| Same normalization for other identity compactifications | `c_id` is a family over every identity compactification (262–264), with the canonical comparison equation (294–296). |

The generator equation covers the node's arbitrary nested lifts, rather than only a
special étale test object: a lift w:W→V from an étale test object over B, with w≫h=v,
is étale by cancellation. Regard it as `W : V.Etale`. Its successive images under
`Over.map h` and `Over.map e` are precisely the lifts in the node. The unit of
`etaleLowerShriekRestrictionAdjunction` inserts the section in the structural-map summand
of the sheafified left Kan extension. Thus the equation compares every nested generator
with its composite-lift generator. It asserts equality of maps, hence equality on every
section in that summand.

The recorded dependency declarations and their source signatures/docstrings were read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`;
  `IsSeparated` from `Morphisms.Separated`.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `Scheme.Hom.IsQuasiFinite`, including finite type and isolated fibre points.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`; `QuasiCompact` from `Morphisms.QuasiCompact`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  scheme `IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, i.e. the unbounded `DerivedCategory`
  of the module-valued sheaf category.
- `def-weil-pbc-geometric-stalks`: `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `GrothendieckTopology.Point.sheafFiber` and `toPresheafFiber`, specialized using
  `Scheme.pointSmallEtale` from `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`: existing
  `Scheme.IdealSheafData.vanishingIdeal` and `subschemeι`, characterized by
  `reduced_induced_closed_subscheme`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.Defs`
  and `.Refinement`, `Compactification` and `Compactification.Refinement`.
- `def-amb-etale-compact-support`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `rightDerivedLowerShriekOfCompactification`, definitionally Dj_! followed by Rr_*.
- `lem-amb-unbounded-compact-support-comparisons`:
  `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
  `unboundedEtaleLowerShriekCompIso` and `unboundedEtaleLowerShriekId`;
  `rightDerivedLowerShriekOfCompactificationIso` and `rightDerivedLowerShriekIso`
  are from upstream `.Derived.LowerShriekIndependenceUnbounded`.
- `lem-cbc-proper-support-sheaf-composition`:
  `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`,
  `properSupportSheafComposition`, including the exact inclusion and σ normalizations.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-weil-pbc-etale-sum-extension`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`, `etaleLowerShriek`;
  its restriction adjunction and graph-normalized comparison to lowerStar are in
  `.UpperLowerStar.FiniteEtale`.

`mapDerivedCategory`, `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, and
`mapDerivedCategoryIdIso` use the existing exact-functor derived API imported by
`.Derived.LowerShriek`. Proof dependency modules are imported as proof-only imports.
Two redundant upstream imports were omitted: upstream
`WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties` collides on
`Scheme.IsClosedSubsetProperOver` with the Sheaf module already imported by the support
interface, and the inverse-image germ theorem is already supplied by the imported
`Sheaf.Paper.InverseImageStalkGerm`. The reduced-induced-closed-subscheme declaration is
also provided through the existing support module. These notions were reused, never copied.

Edge cases checked: the zero coefficient ring is allowed; empty schemes and supports,
zero sections, empty and multipoint étale fibres, nonproper quasi-finite opens, the
identity compactification, arbitrary other identity compactifications, and unbounded
complexes are covered. There is no dimension, excellence, invertibility, characteristic,
connectedness or constructibility hypothesis. All universes and variables are bound.
There are no `HasCompactification` assumptions or extra composite-morphism binders:
the existing Nagata/composition instances elaborate the canonical maps from the actual
Noetherian, separated and finite-type hypotheses.

Searches repeated for this repair:

- `msearch.py ... leanfinder "Quasi finite separated proper support pushforward exact
  unbounded derived compactification compatibility composition"`: eight hits headed by
  `Scheme.Modules.pushforwardComp`, `PresheafOfModules.pushforwardComp`, and
  `SheafOfModules.pushforwardComp`. Their types concern ordinary pushforward composition,
  not this proper-support/derived comparison.
- `msearch.py ... loogle '"shriek"'`: zero hits.
- `msearch.py ... grep 'shriek|properSupport|proper_support'`: zero Mathlib hits.
- Direct `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` for the node id,
  `quasifiniteCompactSupportExact`, `quasiFiniteCompactSupportExact`, and
  `properSupport.*[Ee]xact`: no existing theorem. Focused searches found the comparison,
  exact-derived, graph and étale-generator APIs used here.

Source passages read: Stacks `more-etale.tex`, `lemma-Rf-shriek-for-quasi-finite` (0GKM),
`lemma-separated-etale-shriek` (0F4Y), `lemma-f-shriek-composition` (0F50),
`lemma-lqf-f-shriek-stalk` (0F5F), and the framework of `lemma-shriek-composition` (0F7J).
No statement dispute or source correction is needed. No new node or dependency module
is delivered.

## Repairs of the return

1. H3, c_h: exactness witnesses precede the three actual comparison families into
   `(L h).mapDerivedCategory`, `(L e).mapDerivedCategory`, and
   `(L (h ≫ e)).mapDerivedCategory`; no bare `Nonempty` remains.
2. H3, independence: (285–296) uses the specified canonical comparisons, including the
   identity family, rather than arbitrary candidate isomorphisms.
3. H3, composition: (297–318) fixes σ as the support identification and states the
   requested equality with α, the exact derived compositor, and D(σ).
4. H3, étale nested summands: (319–341) explicitly equates the nested adjunction-unit
   insertion with the composite-lift insertion.
5. H3, identity: (347–357) fixes the ordinary and derived comparisons using
   `unboundedEtaleLowerShriekId`; (262–264, 294–296) transfers this to every compactification.
6. H3, extra assumptions: no `HasCompactification` binder remains. The redundant
   composite separated/finite-type/quasi-compact binders in the retained sandbox were
   also removed; elaboration succeeds from the actual hypotheses.
7. H8: all eight proof steps are now copied in full from the unchanged node into the
   declaration docstring, with their citations, refinement and tower calculations,
   generator construction and identity normalization, numbered 1 through 8.
8. H11: the inaccurate old reading is not retained. The mapping above identifies the
   actual comparison families and equations. The independent second reader must verify
   them before delivery; this worker does not claim an independent reading.

Validation: `scompile.py Q11 lem-sfb-quasifinite-compact-support-exact <module>` passed
both sandbox and library checks without errors or warnings after removing the duplicate
import. `lean.statement` is the literal signature from `theorem` up to, excluding, the body delimiter `:=`.
The first dry run exposed that the metadata had included that delimiter; it was removed
to match the checker's signature boundary. The Lean module itself was already clean.

## Second reading by Q11

I independently read the sandbox node and module against Stacks `more-etale.tex`,
`lemma-Rf-shriek-for-quasi-finite` (0GKM), `lemma-separated-etale-shriek` (0F4Y),
`lemma-f-shriek-composition` (0F50), `lemma-lqf-f-shriek-stalk` (0F5F), and
`lemma-shriek-composition` (0F7J). I also read the surrounding sections introducing
proper support and its locally quasi-finite version. The support construction assumes
separated and locally finite type; the derived compactification comparison uses qcqs.
The node's Noetherian and finite-type hypotheses provide these conditions. Tag 0GKM
speaks of common domains; the node's eight-step proof supplies the stated unbounded
comparison by exact finite pushforward and refinement. This needs no dimension,
excellence, characteristic, or invertibility condition.

My object/hypothesis/conclusion list, with its Lean counterpart and verdict, is:

| Item read from the node | Lean rendering and independent verdict |
| --- | --- |
| A finite commutative coefficient ring, without a nonzero assumption | `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`. Exact match. |
| Schemes V, T and B, each admitting a finite Noetherian affine cover | `{V T B : Scheme.{u}}` and `[IsNoetherian V/T/B]`. Mathlib `IsNoetherian` extends locally Noetherian and `CompactSpace`; the affine basis makes this equivalent to the node's finite-cover convention. Match. |
| Composable maps h:V→T and e:T→B | `(h : V ⟶ T) (e : T ⟶ B)`, with composite `h ≫ e`. Match, including order. |
| Both maps separated, quasi-finite and finite type | `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `hhq : h.IsQuasiFinite`, `ehq : e.IsQuasiFinite`. The recorded `Scheme.Hom.IsQuasiFinite` includes finite type and isolated points of the scheme-theoretic fibres. Redundant finite-type witnesses agree by proof irrelevance; no extra condition is introduced. Match. |
| Constant-A module sheaves on small étale sites; unbounded derived categories | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and `Functor.mapDerivedCategory`; the compactification candidate has the same sheaf category and unrestricted `DerivedCategory`. Match. |
| The proper-support subsheaf of ordinary pushforward | `L`, `ι`, componentwise `Function.Injective`, and the image iff proper-support condition. This is exactly the existential functor/inclusion interface in `properSupportSheafComposition`, not a second definition or a free arbitrary functor. Match. |
| Support is the closed locus of nonzero geometric germs | `T₀ : TopologicalSpace.Closeds ...` and membership iff `toPresheafFiber ... s ≠ 0` for every separably closed Ω and geometric lift `v₀`. The point is that of the source sheaf, via the pulled-back test object's structural map. Match. |
| Give that support its reduced induced scheme structure and require it proper over the test object | `(Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫ pullback.fst V.hom f` is proper. In this API the product is test-object × source, so `fst` is the required projection. Match. |
| The proper-support functor is exact | Existential `Additive`, `PreservesFiniteLimits`, `PreservesFiniteColimits` witnesses for `L h`, `L e`, `L (h ≫ e)`, and identities. They are conclusions before the derived terms, never hypotheses supplied by the caller. Match. |
| For every compactification, Rr_*Dj_! ≅ D(h_!supp), and likewise e and eh | Actual families `c_h`, `c_e`, `c_he`, indexed by every `Compactification`, targeting `@Functor.mapDerivedCategory ... (L f)` with its exactness witnesses. No `Nonempty` stand-in or boundedness restriction. Match. |
| Independence under the specified canonical refinement comparisons | Each family satisfies `(rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫ (c_f d).hom = (c_f c).hom`. The dependency supplies the refinement normalization, so this pairwise equation uses precisely its canonical comparisons. Match. |
| σ is the section-preserving composition identification | `σ : L h ⋙ L e ≅ L (h ≫ e)` and its equation after `ι (h ≫ e)`, using both ordinary inclusions and `lowerStarComp`. This is the dependency's normalization verbatim, and the injective inclusion determines σ. Match. |
| c_eh ∘ α equals the successive c_h, c_e followed by D(σ) | Equality of isomorphisms using `unboundedEtaleLowerShriekCompIso`, the chosen-compactification identifications, `isoWhiskerRight`, `isoWhiskerLeft`, inverse `mapDerivedCategoryCompIso`, and `mapDerivedCategoryNatIso σ`. Directions and functor order match the displayed node equation. Pairwise independence transports it to arbitrary compactifications. Match. |
| Every separated finite-type étale map has canonical sum-extension identification | `o f : etaleLowerShriek ... f ... ≅ L f` for every Noetherian X,Y and separated quasi-compact étale f; its composite with `ι f` is the existing graph-extension map `etaleLowerShriekToLowerStar`. Étale supplies local finite type. Match. |
| For étale e,h the nested summand is sent to its composite-lift summand | The explicit module-map equation under `∀ [Etale h] [Etale e]` inserts with the two restriction-adjunction units, applies `o h`, `o e`, and σ, and equals insertion for h≫e followed by `o (h ≫ e)`. `Over.mapComp.inv` gives the contravariant section transport in the correct direction. Match. |
| Identity compactification gives the identity comparison; all other identity compactifications have the same normalization | Repaired: `idA/idL/idC` and `c_id X` now range over every Noetherian X; `i_id` is fixed by the ordinary inclusion and `lowerStarId`, and the displayed derived equality is `unboundedEtaleLowerShriekId A X`. Its refinement equation covers every other identity compactification. Three added `HEq` clauses identify `c_h`, `c_e`, and `c_he` with this same normalized family when their compactification is an identity compactification. Match after repair. |

For the nested-summand clause I checked the actual upstream definitions, not just their
names. `etaleLowerShriek` is sheafification of left Kan extension along `Over.map`;
`etaleLowerShriekRestrictionAdjunction` is its restriction adjunction. Its unit therefore
inserts the section in the structural-map summand. Any nested lifts from an arbitrary
étale test scheme over B give an étale lift to V, by cancellation for étale morphisms.
That test object is some `W : V.Etale` in the displayed equation; conversely each such W
provides those nested lifts. Thus the equation covers every summand and every section,
including linear combinations after sheafification.

The mismatch I found was in identity coherence: the incoming statement exhibited a
normalized `c_id` family separately from `c_h`, `c_e`, and `c_he`. It did not require
those three families themselves to use that comparison when a map specializes to an
identity. I generalized the identity witnesses from T to arbitrary Noetherian X and
added the three equalities tying the families together. `HEq` here expresses equality
across the dependent scheme/morphism indices; if h is an identity, take d=c and the
premise is reflexivity. The resulting conclusion is equality with the normalized
comparison, not merely existence of an unrelated identity comparison. The same check
applies to e and h≫e. This repairs the Lean to the unchanged node: no natural statement,
dependency, proof step, or target statement changed. The worker's line-number references
and identity rows above describe the incoming version; this section describes the final
version. The docstring now explains this identity connection and retains all eight proof
steps with their sources and dependency citations.

I opened the dependency declarations and signatures: `Scheme`, `IsProper`, `IsSeparated`,
`LocallyOfFiniteType`, `QuasiCompact`, scheme `IsNoetherian`, the project's
`Scheme.Hom.IsQuasiFinite`, `DerivedCategoryModule`/its sheaf encoding,
`pointSmallEtale` and `toPresheafFiber`, the reduced-closed-subscheme characterization,
`Compactification` and refinements, `rightDerivedLowerShriekOfCompactification`, the
pairwise compactification isomorphism, `properSupportSheafComposition`,
`unboundedEtaleLowerShriekCompIso` and `unboundedEtaleLowerShriekId`, and
`etaleLowerShriek` and its restriction adjunction/graph-extension comparison. The exact
functor compositor and derived natural-isomorphism API apply the original maps termwise.
The recorded dependencies provide the needed objects without an additional instance or
private construction. In particular the upstream compactification's open immersion need
not be qc in general, but it is qc here over the Noetherian proper ambient scheme.
Nagata and composition instances supply compactifications; none is an added hypothesis.
There is no repair note for this item, no `statement_change`, and no new node or
dependency module to audit.

Edge cases: zero coefficient ring and zero sheaf/section are allowed. Empty schemes,
empty support, and empty fibres are allowed; the empty reduced support is proper and
sum-extension has its zero summand value. Multipoint fibres and arbitrary étale test
objects are covered by the generator equation. Nonproper open quasi-finite maps are
allowed; properness is required of support only. Identity cases are now tied to the
actual comparison families, for all compactifications. There is no n, dimension,
characteristic, field-coefficient, connectedness, constructibility, or boundedness
restriction. Universes are explicit: schemes and geometric fields use u, the full
small étale category and coefficient modules use u+1 as in the recorded six-functor
encoding. Separably closed extensions of residue fields can be taken in u, so geometric
points detect all underlying points. No site-object/morphism universe equality or
independent small test-field universe makes a hypothesis vacuous.

Independent searches repeated using the prescribed `msearch.py` wrapper:

- LeanSearch, “A quasi-finite separated morphism of schemes has exact direct image with
  compact support, agreeing with compactification-defined derived lower shriek”: eight
  hits about `LocallyQuasiFinite`, quasi-separatedness and quasi-compactness, no match.
- LeanFinder, “Direct image with compact support along a quasi-finite separated morphism
  is exact and equals its unbounded derived functor”: eight hits, headed by module-sheaf
  ordinary pushforward adjointness and exact-derived lifting/factorization, no match.
- Loogle, `"LowerShriek"`: zero hits.
- Grep, `properSupport|proper_support|quasiFinite.*[Ee]xact|quasifinite.*[Ee]xact`:
  only an incidental quasi-finite-at-point proof line, no matching declaration.
- Direct `rg` on Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`, using
  `quasifiniteCompactSupportExact`, `quasiFiniteCompactSupportExact`,
  `properSupport.*[Ee]xact`, and both word orders of quasi-finite/compact-support:
  no existing statement. The shared weighted-flat-trace theorem concerns a flat trace
  and degree-zero comparison and does not state this unbounded coherence package.

No hollow definition, axiom, private/local notion, or proved theorem is introduced.
The sole theorem body remains `by sorry`; all variables and universes are explicitly
bound. The node still differs from the shared node only in `lean`; `lean.statement`
was regenerated verbatim from the final signature. Final compilation and preflight
results are recorded below.

Final validation: the prescribed `scompile.py Q11
lem-sfb-quasifinite-compact-support-exact
lean/Sheaf/AlgebraicGeometry/QuasiFiniteCompactSupportExact.lean` passed both its
sandbox (3.9 seconds) and library (4.4 seconds) checks with no errors or warnings.
The final source has one `sorry`, no line over 100 characters, and its signature is
verbatim equal to `lean.statement`.
The prescribed `deliver2.py Q11 lem-sfb-quasifinite-compact-support-exact --no-push`
reported `OK (dry run)`: its server preflight and compilation passed; nothing was pushed
by that dry run.
