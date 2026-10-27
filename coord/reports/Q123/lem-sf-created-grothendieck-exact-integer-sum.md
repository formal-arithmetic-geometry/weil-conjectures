## Worker report

Delivered module: `Sheaf.CategoryTheory.CreatedGrothendieckExactIntegerSum`.
Declaration: `CategoryTheory.createdGrothendieck_exactIntegerSum`.
This is a single theorem with a conjunction of the node's conclusions; its only proof is
`sorry`. There are no new definitions, auxiliary postponed theorems, new nodes, dependency
repairs, or statement corrections. The node copy changes only `lean`.

Sources read: Stacks `literature/stacks-project/injectives.tex`,
`definition-grothendieck-conditions` (Tag 079B), its following discussion of exact direct sums
and filtered colimits, and `lemma-F-G-monos` (the finite-subsum presentation and passage of
kernels through a filtered colimit); the supplied source modules
`WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`, `Free.isSeparator_algebra` and
`isGrothendieckAbelian`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra`,
`Free.preservesHomology_functor`. These last declarations concern the specific IsoAlgebra
category, so they are sources for the generic argument, not exact existing matches.
The nine-step node proof is reproduced, with the canonical maps explained, in the theorem
docstring. Nothing is proved in this delivery.

Hypotheses, one by one:

| Node | Lean |
| --- | --- |
| Fixed universe V | `universe w`; all small family indices are `I : Type w` |
| Grothendieck abelian A relative to V | `C : Type u₁`, `Category.{v₁} C`, `Abelian C`, `IsGrothendieckAbelian.{w} C` |
| Locally V-small abelian B | `D : Type u₂`, `Category.{v₂} D`, `Abelian D`, `LocallySmall.{w} D` |
| U : B → A | `U : D ⥤ C` |
| Additive | `[U.Additive]` |
| Faithful | `[U.Faithful]` |
| Conservative | `[U.ReflectsIsomorphisms]` |
| Exact | `[PreservesFiniteLimits U] [PreservesFiniteColimits U]` |
| Creates all V-small colimits | `[CreatesColimitsOfSize.{w, w} U]` |
| Additive left adjoint A : A → B | `L : C ⥤ D`, `[L.Additive]`, `adj : L ⊣ U` |
| Additional integer-indexed autoequivalences | `∀ (P : ℤ → C ⥤ C) [∀ n : ℤ, (P n).Additive] [∀ n : ℤ, (P n).IsEquivalence]` |
| Exactness of the P_n | `(∀ n : ℤ, exactFunctor C C (P n)) →` |
| Natural pointwise-sum identification UA ≅ ⊕P_n | `(L ⋙ U ≅ ∐ P) →`; functor composition follows Lean's order |

The last three hypotheses occur only in the final conditional conjunct. They are not imposed
on generator transfer, Grothendieck transfer, or the arbitrary-family coproduct claims.
The five universes `w v₁ v₂ u₁ u₂` are independent; local smallness is not replaced by equal
hom universes. `set_option autoImplicit false` ensures no auto-bound variables.

Conclusions, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Any generator G transfers to A(G) | `∀ G : C, IsSeparator G → IsSeparator (L.obj G)` |
| Generator means maps miss every proper subobject | `IsSeparator` is the existing faithful representable predicate. In an abelian category it is equivalent to the node's convention: a separator detects a nonzero cokernel of a proper mono; conversely use the proper kernel of a nonzero difference of parallel arrows. This equivalence is explained in the module docstring, without defining another generator predicate. |
| Filtered colimits in B are exact | The `ab5OfSize` field of the asserted `IsGrothendieckAbelian.{w} D`, whose `ofShape` field gives exact colimits for every V-small filtered category. No supplied colimits or exactness of B are assumed. |
| Hence B is Grothendieck abelian | `IsGrothendieckAbelian.{w} D`, including local smallness, existence of filtered colimits, AB5, and a separator; its standard `hasColimits` instance supplies all V-small colimits |
| Small coproducts are exact | For each `I : Type w`, `exactFunctor (Discrete I ⥤ C) C colim` |
| Explicitly, coproducts of any small family of short exact sequences are short exact | The following conjunct quantifies over `S : ShortComplex (Discrete I ⥤ C)`, assumes short exactness after every evaluation, and asserts `(S.map colim).ShortExact`. A diagram short complex is exactly a family of two composable maps with zero composite. Its two coproduct arrows are `colim.map S.f` and `colim.map S.g`, not arbitrary arrows. |
| The canonical finite-subsum maps identify the coproduct with the finite-subset filtered colimit | For every `X : I → C`, `Nonempty (IsColimit (finiteSubcoproductsCocone X))` and invertibility of `colimit.desc (liftToFinsetObj (Discrete.functor X)) (finiteSubcoproductsCocone X)` |
| All finite subsets including the empty one | Mathlib's indexing category is `Finset (Discrete I)`, with inclusions as morphisms. Its object at J is the coproduct indexed by the subtype of members of J; its transitions and cocone maps are defined by the original summand inclusions. `Discrete I` is just I with its discrete category structure, so it changes neither the family nor the finite subsets. |
| Naturality in maps of families | The displayed square `colim.map ((liftToFinset C I).map a) ≫ liftToFinsetColimIso.hom.app G = liftToFinsetColimIso.hom.app F ≫ colim.map a`, for every `a : F ⟶ G` |
| Finite sums identify kernels and cokernels | `exactFunctor (Discrete I ⥤ C) (Finset (Discrete I) ⥤ C) (liftToFinset C I)`, together with explicit invertibility of `kernelComparison a colim` and `cokernelComparison a colim` for every family over every finite subset J |
| Filtered colimits of those kernel/cokernel diagrams identify with the full-sum diagrams | Explicit `IsIso` assertions for `kernelComparison ((liftToFinset C I).map a) (colim (J := Finset (Discrete I)))` and its cokernel comparison, followed by the corresponding full-coproduct comparisons for `a`. These are the actual canonical morphisms, so they identify the inclusions and quotient arrows by the defining equations of `kernelComparison` and `cokernelComparison`, not merely abstract isomorphism types. |
| These kernel/cokernel identifications are natural | The comparisons used are Mathlib's `kernelComparison` and `cokernelComparison`, which already satisfy `kernelComparison_comp_kernel_map` and `cokernel_map_comp_cokernelComparison` for every commuting square. Combined with the displayed natural isomorphism of the two coproduct functors, these are the canonical natural identifications in the node. There are no unconstrained comparison maps in the theorem. |
| Consequently UA and A preserve short exact sequences | Last conjunct: for every short exact `S : ShortComplex C`, `(S.map (L ⋙ U)).ShortExact ∧ (S.map L).ShortExact` |
| A is exact (finite-limit/finite-colimit convention) | `exactFunctor C D L`; also `exactFunctor C C (L ⋙ U)` for the underlying composite |

The coproduct in `L ⋙ U ≅ ∐ P` is the standard coproduct in the functor category.
It is computed pointwise, as specified by `Limits.sigmaObjIso` and its coprojection
identities in `Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products`.
The canonical finite-subsum isomorphism is precisely Mathlib's
`CoproductsFromFiniteFiltered.liftToFinsetColimIso`; its definition uses singleton legs
and the colimit universal property. It is not an arbitrary chosen natural isomorphism.
The additional `IsColimit` and `colimit.desc` assertions expose the specified cocone itself.
`IsColimit` is Type-valued, so `Nonempty` states existence of its universal-property witness;
no construction or definition chooses data from this assertion.

Dependency declarations used, with source signatures/docstrings read:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`.
  The class extends preadditivity and normal mono/epi categories and requires finite
  products, kernels, and cokernels; this is the node's equivalent abelian structure.
- `def-sp-grothendieck-abelian`:
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `CategoryTheory.IsGrothendieckAbelian.{w}`. Its definition explicitly records local
  smallness, filtered colimits, AB5 and a separator, and its instances supply small colimits.
- `def-galois-exact-functor`: `Mathlib.CategoryTheory.Limits.ExactFunctor`,
  `CategoryTheory.exactFunctor`, the intersection of `leftExactFunctor` and
  `rightExactFunctor`; equivalently `PreservesFiniteLimits ∧ PreservesFiniteColimits`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, and `colimit.desc`; also `Cocone` and `IsColimit`.
  The two finite-subsum constructions and `colim` use exactly these colimits.
- `def-weil-pbc-exact-sequence`: `Mathlib.Algebra.Homology.ExactSequence`, with the
  recorded supplementary `CategoryTheory.ShortComplex.ShortExact` from
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`. It comprises exactness, a monic
  first arrow, and an epic second arrow.
- Proof dependency `lem-sfb-grothendieck-filtered-finite-limits` is already Mathlib:
  `IsGrothendieckAbelian.hasLimits`, `.hasColimits`, and
  `HasExactColimitsOfShape.preservesFiniteLimits`, publicly available through the
  Grothendieck-category statement import.
- Proof dependency `lem-weil-pbc-jointly-reflect-short-exact`:
  `Mathlib.CategoryTheory.Functor.ReflectsIso.Exact`,
  `CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff`, imported as a proof-only
  dependency. Its full signature assumes abelian source/targets, joint reflection of
  isomorphisms, and preservation of finite limits and colimits, exactly as used in
  proof steps 3 and 9 for the singleton U family.

No dependency interface is missing or unusable. The existing recorded Mathlib declarations
are used, not replaced. The example Sheaf CompactObject module has been withdrawn; its
node points to `WeilConjectures.CategoryTheory.CompactObject`, which was also read for
the current header/docstring conventions.

Searches performed:

1. `msearch.py ... leanfinder`: “A faithful conservative exact functor creating small
   colimits with additive left adjoint transfers Grothendieck categories and generators;
   sums of exact autoequivalences are exact”. Eight ingredient hits, including
   `Adjunction.hasExactColimitsOfShape`, `Functor.exact_tfae`,
   `HasExactColimitsOfShape.domain_of_functor`, `ExactFunctor`, and `abelianOfAdjunction`.
   None states the generic transfer plus the canonical finite-subsum clauses.
2. `msearch.py ... loogle`: `CategoryTheory.IsGrothendieckAbelian,
   CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimIso`.
   Zero combined hits.
3. `msearch.py ... leansearch`: “An abelian category with a faithful exact conservative
   colimit creating functor to a Grothendieck category and a left adjoint is Grothendieck;
   coproducts of exact equivalences are exact”. Eight ingredient hits, including
   `IsGrothendieckAbelian`, `.hasColimits`, `.hasLimits`, `AB4OfSize.mk`, and
   `abelianOfAdjunction`; no full existing match.
4. `msearch.py ... grep 'liftToFinset|domain_of_functor|isSeparator.*adj'
   CategoryTheory`: eighteen hits, including the existing canonical finite-subsum
   constructions and exactness ingredients. Read their actual definitions in
   `Limits/Constructions/Filtered.lean`, `Preadditive/LiftToFinset.lean`, and
   `Abelian/GrothendieckAxioms/Basic.lean`; reused the constructions.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for the item ID and `CreatedGrothendieck|finiteSubsum` variants: only unrelated
   scheme-cohomology finite-subsum results; no declaration of this generic statement.
   `tools/lean_names_upstream.py show` for the item gives no binding.
6. `rg` for `createdGrothendieck_exactIntegerSum` in Mathlib, WeilConjectures,
   Sheaf and the upstream names index: no collision.
7. Read the generator, Grothendieck, creation, finite-limit/finite-colimit exactness,
   kernel/cokernel comparison, pointwise functor coproduct, short-complex, and
   joint-reflection source declarations. Only their established interfaces are used.

Edge cases checked before/following the signature:

- Empty I: `Finset (Discrete I)` still has the empty finite subset. The coproduct and
  each resulting sequence are zero; the naturality and comparison assertions reduce
  to the canonical zero-object cases. No `Nonempty I` is assumed.
- Empty J: finite comparison assertions include the zero-family coproduct functor.
- Singleton families: the canonical colimit/coproduct maps identify with their unique
  components, and the kernel/cokernel assertions are the original ones.
- Zero category: its zero object is a separator by the proper-subobject convention
  (there are no proper subobjects); all conclusions apply without nonzero hypotheses.
- Zero morphisms and identity morphisms: the canonical kernel/cokernel comparisons
  yield the full-domain/zero kernels and zero/full-codomain cokernels respectively.
- Integer index includes negative, zero, and positive n; there is no truncation or
  boundedness condition. `ℤ : Type 0` is small relative to every w.
- Universes: object universes u₁/u₂ and hom universes v₁/v₂ remain separate from w;
  there is no forced equality or smallness condition on the object collections.
- U = identity with L = identity is consistent with all transfer clauses. The orbit-sum
  clause remains conditional on its stated natural isomorphism; it is never silently
  imposed on the identity example.

Validation: `scompile.py Q123 lem-sf-created-grothendieck-exact-integer-sum
<module-file>` compiled both the sandbox probe of the actual module and its named library
module cleanly (2.2 s and 2.5 s). All variables/universes are explicit; no diagnostic commands
remain in the delivered module. The earlier scratch probe checked canonical comparison
signatures and confirmed that colimit functors preserve zero morphisms. Its deliberate
queries identified the correct `colim.map` interface and the lack of a generic zero-map
instance for `liftToFinset`; the final statement uses neither the nonexistent
`colimit.map` name nor any such zero-map assumption on `liftToFinset`.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q123

A second pass by this same dispatcher-assigned worker reread the complete node and final
Lean signature together; no separate agent was started, as the assignment prohibits that.
The maintainer performs the independent review of this delivery.

Checked the hypothesis table against every binder and the conclusion table against every
conjunct. The orbit-sum data are inside the final implication, leaving the unconditional
transfer and family assertions untouched. `L ⋙ U` is UA, and the standard functor coproduct
is pointwise, not a sum of unrelated object choices. The generator convention is equivalent
in abelian categories and explicitly explained. Exactness uses finite limits and finite
colimits, rather than just an unqualified exactness predicate.

Reopened the Mathlib finite-subsum definitions: `liftToFinsetObj` uses the actual finite
subset subtype, its maps are the specified inclusions, and `finiteSubcoproductsCocone`
has point the full coproduct. The canonical `colimit.desc` is asserted invertible; its
universal property and the natural `liftToFinsetColimIso` identify the same summands and
therefore the same arrows. The finite, filtered, and full kernel/cokernel comparisons
are all canonical Mathlib maps. Their defining inclusion/quotient equations and standard
naturality lemmas guarantee the node's compatibility clauses, including commuting squares
of maps of families. No arbitrary comparison data are substituted.

Checked the empty-index and independent-universe cases again. Checked that the single
`sorry` is attached to the single node-matching theorem and that its docstring gives every
proof step. No mismatch or statement correction was found in this second pass. The scratch
probe's API corrections were made before the clean compile; no final signature change
was needed after compilation.
