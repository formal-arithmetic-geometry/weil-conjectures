## Worker report

Item: `lem-coef-brown-slice-fraction-calculus`; group Q52, 2026-10-17.
Module: `Sheaf.CategoryTheory.BrownSliceFractionCalculus`.
Main declaration: `HomotopicalAlgebra.brown_slice_fraction_calculus`.

The earlier sandbox contained a compiling draft and searches, but no node record or report.
I read the node, its fifteen proof steps, the enhanced-diagrams dependency and its recorded
source, the comparison/localization definitions, the right-vertex slice implementation,
and the relevant Mathlib morphism-property declarations. I completed the node record and
this report and made the categorical terminal predicate fully qualified. The sole theorem
has the whole proof `by sorry`; its docstring describes all fifteen proof steps. No source
statement is changed, no dependency interface is repaired, and no independent notion is added.
The four supporting declarations belong to the hypotheses and constructions explicitly
introduced by this very node, as authorized by the helper-declaration rule.

The mathematical source was opened online at
[Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
in particular Definition 7.4.12, Proposition 7.4.13, paragraph 7.6.12,
Corollary 7.6.13, and the discussion of the fibrant subcategory C(x) in Proposition 7.6.16.
The latter explicitly identifies the localization of C(x) with the localized slice.
The section consequence uses the fraction calculus of Corollary 7.2.18 inside that slice.
I follow the node's explicit ordinary all-fibrant hypotheses, including retract closure.
No saturation, model structure, functorial factorization or global choice of localization
is added as a hypothesis.

Clause-by-clause correspondence:

| Node hypothesis or construction | Lean rendering |
| --- | --- |
| Ordinary category with arbitrary object and arrow universes | `(C : Type u) [Category.{v} C]`; `universe u v t` is explicit and auto-implicits are disabled. |
| A terminal object 1 | `BrownFibrantAxioms.terminal` supplies `one : C` and `Nonempty (CategoryTheory.Limits.IsTerminal one)`. The theorem does not depend on a chosen terminal representative. |
| Every arrow to 1 belongs to F | The same field requires `∀ (X : C) (f : X ⟶ one), F f`. |
| Classes W and F | `(W F : MorphismProperty C)`. |
| Both classes contain all isomorphisms | `weak_iso` and `fib_iso` are the respective inequalities from `MorphismProperty.isomorphisms C`. |
| W is closed under composition and satisfies two-out-of-three | `weak_three : W.HasTwoOutOfThreeProperty`; this Mathlib class extends `W.IsStableUnderComposition`, `W.HasOfPostcompProperty W` and `W.HasOfPrecompProperty W`. Thus composition is not omitted. |
| W is retract closed | `weak_retract : W.IsStableUnderRetracts`. |
| F is closed under composition | `fib_comp : F.IsStableUnderComposition`. |
| Pullbacks of F arrows along arbitrary arrows exist | `pullback_exists` quantifies over every `p : Y ⟶ Z`, `f : X ⟶ Z` and assumes only `F p`, concluding `HasPullback p f`. |
| Such pullbacks are again in F | `fib_pullback : F.IsStableUnderBaseChange`, which tests every actual pullback square. |
| Pullbacks of trivial fibrations are trivial fibrations | `trivial_pullback : (F ⊓ W).IsStableUnderBaseChange`. Existence follows from `pullback_exists` since a trivial fibration lies in F. |
| Every arrow factors as W followed by F | `factor` gives `Z`, `w : X ⟶ Z`, `p : Z ⟶ Y`, `W w ∧ F p ∧ w ≫ p = f`, separately for each arrow. |
| Ordinary slice with commuting triangles | Mathlib `Over b`, whose arrows have their strict commuting equation. |
| Full subcategory C(b) on fibrations | `brownFibrantSlice F b := ObjectProperty.FullSubcategory (fun X : Over b ↦ F X.hom)`. No restriction is imposed on its arrows. |
| W and F detected in C | `brownSliceProperty F V b` evaluates `V` on `f.hom.left`, for `V = W` or `V = F`. |
| Enlarged nerves | Existing `FiniteReedy.largeNerve.{u, v, t} C`, with degreewise `ULift` into `max u v t`. Slice objects lie in `max u v`, with arrows in `v`, so their lifted nerve lies in the very same ambient universe. |
| Entire coherent functor-category localization | Existing `FiniteReedy.IsLocalization W q`: quasicategory target, inversion of W and functor equivalence from every entire coherent functor category to its full W-inverting subcategory, with the actual precomposition equation. |
| Coherent slice D/d and its operators | Existing `SSet.Enhanced.rightVertexSlice L (object q b)` fixes the final vertex in every degree, with operators given by `appendLast`. No ordinary homotopy-category slice is substituted. |
| Functor on slices induced by q | `IsBrownSliceComparison F q b j` quantifies over every simplex, extends its underlying composable string by its structure map to b, and requires the value of j to equal q of this extension. The object equations and `HEq` arrow equations specify the whole extended functor without arbitrary transport choices. This characterizes the canonical map, rather than an arbitrary equivalence. |
| C(b) satisfies all Brown hypotheses | The first conjunct for every `b` is `BrownFibrantAxioms (brownFibrantSlice F b) (brownSliceProperty F W b) (brownSliceProperty F F b)`. |
| Localization of C(b) is the localized slice | The comparison `j` satisfies `IsLocalization (brownSliceProperty F W b) j`. For any other localization `r` with target K, the following clause supplies `E : K ⟶ rightVertexSlice L (object q b)`, `IsFunctorEquivalence E` and `AreNaturallyEquivalent (r ≫ E) j`. This states equivalence for the induced comparison, including its coherent identification on the ordinary slice. These are two universal-property presentations of the same assertion, not an extra mathematical assumption. |
| Given a fibration t : T → P | `(P T : C) (p : T ⟶ P), F p → ...`; `p` is the node's t, to avoid confusion with the universe t. |
| Specified coherent section with its triangle | `i` and `e` are slice vertices with underlying simplices `q(id P)` and `q(p)`. A vertex `h` of `mappingSpace (rightVertexSlice L (object q P)) i e` is exactly an edge of the coherent slice from the identity to p: its underlying arrow is the section and its two-simplex is the specified section triangle. Universal quantification over `i,e` with those value equalities avoids dependent casts and excludes no choices of section. |
| Strict fraction representing the section | `∃ Z s a, F s ∧ W s ∧ a ≫ p = s`, with `s : Z ⟶ P`, `a : Z ⟶ T`. |
| Representation up to homotopy in the actual slice | `S` is q of the strict triangle `(s, id P)`, and `A` is q of `(a,p)`. The slice two-simplex `τ` has faces `δ₂ τ = S`, `δ₀ τ = h.val`, `δ₁ τ = A`. Thus it witnesses `h ∘ q(s) ≃ q(a)` in the slice. Since s is inverted, this is exactly the fraction relation `h ≃ q(a)q(s)⁻¹`, retaining the supplied triangle. No unspecified inverse is chosen and no triangle is discarded. |

Dependency declarations actually reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, the recorded module of
  `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.mappingSpace`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`. Its other primitives are reused
  transitively by the localization and slice interfaces.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: the existing real helper definitions
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `IsLocalization` and `object`.
  The finite-Reedy theorem is not used. Adding that theorem as a DAG dependency would
  create a cycle through the Brown finite-direct rectification consumer; the present
  import merely reuses its already published definitions and assumes no result of it.
- `Sheaf.CategoryTheory.SliceArrowEquivalence`: the existing `SSet.Enhanced.rightVertexSlice`,
  supplied by the recorded proof dependency `lem-coef-infinity-slice-arrow-equivalence`.
- Mathlib `Over`, `ObjectProperty.FullSubcategory`, `ComposableArrows`, `MorphismProperty`,
  `HasPullback`, categorical `IsTerminal`, the three morphism-property stability classes,
  and `HasTwoOutOfThreeProperty`; these are not redefined.

The recorded and published proof dependencies have non-public imports:
`EnhancedFunctorConeCalculus`, `InfinityMappingComposition`,
`NerveNaturalHomotopyEquivalence`, and `SpacesHomotopyFiberDetection`.
`SliceArrowEquivalence` is public since its slice definition occurs in the signature.
At this reading `lem-coef-infinity-full-essential-image`,
`lem-coef-quillen-b-discrete-fibration-base-change` and
`lem-coef-trivial-fibration-fraction-model` have no `lean` record; no unused speculative
import for these unstated proof prerequisites is added. They are not needed to type
this theorem and remain named in its natural-language proof for stage 3.

Edge cases checked before accepting the draft:

- The empty category cannot have the assumed terminal object; no extra nonemptiness
  hypothesis is introduced. A terminal one-object category satisfies the formulas.
- For `W = isomorphisms` and `F = all arrows` in a category with finite limits,
  localization is its nerve and fibrant slices are the usual slices. The section
  clause reduces to a strict section, with s an isomorphism (one may take the identity).
- For `F = W = all arrows` in a finitely complete category, the terminal objects
  contract the localized category and its fibrant slices; strict fractions can still
  be formed by pulling p back along the identity of P. No nontrivial section is lost.
- At `b = one`, every structure arrow is in F, so C(b) is the entire ordinary slice,
  equivalent to C as expected. For `p = id P`, the section triangle is still a supplied
  simplex; the final τ retains that supplied coherence, rather than assuming it degenerate.
- For `n = 0`, the comparison condition extends the single slice object to its actual
  structure arrow to b. For `n = 1`, it retains the commuting triangle. Higher n are
  all quantified, so it is not merely an object/arrow formula.
- No equality between u and v, finiteness condition, model structure, functorial
  factorization, chosen inverse map or chosen mere-existence object is imposed.

Searches for reuse (the earlier exact results are in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder`: “The infinity localization of a Brown category of fibrant
  objects over a base is equivalent to its coherent slice, and sections are trivial
  fibration fractions”, 8 hits. A fresh search with “with sections represented by trivial
  fibration fractions” also gave 8 hits, all model-category cofibrant-object/localizer
  statements, not the asserted coherent slice theorem under the Brown hypotheses.
- `msearch.py ... loogle '"HomotopicalAlgebra", "Over"'`, repeated: 12 hits including
  `ModelCategory.over` and the overcategory fibration instances. Their source was read:
  they give model structures on the full overcategory, not this Brown coherent comparison.
- `msearch.py ... leansearch`: “Localization of a Brown category over a fibrant base is
  equivalent to the coherent slice and sections lift along trivial fibrations”, 8 hits:
  ordinary localization, model overcategories and `FibrantBrownFactorization`.
  The latter's signature assumes a model category and describes factorization data;
  it does not give the node's theorem or an axioms predicate for arbitrary W,F.
- `msearch.py ... grep 'localization.*slice|slice.*localization|Brown.*[Ss]lice'
  AlgebraicTopology`, 0 hits. The helper-name grep also returned 0 hits.
- `rg` of Brown/slice/localization in `WeilConjectures` and `lean/Sheaf`, and exact
  searches for all five new declaration names, found no duplicate. Existing
  `BrownFibrantLocalizationPullbacks` proves localization preserves pullbacks;
  `BrownLocalizationProducts` concerns products. Neither states this theorem or
  supplies a packaged Brown-fibrant axioms predicate.
- `rg` for the item ID in `WeilConjectures` gave no match. The exact helper names
  were also checked against `dag/lean_names_upstream.json`; no collision was found.

There is no STATEMENT-DISPUTED flag, statement correction, new node or dependency module.
The node copy changes only `lean`; its complete signature is copied verbatim from the file.
Validation uses only the authorized `scompile.py` and `deliver2.py --no-push` wrappers.

## Second reading by Q52

Independent reading, 2026-10-17. I opened the base node and sandbox node, all fifteen
proof steps, the complete Lean module, the recorded enhanced-diagrams definition node
and its implementation, and the right-vertex-slice node and implementation. There is
no repair note for this item. The sandbox node differs from the base only in `lean`;
there is no statement correction, new node or dependency module to audit.

Source check: this node cites Cisinski, not a Stacks tag. I independently opened
[CatLR.pdf](https://cisinski.app.uni-regensburg.de/CatLR.pdf), and read Definition
7.4.12, the standing assumptions following it, Proposition 7.4.13, Theorem 7.5.18,
paragraph 7.6.12, Corollary 7.6.13, and the definition of C(x) and localization
identification in Proposition 7.6.16. I also checked Corollary 7.2.18 and formula
(the project server). Definition 7.4.12 allows nonfibrant objects; our node explicitly assumes
all objects fibrant, making its pullback and factorization hypotheses apply to all
arrows. Proposition 7.6.16 identifies C(x) as the full subcategory of fibrations,
with both morphism classes detected downstairs, exactly as here. Its additional
right-adjoint assumption belongs to its locally Cartesian closed conclusion and is
not needed for the slice identification. Saturation is a reduction within the proof
of Corollary 7.6.13, not an extra hypothesis. Retract closure is explicitly in our
node and is retained even though Definition 7.4.12 does not require it. No source
hypothesis justifies adding a model structure or functorial factorizations.

My list of objects, hypotheses and conclusion clauses, matched against the Lean:

| Node item | Actual Lean and verdict |
| --- | --- |
| Ordinary category C | `C : Type u`, `[Category.{v} C]`; exact, with independent object and arrow universes. |
| Classes W and F | `W F : MorphismProperty C`; exact, arbitrary classes on arrows. |
| Terminal object 1 and all terminal arrows fibrations | `BrownFibrantAxioms.terminal` asserts existence of `one`, `Nonempty (CategoryTheory.Limits.IsTerminal one)` and `∀ X f, F f`; exact. The conclusion does not name 1, so packaging its existence loses no parameter. |
| Both classes contain every isomorphism | `weak_iso` and `fib_iso` compare `MorphismProperty.isomorphisms C` with W and F; exact. |
| Both classes closed under composition | `fib_comp`, and the composition superclass of `weak_three`; exact. I opened `HasTwoOutOfThreeProperty`, which extends composition stability and both cancellation classes. |
| W has two-out-of-three | `weak_three : W.HasTwoOutOfThreeProperty`; exact, including both cancellation directions. |
| W is retract closed | `weak_retract : W.IsStableUnderRetracts`; exact. Its Mathlib field quantifies over `RetractArrow`, rather than merely object retracts. |
| Arbitrary pullbacks of F maps exist | `pullback_exists` concludes `HasPullback p f` for every `p`, `f` with `F p`; exact. No finite-limit instance is added. |
| These pullbacks lie in F | `fib_pullback : F.IsStableUnderBaseChange`; exact. I checked its field applies to every actual pullback square. |
| Pullbacks of trivial fibrations are trivial fibrations | `trivial_pullback : (F ⊓ W).IsStableUnderBaseChange`; exact. Their existence follows from the previous existence field. |
| Every arrow factors as W followed by F | `factor` gives `Z`, `w`, `p`, `W w ∧ F p ∧ w ≫ p = f`; exact, pointwise existence with no functorial choice. |
| Ordinary slice C/b, strictly commuting arrows | Mathlib `Over b`; exact. |
| Full fibrant slice C(b) | `brownFibrantSlice F b`, now an abbreviation of `(F.overObj (X := b)).FullSubcategory`; exact. All morphisms of the ordinary slice remain available. |
| W and F in the slice detected in C | `brownSliceProperty F V b`, now `V.over.inverseImage (F.overObj (X := b)).ι`; exact, definitionally the same test `V f.hom.left`. |
| Enhanced categories and the entire coherent localization property | The recorded dependency's mapping spaces and equivalence predicates, and `FiniteReedy.IsLocalization W q`; exact. I opened `IsLocalization`, `localDiagrams` and `Inverts`: it requires a quasicategory, inversion of W, and equivalence of whole internal functor simplicial sets with the full subcomplex on W-inverting diagrams. The inclusion equation is actual precomposition by q. |
| Enlarged nerve and localized category | `largeNerve.{u,v,t} C`, `L : SSet.{max u v t}`, and the given q; exact. `largeNerve` is the existing degreewise lifted ordinary nerve, not a replacement object chosen by existence. |
| Coherent slice with the final vertex fixed | Existing `rightVertexSlice L (object q b)`; exact. I opened its degreewise subtype and maps induced by `appendLast`, which preserve the last vertex. |
| Functor induced by q on slices | `IsBrownSliceComparison F q b j`; exact. For every n and every composable string in the full slice, A extends the underlying string by its structure arrows to b, and the equality prescribes j on that simplex. Both object equations and all-arrow `HEq` equations are necessary and present. |
| C(b) satisfies the same Brown hypotheses | First conjunct under `∀ b`, using the two detected slice properties; exact, retaining every field including retract closure. |
| Localization of C(b) is the coherent slice | `∃ j`, the canonical-comparison condition, and `IsLocalization (brownSliceProperty F W b) j`; exact. The following `∀ K r` clause supplies an equivalence E out of every other localization and `AreNaturallyEquivalent (r ≫ E) j`. This is the induced comparison identified on the original slice, not an arbitrary equivalence of the two categories. |
| Any fibration t : T → P | `∀ P T p, F p → ...`; exact. The name p avoids collision with universe t. |
| Any specified coherent section with its triangle | `i,e` are vertices of the actual slice with underlying arrows q(id P), q(p), and h is a vertex of its `mappingSpace i e`; exact. A vertex of this mapping space is a slice edge, whose underlying simplex in L is the specified triangle. The endpoint equalities impose no degeneracy on that triangle. |
| A strict trivial-fibration fraction | `∃ Z s a, F s ∧ W s ∧ a ≫ p = s`; exact. No fibration assumption on a is introduced. |
| The fraction represents that particular section up to slice homotopy | S is q applied to `(s,id P)` and A is q applied to `(a,p)`. The three face equations of the slice two-simplex τ are `δ₂ τ = S`, `δ₀ τ = h.val`, `δ₁ τ = A`; exact. Thus `h ∘ q(s)` and q(a) compose by this triangle in the slice, and inversion of q(s) gives precisely the fraction representation. |

In particular, the last clause does not replace the specified triangle by the equation
in the ordinary homotopy category. For a quasicategory, a two-simplex with prescribed
three edges expresses precisely equality of the composite class and the third edge.
Here that assertion is made in the slice quasicategory itself. The source and target
of S and A agree with the required slice vertices by naturality of q and `a ≫ p = s`;
the subtype proofs do not add arbitrary choices of endpoints. Quantifiers are in the
right order: q and its localization property are given first, each base has its
comparison, and every specified section receives its own fraction witnesses.

Edge cases independently checked:

- The empty category is excluded exactly by the existence of a terminal object in
  the node. No additional nonemptiness condition occurs in Lean. The terminal category
  and zero object of a pointed example cause no special typing requirement.
- For W consisting of isomorphisms and F of all arrows, in a finitely complete
  category, C(b) is the ordinary full slice and the strict-section case is recovered
  by taking `s = id P`. For W = F = all arrows, one may take `Z = T`, `s = p`,
  `a = id T`; terminality contracts the localized category and the slice.
- For b terminal, the fibrant full slice contains every ordinary slice object.
  For p an identity, the section still ranges over every permitted triangle homotopy;
  the endpoint conditions do not force a degenerate triangle.
- At n = 0 the comparison specifies the actual structure arrow; at n = 1 it specifies
  its commuting triangle. Arbitrarily large n are included. There is no indexing set,
  coefficient ring, characteristic, scheme, or numerical degree to restrict here.
- Objects of `Over b` and its full subcategory live in `max u v`, and their arrows
  in v. Both enlarged nerves and the slice live in `max u v t`. No equation between
  u and v is required, and t permits further enlargement.

Independent searches and the reuse repair:

- LeanFinder query: "Infinity localization of the full overcategory of fibrations in
  a category of fibrant objects computes the overcategory of the localization".
  Eight hits, chiefly the model-overcategory instances and ordinary cofibrant-object
  localization; no coherent slice theorem under these Brown hypotheses.
- LeanSearch query: "A category with weak equivalences and fibrations has a
  localization equivalent to the slice of its localization over a fibrant object".
  Eight hits, ordinary `Functor.IsLocalization`, `MorphismProperty.Localization`, and
  category-with-weak-equivalences constructors. These do not state this theorem.
- Loogle query: `"MorphismProperty", "Over"`. Twelve hits, including `overObj`,
  `over`, and the restricted comma category `MorphismProperty.Over`. I read
  `Mathlib/CategoryTheory/MorphismProperty/Comma.lean`: it already provides the exact
  object predicate and induced arrow property that the original draft wrote as lambdas.
  Its `Over` structure also supports restricted morphisms; the already used
  `ObjectProperty.FullSubcategory` gives our specified full-subcategory implementation.
- `msearch.py ... grep` for `category of fibrant objects|BrownFibrantAxioms|slice.*localization|localization.*slice`
  in CategoryTheory gave no hit. Independent `rg` searches in all named project
  sources and Mathlib found no occurrence of the five proposed declaration names,
  including in `dag/lean_names_upstream.json`. Concept searches in Mathlib,
  `WeilConjectures` and `lean/Sheaf` found model overcategories and site localizations,
  and the project's Brown pullback theorem. I opened `ModelCategory/Over.lean` and
  `BrownFibrantLocalizationPullbacks.lean`; neither states the present slice equivalence
  or specified-section fraction clause, and the latter has no shared Brown-axioms
  structure. The recorded enhanced-diagram and right-slice definitions are reused.

Mismatch repaired: the draft's two slice helper bodies unnecessarily repeated the
standard object predicate and induced morphism property. I changed the slice
abbreviation to use Mathlib `overObj`, changed the arrow-property body to use Mathlib
`over` and `inverseImage` along the full-subcategory inclusion, and replaced the
direct `Comma.Over.Basic` import by `MorphismProperty.Comma`. The resulting bodies are
definitionally equal to the old bodies. The main theorem signature is unchanged and
remains verbatim equal to `lean.statement`. No mathematical statement mismatch was
found; no node correction or extra assumption is needed. The Worker report above
records the original formulas; this section records the final API reuse.

All four helper declarations have real data or explicit predicates, with no hidden
`sorry`, choice from mere existence, private copy of a dependency, or local instance.
The only postponed theorem is the named main theorem, with its whole proof `by sorry`.
Its docstring follows all fifteen DAG steps in order. Every declaration names its
source and this blueprint node; there are no unbound variables or universes. I checked
the recorded proof dependency modules: all those currently stated are imported; the
three still without a `lean` record are correctly listed in the Worker report.

Validation: the final module passed the prescribed `scompile.py Q52
lem-coef-brown-slice-fraction-calculus lean/Sheaf/CategoryTheory/BrownSliceFractionCalculus.lean`
invocation, both sandbox and library-path checks, with no diagnostics. The node still
changes only `lean`. Delivery preflight and push are performed with the required
`deliver2.py` wrapper.
