## Worker report

The module `Sheaf.SixFunctors.IntegralTensorInverseImage` states
`AlgebraicGeometry.ProEtale.CondensedRing.integralTensorInverseImage` with a single
`sorry` proof. All other declarations are explicit auxiliary constructions for its
canonical completion comparison. The item's statement and dependency lists are unchanged.

Hypothesis and clause correspondence:

- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The finite coefficient extension is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`, the existing finite subextension of
  the fixed algebraic closure. This represents arbitrary finite extensions up to
  coefficient isomorphism, as in the coefficient conventions. Its valuation ring is
  the existing `Profinite.padicIntegersRingObj ℓ E.val`; its pullback is the existing
  `condensedRingObj ... X`. No coefficient ring is supplied as a hypothesis.
- A field of positive characteristic different from ℓ is `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. The prime characteristic implies
  positive characteristic. The scheme universe `u` is arbitrary.
- The schemes are `X Y : Scheme.{u}` with `Over (Spec (.of k))`, separated, locally
  of finite type and quasi-compact structure morphisms. Locally finite type plus
  quasi-compact is finite type. `[g.IsOver (Spec (.of k))]` states that the arbitrary
  map `g : X ⟶ Y` is a k-morphism. These are exactly the imported standing setting;
  no dimension, properness, smoothness or nonemptiness hypothesis is imposed.
- The ambient category is `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X)
  Ab.{u+1}) (condensedRingObj ... X))`. The bounded constructible predicate is the
  dependency's `AlgebraicGeometry.ProEtale.boundedConstructible`, with no completeness
  added to its definition or to the input hypotheses.
- Pullback preservation is the first conjunct, for every `K` in the ambient category
  over Y satisfying that bounded constructible predicate. The output is
  `(upperStar ... g).leftDerivedFunctor.obj K` with the predicate over X.
- The other half of that first conjunct is `IntegralPullbackIsCompleted ℓ E g K`.
  This is the canonical comparison's invertibility, expressed without choosing a
  model of the homotopy limit: there is a product fan `c`, its `IsLimit` witness `hc`,
  and a connecting map making the prescribed triangle distinguished. The first map
  is the product lift of the actual finite reduction maps; the second is 1 minus
  the shift induced by the actual quotient transitions. This is the usual
  `L → product K_n → product K_n → L[1]` derived-limit triangle. In particular it
  specifies the comparison, rather than asserting existence of an unrelated iso.
- `integralFiniteComplex` is the cone of multiplication by `ℓ^(n+1)` on a
  representing complex P. The two-term flat resolution
  `[O_E --ℓ^(n+1)--> O_E]` of O_E/ℓ^(n+1) shows that this computes precisely
  `P tensor^L O_E/ℓ^(n+1)` for any P. No K-flat hypothesis on P is needed,
  since the coefficient resolution is bounded and flat. The quotient map is
  the actual cone inclusion; the transition uses the square with multiplication
  by ℓ on the source and identity on the target. These are the canonical finite
  reduction maps. The definition quantifies a representative P and an isomorphism
  `e : Q.obj P ≅ K`; the first leg is pulled back from `e.inv ≫ Q.map inclusion`.
  Changing the representative or its identification transports this same canonical
  completion comparison, so existence of the model adds no condition on K.
  Powers of ℓ and powers of any uniformizer are cofinal in the finite DVR O_E,
  so this computes exactly the source's completion. The zero exponent is omitted
  by indexing n+1; adding its zero quotient changes no inverse limit.
- Applying the existing inverse image to these derived finite reductions gives
  the source's `g⁻¹(K tensor^L O_E/ℓ^(n+1))` after restriction to constant O_E:
  at finite level the pulled-back coefficient quotient is the constant finite ring,
  and the coefficient pullback comparison is the canonical one from the point.
  Exact coefficient restriction preserves products and triangles and detects
  isomorphisms. Thus the displayed internal-module comparison is precisely the
  scalar-restricted completed inverse-image assertion, with the coefficient action
  retained. Naturality is built into the quotient maps, derived tensor, and pullback;
  no arbitrary isomorphism or extra model is quantified over as an input assumption.
- The tensor conjunct quantifies arbitrary `K L` over X and their two bounded
  constructibility hypotheses. Its output is exactly
  `((derivedTensor ... X).obj K).obj L` in the ambient category. There is no completion.
- The open conjunct quantifies every `j : X ⟶ Y` with `IsOpenImmersion j`,
  `QuasiCompact j` and `j.IsOver ...`. It uses the exact levelwise functor
  `(openImmersionLowerShriek ... j).mapDerivedCategory`, and asserts bounded
  constructibility for every bounded constructible input.
- The closed conjunct quantifies every `i : X ⟶ Y` with `IsClosedImmersion i` and
  `i.IsOver ...`. It uses `(lowerStar ... i).rightDerivedFunctor`, the ambient
  direct image on derived categories. It has exactly the same preservation claim.
  On these Noetherian schemes this agrees with the exact closed direct image.
- The final prose concerning stratification describes the purpose of the four
  assertions; it is not an additional generation assertion. The proof docstring
  records all three DAG proof steps and their three detailed lemma dependencies.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  `AlgebraicGeometry.ProEtale.BoundedConstructible`, `boundedConstructible` and
  `CondensedRing.compactificationOverField`. The statement uses the first two and
  expands the standing setting into binders; no compactification is needed in this
  lemma's signature. Read the full module locally and the current source through
  `scompile.py --source` (the latter uses Over objects in its restricted functors).
- `sk-def-sfb-derived-tensor-hom`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`, importing its Tensor
  module; `CondensedRing.derivedTensor`, the relative K-flat derived tensor,
  `derivedHom` and the tensor-Hom adjunction. Read the full signatures and docstrings,
  including the current server sources. Only the relative tensor is needed here.
- Their existing ambient operations are `CondensedRing.upperStar`,
  `openImmersionLowerShriek`, and `lowerStar` in the corresponding UpperLowerStar
  and LowerShriek modules; their derived forms are the generic functor constructions.
- Existing integral coefficients: `Profinite.padicIntegersRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, and
  `ProEtale.condensedRingObj` from the module-object framework. All reductions use
  Mathlib `CochainComplex.mappingCone`, `CochainComplex.mappingCone.inr`,
  `HomologicalComplex.homotopyCofiber.mapArrowHom`, and `DerivedCategory.Q`.
- None of the three detailed proof dependencies has a Lean declaration or a closed
  upstream audit in the current DAG, so there is no proof-only import to add.

Edge cases checked: X or Y empty, zero complexes, zero tensor factor, identity map,
identity/empty open immersions and identity/empty closed immersions. No binder
excludes them. The product index is all natural numbers, hence includes the first
positive quotient even at ℓ=2 or for ramified extensions. The coefficients retain
Ab.{u+1} on a Scheme.{u} site. The tensor statement imposes no extra finite Tor or
flatness assumption. The derived-limit triangle has the conventional 1-shift sign.

Searches made:

- `msearch.py ... leanfinder` with query "Inverse image preserves integral bounded
  constructible complexes and agrees with completed inverse image; uncompleted
  derived tensor and extension by zero preserve constructibility": eight hits on
  constructible preimages and condensed modules, no matching statement.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor, AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStar`:
  zero hits, unknown first identifier in the Mathlib-only index.
- `msearch.py ... grep 'boundedConstructible|completedInverseImage|integralTensor'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` with query "Integral bounded constructible complexes
  on a pro-etale site are stable under inverse image ordinary derived tensor
  extension by zero and closed direct image": eight hits on object-property
  preservation, integral morphisms and limits, no match.
- `rg` of the upstream WeilConjectures tree, this project's lean/Sheaf, and
  dag/lean_names_upstream.json for the item id and integral/condensed completion
  names: no existing full statement. The upstream BoundedConstructible module has
  preservation components, but not the completed Stacks comparison. Existing
  `IntegralOperationsPreserveConstructible` and `OrdinaryCompletedIntegralPullback`
  concern SheafOfModules over completed constant coefficients, not the ambient
  condensed module-object category of this item; the former also uses a completed
  tensor. They do not state this node, and none was copied.
- Searched the helper/main names in Mathlib, the upstream trees,
  lean/Sheaf and dag/lean_names_upstream.json: no name collision.
- Read the blueprint unit and all three detailed DAG statements. Read the local
  Stacks source at Tags 09AA, 09BM, 09BP, 099M and 099N: the first three support
  open/closed image operations; 099M and 099N give the completion formula used here.

No statement correction, missing dependency module, new node, or disputed statement
is needed. The reduction and comparison helpers belong to the item's own comparison
notion and are listed in `lean.declarations`. All data are constructed; only the
main named theorem is postponed.

## Self-check

Read the module against the node after writing. The four conjuncts reproduce all
clauses. In particular the tensor is uncompleted and the completion product leg is
fixed by quotient maps. Corrected generic derived-functor names after the first
compiler run, qualified the triangle namespace, removed the unused simp argument, and
used an explicit @id to fix the type of the product shift endomorphism.
An independent maintainer reading is supplied by the dispatch workflow, not invented
as a second worker reading here.

Validation: earlier tensor-unit expressions compiled but were too close to the
60-second limit for the required dry run. Replaced the finite derived reduction
model by the canonical multiplication cone and its functorial maps, as above.
The statement is unchanged. `scompile.py Q31 sk-lem-int-tensor` passed both
the sandbox and library-path checks cleanly (47.7 s and 33.6 s, including slot
acquisition). `deliver2.py Q31 sk-lem-int-tensor --no-push` then reported
OK: the packet passes preflight and compiles.
No global build was run, and the per-file limit was never raised.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
