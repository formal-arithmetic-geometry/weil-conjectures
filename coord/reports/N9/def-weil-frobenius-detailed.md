## Worker report

The main module `Sheaf.AlgebraicGeometry.FrobeniusDetailed` constructs the geometric
scheme Frobenius on the exact arbitrary-algebraic-closure fibre supplied by
`WeilConjectures.FiniteFieldDatum`. The dependency module
`Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber` states the previously unstated
relative construction. The absolute construction is reused from upstream, through an
`existing: true` repair of its dependency record. No field or absolute Frobenius is defined
a second time. Every theorem written here has proof `sorry`; all morphism data are explicit.

Hypotheses and clauses of the item:

- The global `(p,a,q,k₀,k)` is the recorded `D : FiniteFieldDatum.{u}`. Its `prime`,
  `exponent_pos`, `cardinality_eq`, `card_base`, field, finite, algebra and algebraic-closure
  fields supply exactly the fixed setting. In particular the closure is `D.k`, never replaced
  by `AlgebraicClosure D.k₀`.
- Arithmetic Frobenius is `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k`.
  `coe_frobeniusAlgEquivOfAlgebraic`, together with the datum's cardinality equation, gives
  `z ↦ z^q`. Geometric field Frobenius is the existing upstream
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`, defined as its inverse.
  The `Fintype.ofFinite D.k₀` in the definition body only supplies a finite enumeration.
- A finite-type k₀-scheme is `Y₀ : Over (Spec (CommRingCat.of D.k₀))`, with
  `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`. Its fibre is exactly
  `(D.geometricFiber Y₀).left`, with second projection `(D.geometricFiber Y₀).hom`.
- `geometricFrobenius D Y₀` is an `Aut` of that fibre. Its hom is `galoisMap` at the
  geometric field automorphism. `galoisMap` is the existing `baseChangeMap`, applied to
  `Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (specGaloisMap_over D σ)`.
  Thus the construction is exactly id on the model and Spec(γ) on coefficients.
- `specGaloisMap_over` expresses that σ fixes k₀. `galoisMap_projections` expresses both
  the fixed projection to the model (hence the map is over k₀) and the precise semilinearity
  equation for the second projection to Spec k.
- The inverse data are `galoisMap` at the inverse field automorphism, hence at arithmetic
  Frobenius for the geometric specialization. `galoisMap_inverse` separately states both
  composition laws; its proof fields do not choose any unspecified morphism.
- `galoisMap_affine` conjugates by Mathlib's `pullbackSpecIso` and identifies the map with
  Spec of `Algebra.TensorProduct.map (AlgHom.id D.k₀ A) σ.toAlgHom`. On pure tensors this
  is exactly `a ⊗ b ↦ a ⊗ γ(b)`. It applies to every affine open by base-change functoriality.
- The absolute map is the existing
  `Scheme.iterateFrobenius Y D.prime hY D.a`, where `Y = (D.geometricFiber Y₀).left`
  and `hY = D.model_characteristic ((D.geometricFiber Y₀).hom ≫
  Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))`.
  Its actual upstream data have identity base and p^a-power section maps. The recorded
  `iterateFrobenius_apply` and `iterateFrobenius_app_apply` identify those maps; q=p^a.
- `D.relativeFrobenius Y₀` is `Over.pullback` applied to the actual absolute q-power
  Frobenius of Y₀. `model_characteristic` provides p=0 without imposing a new hypothesis;
  `model_frobenius_over` supplies k₀-linearity. `relativeFrobenius_projections` states the
  model Frobenius on the first projection and the identity on the second, hence k-linearity.
  `relativeFrobenius_affine` explicitly states Spec of `a ⊗ b ↦ a^q ⊗ b` via the existing
  `FiniteField.frobeniusAlgHom` and tensor-product map.
- The absolute, relative and geometric maps are separate constructions. The source's
  assertion that they differ in general is a convention distinguishing their definitions,
  not a universal pairwise inequality: they agree on some schemes, notably the empty one.
  The module docstring explicitly adopts the geometric map for all blueprint operators.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (full structure and
  instance fields) and `FiniteFieldDatum.geometricFiber` (full declaration and docstring).
- `Mathlib.FieldTheory.Finite.Basic`: `FiniteField.frobeniusAlgEquivOfAlgebraic` and its
  coefficient-power formula. `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`:
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` and its inverse formula.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver` and their bundled
  equivalents `CategoryTheory.Over`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `LocallyOfFiniteType` and `QuasiCompact` from its dependency module. These render exactly
  the scheme-over-base and finite-type conventions.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions` (recorded dependency): its module
  docstring and `baseChange_morphism_projections` identify the actual chosen pullback
  conventions. `AlgebraicGeometry.baseChangeMap` from the publicly imported upstream
  `WeilConjectures.AlgebraicGeometry.PicardFunctor` is the construction used by galoisMap;
  `Over.pullback` is the scheme-base-change functor used by relative Frobenius.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.Spec`; the base-change
  comparison `AlgebraicGeometry.pullbackSpecIso` is from Mathlib.AlgebraicGeometry.Pullbacks.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`: the full `Scheme.iterateFrobenius`
  construction, `iterateFrobenius_apply`, `iterateFrobenius_app_apply`. The construction
  uses `iterateFrobeniusOfPrime`, so no nontriviality or impossible characteristic instance
  is assumed for a zero ring of sections.
- `def-weil-relative-frobenius-geometric-fiber` had no Lean record or Mathlib match; its
  exact notion is supplied in the dependency module of this delivery.

Edge cases checked: the empty scheme and empty open (zero section rings), arbitrary fixed
algebraic closures, the least allowed a=1, schemes which are not reduced, and schemes on
which the three endomorphisms coincide. The absolute construction takes the equation p=0,
not `CharP` on every section ring, so it includes zero rings. No reducedness, smoothness,
separatedness or nonemptiness is imposed. Scheme and field universes are the datum's u,
which is the same size convention as the recorded geometric fibre. The affine auxiliary
statement's Fintype argument is a choice of enumeration of a field already finite in D,
not a restriction on the datum. In the affine relative formula, the locally-finite-type
assumption is the model hypothesis; quasi-compactness of the affine Spec map is supplied
by `inferInstanceAs`, rather than made an additional hypothesis. The empty-scheme fault
is corrected below.

Searches made (all tool outputs retained in searches.jsonl):

- msearch.py leanfinder, “arithmetic and geometric Frobenius maps of finite field scheme,
  absolute and relative q-power Frobenius”: eight hits, including arithmetic field
  Frobenius and its coefficient-power formula; no scheme-level match.
- msearch.py loogle, “Scheme.iterateFrobenius, geometricFiberGaloisMap, pullback.map”:
  no hit; Scheme.iterateFrobenius is an upstream declaration, absent from the Mathlib index.
- msearch.py grep, “geometricGaloisFrobenius|iterateFrobenius”, AlgebraicGeometry: no hit.
  A grep with subdirectory WeilConjectures/AlgebraicGeometry was also attempted; that path
  is outside the tool's Mathlib root, so it is not evidence about the upstream source.
- msearch.py leansearch, “The geometric Frobenius automorphism of a scheme obtained by
  extension of scalars from a finite field”: service unavailable (Internal Server Error).
- msearch.py loogle, “Algebra.TensorProduct.map”: twelve hits, including the tensor map
  and map_tmul, used to render the affine formulas.
- Direct rg/grep of upstream WeilConjectures found the real absolute Frobenius construction,
  and `Scheme.Hom.geometricGaloisFrobenius` in AlgebraicGeometry.GeometricFrobenius. Its
  full signature restricts the closure to the type AlgebraicClosure k₀; the datum's
  arbitrary closure and chosen fibre do not have that interface. The new galoisMap is
  constructed with the existing generic baseChangeMap, rather than replacing the datum.
  The upstream TraceFormula.Frobenius file only carries IsModelFrobenius predicates and
  a different relative morphism of a supplied square; neither constructs this dependency.
- Direct rg of lean/Sheaf found no definition of these geometric/relative maps. The
  upstream node-id grep only found a mention of the convention in WeilSheaf.PoincareDuality.
  The node has no existing attachment in dag/lean_names_upstream.json. Current-source
  checks with scompile.py --source confirmed the finite-field and upstream geometric-fibre
  sources; the expected Sheaf absolute/relative module names had no published source.

The source PDF was downloaded into scratchpad and read at (1.1.7), (1.1.8) and (1.1.14).
It defines inverse arithmetic Frobenius, the action on the algebraic closure, and the
base-changed q-power model endomorphism exactly as used here.

## Dependency modules

`def-weil-relative-frobenius-geometric-fiber`: no Lean declaration or Mathlib match existed.
The delivered module states the characteristic and linearity facts the node explicitly
asserts, then constructs its morphism by applying the recorded base-change functor to the
existing absolute model Frobenius. Its projection and affine descriptions are stated.
All its characteristic/linearity proofs are named, with source and complete proof docstrings;
the data themselves are real morphisms, never choices from an unconstrained existence claim.

`def-weil-absolute-frobenius-scheme`: the recorded Lean interface was absent, but the exact
construction already exists in `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`.
Its lean-only repair records that existing declaration and its section/point formulas;
no new module or duplicate absolute construction is supplied.

## Statement corrected

Old statement (verbatim):

Fix the global finite-field datum $(p,a,q,k_0,k)$ [def-weil-finite-field-fiber]. Four Frobenius maps are attached to it.

1. The *arithmetic Frobenius* (Frobenius substitution) $\varphi_q\in\operatorname{Gal}(k/k_0)$, $z\mapsto z^q$, and the *geometric Frobenius* $\gamma=\operatorname{Frob}_q=\varphi_q^{-1}\in\operatorname{Gal}(k/k_0)$ [def-weil-frobenius-substitution].

2. For a $k_0$-scheme $Y_0$ [def-weil-scheme-over-base] of finite type [def-weil-finite-type-morphism], with $Y=Y_0\times_{k_0}k$ [def-weil-finite-field-fiber], the *geometric Frobenius automorphism*

$$
 g_Y=\operatorname{id}_{Y_0}\times_{k_0}\operatorname{Spec}(\gamma):Y\longrightarrow Y,
$$

the base change [def-pc-base-change] of $Y_0\to\operatorname{Spec}k_0$ along the $k_0$-morphism $\operatorname{Spec}(\gamma):\operatorname{Spec}k\to\operatorname{Spec}k$ [def-weil-affine-spectrum] ($\gamma$ fixes $k_0$). It is an automorphism of the scheme $Y$ over $k_0$, with inverse $\operatorname{id}_{Y_0}\times_{k_0}\operatorname{Spec}(\varphi_q)$ by functoriality of $\operatorname{Spec}$ and of the fibre product; it is not a $k$-morphism but lies over $\operatorname{Spec}(\gamma)$ (it is semilinear). On an affine open $\operatorname{Spec}A_0\subseteq Y_0$ it is $\operatorname{Spec}$ of $a\otimes b\mapsto a\otimes\gamma(b)$ on $A_0\otimes_{k_0}k$.

3. The *absolute $q$-power Frobenius* $\operatorname{Fr}^{(q)}_Y:Y\to Y$ (identity on the space, $g\mapsto g^q$ on $\mathcal O_Y$) [def-weil-absolute-frobenius-scheme].

4. The *relative Frobenius* $F_Y=\operatorname{Fr}^{(q)}_{Y_0}\times_{k_0}\operatorname{id}_k:Y\to Y$, a $k$-morphism [def-weil-relative-frobenius-geometric-fiber].

The maps $g_Y$, $\operatorname{Fr}^{(q)}_Y$ and $F_Y$ are three distinct endomorphisms of $Y$ in general. Convention: every Frobenius operator in this blueprint is induced by $g_Y$ and is geometric (Deligne's 'action of the geometric Frobenius $F\in\operatorname{Gal}(\bar{\mathbf F}/\mathbf F_q)$', $\operatorname{id}_{X_0}\times F$).

Correction: The unqualified claim that g_Y is not a k-morphism is false when Y₀ is the empty finite-type k₀-scheme. Then Y is empty and its unique endomorphism is over every base. Qualify only that remark by in general, explicitly allowing the empty scheme. The construction id × Spec(γ), its inverse, and its semilinearity equation are unchanged.

Source: Deligne, Weil II (1.1.7), pp. 150–151 and (1.1.14), p. 153. The source constructs
the action id × F for arbitrary models, including the empty model, and imposes no
nonemptiness condition. Only the unqualified remark was repaired; no definition or
hypothesis changed, and no stmt_deps, proof or proof_deps changed. This is a node of
unit null, not a blueprint unit's own statement. No citer is edited.

Complete direct-citer audit (34 nodes):

- `cor-zl-purity-smooth-proper`: holds true. Uses the same geometric cohomology eigenvalues in the purity statement.
- `def-pur-scheme-geometric-frobenius`: holds true. Uses the semilinear automorphisms and their Cartesian squares, all of which also exist on empty schemes.
- `def-trf-scheme-frobenius`: holds true. Uses both field automorphisms and the same geometric and relative scheme maps; all affine formulas remain valid.
- `def-weil-complex-weights`: holds true. Uses geometric local Frobenius eigenvalues and degrees to define weights.
- `def-weil-constant-weil-structure`: holds true. Uses the same geometric pullback of the constant coefficient object.
- `def-weil-determinant-constants`: holds true. Uses the same geometric cohomology operators to define determinants and Euler characteristics.
- `def-weil-frobenius-coefficient-twists`: holds true. Uses the same geometric map and its action on roots of unity; its coefficient semilinearity is unchanged.
- `def-weil-frobenius-cohomology-transport`: holds true. Uses geometric automorphisms and exchange maps, all defined with the same formulas.
- `def-weil-frobenius-point-transport`: holds true. Uses Spec(γ) and its inverse on Spec k, unchanged by the empty-model qualification.
- `def-weil-frobenius-square-exchange`: holds true. Uses the geometric Cartesian square and its inverse morphisms, unchanged for empty schemes.
- `def-weil-global-geometric-frobenius`: holds true. Uses γ and id × Spec(γ) to form the same ordinary and compact-support cohomology operators.
- `def-weil-ordinary-reciprocal-roots`: holds true. Uses the geometric cohomology characteristic polynomial, unchanged.
- `def-weil-smooth-proper-cohomological-family`: holds true. Uses the same geometric Frobenius on the smooth proper cohomological family.
- `def-weil-weil-sheaf-complex`: holds true. Uses the actual geometric automorphism to define pairs with an isomorphism of its pullback.
- `def-zl-frobenius-trace-series`: holds true. Uses the same geometric Frobenius convention for its trace series.
- `lem-fix-weil-operations`: holds true. Uses the geometric automorphism and its pullback to equip operations with Weil structures; no non-linearity assertion is used.
- `lem-weil-constant-weil-structure-stage-independence`: holds true. Uses the same geometric pullback and its constant Weil structure under coefficient extension.
- `lem-weil-frobenius-cohomology-transport-iso`: holds true. Uses invertibility of the geometric maps and the Cartesian Frobenius square; neither needs nonempty models.
- `lem-weil-frobenius-point-transport-natural`: holds true. Uses the same point transport along Spec(γ), without any non-linearity claim for empty models.
- `lem-weil-frobenius-square-cartesian`: holds true. Uses the explicit maps, inverses and projection formulas; its Cartesian assertion includes empty schemes and is unaffected.
- `lem-weil-local-frobenius-conjugacy-class`: holds true. Uses the Galois action and its iterations to compare stalk operators, not universal failure of k-linearity.
- `prop-duality-reciprocity`: holds true. Uses the geometric cohomological operator and its twist scalar on smooth proper geometrically connected schemes, unchanged.
- `prop-endpoints`: holds true. Uses geometric Frobenius on endpoint cohomology, unaffected by the correction to an empty-model remark.
- `prop-functional-equation`: holds true. Uses geometric Frobenius and the q-power convention in its characteristic-polynomial identity.
- `prop-poincare-pairing`: holds true. Uses geometric Frobenius and its Tate scalar on a smooth proper geometrically connected scheme.
- `prop-sf-open-closed-triangle-all-stages`: holds true. Uses functorial geometric Weil structures on the open/closed triangle, including empty pieces.
- `prop-trf-scheme-galois-comparison`: holds true. Uses the absolute/relative/Galois Frobenius comparison, not universal failure of k-linearity.
- `prop-weight-purity`: holds true. Uses the same global datum and geometric Frobenius on smooth proper cohomology.
- `prop-weil-operations`: holds true. Uses the same geometric automorphisms and exchange transformations to lift the operations.
- `prop-weil-reciprocal-roots-eigenvalues`: holds true. Uses the geometric convention for the cohomology operator whose eigenvalues are roots.
- `thm-pod-equivariance-of-the-twisted-pairing`: holds true. Uses the geometric operator, constant target datum and Tate normalization, unchanged.
- `thm-weil-deligne-purity`: holds true. Uses geometric Frobenius eigenvalues and their weights; the qualification removes no needed fact.
- `thm-weil-poincare-duality`: holds true. Uses the same geometric operator and its powers under finite base extension.
- `thm-zl-lefschetz-weil-identity`: holds true. Uses the same geometric operator in the trace/determinant identity.

## Validation

Both delivered modules compiled separately through scompile.py in dependency order,
without errors or warnings. All declaration binders and the universe are explicit.
Delivery validation uses `deliver2.py N9 def-weil-frobenius-detailed --no-push`;
the independent second reading belongs to the next worker.

The preflight signature reader starts at the `def` keyword, omitting its `noncomputable`
modifier. Each lean.statement record follows that exact keyword-to-`:=` signature.

## Second reading by N9

I read the corrected item first against Deligne, Weil II (1.1.7), pp. 150–151,
(1.1.8), p. 151, and (1.1.14), p. 153, using the PDF text in scratchpad.
The source defines arithmetic Frobenius by q-th powers, geometric Frobenius as its
inverse, the coefficient action id × F, and the model Frobenius extended to the closure.
It assumes neither a nonempty model nor reducedness. I then read both delivered modules
in full, the three delivered node records, and every direct statement dependency's
statement and recorded interface. No new definition node is introduced: both additional
node records already exist on the base, and change only their Lean records.

My independent object/hypothesis/clause inventory and match is:

1. Global p prime, a ≥ 1, q = p^a, finite field k₀ with q elements, and its fixed algebraic
   closure k with the specified inclusion. Lean: `D : WeilConjectures.FiniteFieldDatum.{u}`;
   I opened the structure in `Sheaf.Paper.FiniteFieldFiber`. Its `prime`, `exponent_pos`,
   `cardinality_eq`, `card_base`, and field/algebra/closure instance fields give exactly
   these objects and hypotheses. Verdict: exact; no replacement of D.k by a canonical
   algebraic-closure type.
2. Arithmetic field Frobenius z ↦ z^q, fixing k₀, and geometric Frobenius its inverse.
   Lean: the existing `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k` and
   `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`. I opened both definitions,
   the power formula and inverse formula. `Nat.card_eq_fintype_card` and `D.card_base`
   identify the exponent with q. The local Fintype in the definition body enumerates an
   already finite field; it adds no hypothesis. Verdict: exact, existing notions reused.
3. A finite-type k₀-scheme Y₀ and its fibre Y = Y₀ ×_{k₀} k with structure projection.
   Lean: `Y₀ : Over (Spec (CommRingCat.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]`,
   `[QuasiCompact Y₀.hom]`, and `(D.geometricFiber Y₀).left` / `.hom`.
   I opened the recorded Mathlib scheme-over-base and finite-type signatures, and the
   actual `geometricFiber` body: it is precisely `Over.pullback` of the base inclusion.
   Verdict: exact, no separatedness, smoothness, Noetherian or nonempty assumption.
4. g_Y = id on the model × Spec(γ), an automorphism over k₀, semilinear over k.
   Lean: `geometricFrobenius` is an `Aut` of this exact fibre, with hom `D.galoisMap`
   at the existing geometric field automorphism. `galoisMap` applies the recorded
   `baseChangeMap` to `Over.homMk (Spec.map …)`; I opened the underlying pullback.map
   construction in upstream PicardFunctor and the BaseChangeConventions module.
   `specGaloisMap_over` says σ fixes the inclusion of k₀; `galoisMap_projections` fixes
   the model projection and gives the coefficient Spec(σ) equation. Together with
   pullback.condition these imply the over-k₀ clause. Verdict: exact, correct variance.
5. Inverse id × Spec(φ_q). Lean: the explicit `inv` uses the inverse of γ, and
   `galoisMap_inverse` states both composition identities. The data are actual maps;
   the postponed proofs only certify these uniquely prescribed maps. Verdict: exact.
6. On every affine chart the map is Spec of a tensor b ↦ a tensor γ(b).
   Lean: `galoisMap_affine`, with arbitrary commutative D.k₀-algebra A and σ,
   conjugates the chosen pullback by `pullbackSpecIso` and uses
   `Algebra.TensorProduct.map (AlgHom.id D.k₀ A) σ.toAlgHom`. I opened the direction of
   `pullbackSpecIso`; inv then map then hom is the correct conjugation. Taking σ = γ
   and the affine chart's algebra gives the node's formula. Base-change naturality
   identifies that chart with the restriction of the global construction.
   Verdict: exact; the auxiliary formula holds more generally without altering the item.
7. Absolute q-power Frobenius on Y: identity on points and q-th powers on sections.
   Lean: existing `Scheme.iterateFrobenius Y D.prime hY D.a`, with hY supplied by
   `D.model_characteristic` applied to the composite of the fibre projection and the
   base inclusion. I opened the full upstream body and its point/section formulas:
   `base := 𝟙 _`, and `iterateFrobeniusOfPrime` on every open. The repaired dependency
   record uses this exact existing construction. Verdict: exact; no duplicate definition.
8. Relative Frobenius is the base change of absolute q-power Frobenius of Y₀ and is
   k-linear, with affine formula a tensor b ↦ a^q tensor b. Lean: `relativeFrobenius`
   applies `Over.pullback … |>.map` to that actual absolute model map.
   `model_characteristic` and `model_frobenius_over` supply its characteristic and
   k₀-linearity proofs; `relativeFrobenius_projections` gives the model map on the first
   projection and fixes the second. `relativeFrobenius_affine` is Spec of the tensor
   product of existing `FiniteField.frobeniusAlgHom` with the identity. Its Fintype
   parameter exists for every D, and quasi-compactness of an affine morphism is inferred.
   Verdict: exact. I checked this dependency module against its own full node statement
   and Deligne (1.1.14), rather than relying on its name.
9. The three maps differ in general, and blueprint Frobenius operators use the geometric
   one. Lean: the three constructions are identified in the main module docstring, and
   the convention is explicitly stated there. General distinction is not an inequality
   asserted for every Y (which would fail for the empty scheme).
   Verdict: exact convention; no spurious universal inequality was introduced.

Edge cases: the empty model and zero affine algebra are allowed; `model_characteristic`
uses p = 0 in sections, and upstream absolute Frobenius avoids an impossible characteristic
instance on a zero ring. The empty open is likewise covered. Nonreduced models are allowed.
The datum requires a ≥ 1, so a = 0 is outside this node; the reused absolute construction
itself accepts iterate n = 0. There is no index set to restrict. Field, algebra and scheme
universes are explicit u throughout, matching the recorded finite-field fibre interface;
there is no extra equality between independent universes or unbound variable. No theorem
is proved: every delivered theorem has whole proof `sorry`, source/blueprint docstring,
and the complete natural-language argument for the assertion it certifies. Every definition
has real data. No file-local notation, instance, private declaration or hidden statement let
is used.

Correction audit: the first worker's empty-scheme qualification is source-faithful and
necessary. Its `old_statement` equals the base verbatim, and I recomputed the direct-citer
set from stmt_deps/proof_deps: exactly the 34 recorded citers, none missing or extra.
I opened `def-trf-scheme-frobenius` and `def-pur-scheme-geometric-frobenius` in full.
The former uses the unchanged geometric, arithmetic and relative maps; the latter uses
the unchanged semilinear squares and factorization. Both `holds: true` verdicts are valid.
This item has unit null and the correction changes no unit statement.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: “scheme coefficient automorphism induced on a fibre product by a field
  algebra automorphism”. Eight hits, including `pullbackSpecIso` descriptions and generic
  pullback data; no exact Frobenius construction on this arbitrary closure interface.
- Loogle: `FiniteField.frobeniusAlgHom`. Eight hits, confirming the reused ring/field
  Frobenius and its power formula; no scheme-level replacement.
- msearch grep: `coefficient.*automorphism|relativeFrobenius|iterateFrobenius`.
  Hits are ring Frobenius and field results, not this scheme notion.
- LeanSearch: “Base change of the q-power Frobenius of a scheme over a finite field to
  its algebraic closure”. The service returned Internal Server Error, recorded unavailable;
  this failed search supplies no absence evidence.
- Direct rg with Galois/fibre/coefficient-action terms in Mathlib, upstream WeilConjectures
  and project lean/Sheaf: I opened `Scheme.Hom.geometricFiberGaloisMap` and
  `Scheme.Hom.geometricGaloisFrobenius`, including their binders. Both use the specific
  type `AlgebraicClosure k`, whereas D.k is an arbitrary supplied closure. Thus neither
  gives this exact dependency interface. The delivered map uses the already generic
  `baseChangeMap`, so its extension does not reconstruct the pullback mechanism.
  Absolute Frobenius is already upstream and is correctly attached with existing: true.
  No usable relative model-Frobenius construction on D's interface was found, and no
  delivered full declaration name collides with upstream or project names.

Mismatch found and repaired: the relative module cited Stacks tag 0CC8 for Frobenius
naturality. I checked the primary sources: [03SM](https://stacks.math.columbia.edu/tag/03SM)
defines absolute Frobenius; [0CC7](https://stacks.math.columbia.edu/tag/0CC7), Lemma 33.36.2,
is naturality; 0CC8 is instead the universal-homeomorphism lemma. I corrected the module
source citation to 03SM/0CC7, its characteristic docstring to 03SM, and its linearity
docstring to 0CC7. The relative node's inherited citation also has this tag typo; I
recorded the clarification in `lean.note`, respecting the dependency's lean-only edit rule.
No mathematical signature or construction needed repair, and the item signature records
remain verbatim equal to the declarations.

Second-reader validation: both modules compiled separately through scompile.py with no
errors or warnings. The delivery dry run passed preflight and compilation (9613cf2665).
