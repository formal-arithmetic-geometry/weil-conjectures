## Worker report

The module `Sheaf.SixFunctors.FrobeniusSquareCartesian` states
`WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian`. Its only theorem
proof is `sorry`; it introduces no definition or axiom. The node's statement,
statement dependencies, proof and proof dependencies are unchanged.

Hypotheses and objects, matched to the node:

- The fixed tuple `(p,a,q,k₀,k)` is the binder
  `D : WeilConjectures.FiniteFieldDatum.{u}`. The datum includes primality,
  positive exponent, `q = p^a`, cardinality of the finite base, and the chosen
  algebraic closure with its actual algebra structure. No canonical-closure
  specialization is made.
- `X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))` are arbitrary schemes with the
  specified structure maps. `f₀ : X₀ ⟶ Y₀` includes exactly the equation that
  the morphism is over the finite base. There is no finite-type, separatedness,
  reducedness, nonemptiness or smoothness hypothesis.
- The embedding `ι` is `algebraMap D.k₀ D.k`, and `u = Spec ι` is
  `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`.
  The chosen schemes `X` and `Y` are `pullback X₀.hom u` and
  `pullback Y₀.hom u`. These are the actual chosen pullbacks used in
  `D.geometricFiber` when that finite-type convention applies; no replacement
  geometric-fibre notion is defined here.
- The induced map `f` is `((Over.pullback u).map f₀).left`, exactly
  `f₀ × id_k`. The `Over.pullback` functor has this chosen pullback as its
  object part and the induced pullback map as its morphism part.
- The field automorphism `γ` is the existing
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`.
  Its `Fintype` argument is supplied explicitly as `Fintype.ofFinite D.k₀`,
  without an enumeration hypothesis or a local instance. The existing
  declaration is the inverse of arithmetic Frobenius. `g_X` and `g_Y` are
  the dependency's `D.galoisMap X₀.hom γ` and `D.galoisMap Y₀.hom γ`.
  This recorded interface is unrestricted; the convenience declaration
  `D.geometricFrobenius` would impose finite type, so it is not used.

Conclusions, matched clause by clause:

1. The first four conjuncts state the two inverse identities for each of
   `g_X` and `g_Y`, with exactly `D.galoisMap X₀.hom γ.symm` and
   `D.galoisMap Y₀.hom γ.symm` as inverses. Thus they state both that the
   maps are isomorphisms and the inverses requested in clause 1, rather than
   an unspecified isomorphism or arbitrary map.
2. The fifth conjunct is `g_X ≫ f = f ≫ g_Y`. Lean composition is applied
   left-to-right, so this is precisely `f ∘ g_X = g_Y ∘ f`.
3. The sixth conjunct is `IsPullback g_X f f g_Y`, with those four actual
   maps. The definition includes commutativity and the limiting property
   of that square. This gives precisely the isomorphism `(g_X,f)` into the
   chosen pullback: in Mathlib, `h.isoPullback : X ≅ pullback f g_Y`,
   `h.isoPullback_hom_fst` and `h.isoPullback_hom_snd` say its projections
   are `g_X` and `f`; uniqueness identifies it with `pullback.lift g_X f h.w`.
   Hence this encoding retains the specified identification, not merely
   the existence of an unrelated isomorphism of the two schemes.
4. The seventh conjunct is `IsIso (pullback.snd (𝟙 (Spec k₀)) u)`, the
   identification `Spec k₀ ×_{Spec k₀} Spec k = Spec k` by the second
   projection. The final conjunct is
   `IsPullback g_X (pullback.snd X₀.hom u) (pullback.snd X₀.hom u) (Spec γ)`.
   Its commutativity field is exactly `a_X ∘ g_X = Spec(γ) ∘ a_X`, and its
   limiting property gives the specified comparison `(g_X,a_X)`.
   Applied to the identity model, the same second-projection equation
   identifies `g_Y` with `Spec γ` through the seventh conjunct's canonical
   identification. Thus the displayed base-scheme specialization is
   included, including its structure-map square.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`, read with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.specGaloisMap_over`, `galoisMap`, `galoisMap_inverse`,
  `geometricFrobenius`, `galoisMap_projections`, `galoisMap_affine`, all read
  in full with `scompile.py --source`. In particular `galoisMap` constructs
  the actual `baseChangeMap`, so no semilinear map has been chosen arbitrarily.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`,
  `Scheme.Hom.isOver_iff`, and the bundled `CategoryTheory.Over` encoding.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, and `pullback.map`.
  The scheme `HasPullbacks` instance is imported through the dependency.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Spec.map_id`,
  `Spec.map_comp`, and `Scheme.Spec`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `IsPullback` and `IsPullback.isoPullback` with both projection equations;
  the public import of `IsPullback.Basic` exposes this standard API.
- The geometric field automorphism comes from the recorded Frobenius
  module's import `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`.

Read the source assertion in the slopmaster2 blueprint at
`def:weil-direct-image-object`, lines 2405–2425, and Deligne, Weil II,
printed pp. 151–153, (1.1.10)(i), (1.1.11), (1.1.14). The blueprint's
application uses finite-type schemes, but the node intentionally states
this elementary Cartesian fact for arbitrary models. The recorded
unrestricted `galoisMap` interface makes that statement possible as written.
The docstring records all five proof steps and their dependency nodes.

Edge cases checked mathematically: either model empty (all maps and
pullback comparisons remain the canonical maps); nonreduced models
(the coefficient action is not absolute Frobenius); identity model and
identity morphism; arbitrary models not of finite type; the base model
`Spec k₀`; every prime including 2 and exponent `a = 1`; and every fixed
algebraic closure rather than only `AlgebraicClosure k₀`. The datum already
excludes `a = 0`. All universes and binders are explicit; no site or
coefficient-size restriction is introduced.

Searches actually run:

- `msearch.py`, LeanFinder: “The geometric Frobenius square of a morphism
  of schemes over a finite field is cartesian, with inverse coefficient
  action”. Eight hits: affine-space base-change and Spec-tensor pullback
  results; no whole-item match.
- `msearch.py`, Loogle: `CategoryTheory.IsPullback.of_horiz_isIso,
  CategoryTheory.Limits.pullback.map` returned zero hits. Retried with
  `CategoryTheory.IsPullback.of_horiz_isIso`: one hit, the general ingredient
  requiring already-known invertible maps and commutativity.
- `msearch.py`, grep: `frobenius|galois`, directory `AlgebraicGeometry`.
  Thirteen hits about Galois connections; no scheme Frobenius square.
- `msearch.py`, LeanSearch: “The square of a morphism of schemes with the
  geometric Frobenius automorphisms of its scalar extensions is cartesian”.
  Service returned Internal Server Error, recorded as unavailable.
- `rg` in upstream `WeilConjectures` found
  `Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`,
  `commSq_geometricGaloisFrobenius`,
  `isPullback_geometricGaloisFrobenius_geometricFiberMap`, and
  `isPullback_geometricGaloisFrobenius` in
  `WeilConjectures/AlgebraicGeometry/GeometricFrobenius.lean`.
  Read their complete signatures and surrounding declarations. Their
  schemes use `AlgebraicClosure k` rather than the datum's arbitrary fixed
  closure and chosen fibre; they also do not jointly state all the explicit
  inverse and base-identification clauses of this node. They are not an
  exact existing declaration for the item.
- `grep -rn` for the item id in upstream `WeilConjectures` returned no hits;
  `rg` of `dag/lean_names_upstream.json` for the proposed theorem name
  returned no hits. `rg` in project `lean/Sheaf` for Frobenius/Galois names
  found no duplicate of this statement. Current dependency sources were
  additionally read with `scompile.py --source`, since the older local
  source tree does not contain these stage-2 modules.

The module compiled through `scompile.py N1
lem-weil-frobenius-square-cartesian` in both sandbox and library passes,
with no errors or warnings. No new nodes, dependency repairs, statement
correction, or disputed statements are needed.

## Second reading by N1

I independently read the sandbox node and theorem, all five statement-dependency
nodes, their actual declaration signatures and definitions, and the cited source.
No statement correction, new node or dependency module is present in this delivery.
Comparison with the read-only project node shows that only `lean` was changed.

Source reading: Deligne, Weil II, printed pp. 150--153, (1.1.7), (1.1.10)(i),
(1.1.11), (1.1.14), and blueprint `def:weil-direct-image-object`, lines
2405--2425. I read the PDF with `pdftotext` and the blueprint TeX from the
launcher's literature mirror, since these untracked literature files are absent
from the shared checkout. The coefficient automorphism is the inverse of
arithmetic Frobenius, and the scheme map acts on the closure factor. The source
application concerns separated finite-type morphisms between finite-type models;
these conditions are for the direct-image application. The node explicitly
extracts the elementary Cartesian assertion for arbitrary models, and its
five-step universal-property proof uses no such conditions. Stacks Tag 001V,
`categories.tex`, definition-fibre-products, lines 715--746, confirms the
unrestricted fibre-product universal property and uniqueness of the compatible
comparison, without additional finiteness or nonemptiness assumptions.

Object, hypothesis and conclusion inventory, with Lean rendering and verdict:

1. Fixed prime `p`, positive integer `a`, `q = p^a`, field `k₀` of cardinality
   `q`, and fixed algebraic closure `k` with its inclusion. Rendering:
   `(D : WeilConjectures.FiniteFieldDatum.{u})`. I read the current
   `Sheaf.Paper.FiniteFieldFiber` via `scompile.py --source`: its fields are
   `prime`, `exponent_pos`, `cardinality_eq`, `field_base`, `finite_base`,
   `card_base`, `field_closure`, `algebra_closure`, `isAlgClosure`.
   The embedding is `algebraMap D.k₀ D.k`. Verdict: exact; arbitrary fixed
   closure, not a specialization to `AlgebraicClosure D.k₀`.
2. Geometric field Frobenius `γ = φ_q⁻¹` fixing `k₀`. Rendering throughout:
   `@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
   (Fintype.ofFinite D.k₀) _ _ _`. I read its upstream definition, which is
   `(frobeniusAlgEquivOfAlgebraic K L)⁻¹`, and Mathlib's arithmetic
   definition and `coe_frobeniusAlgEquivOfAlgebraic`: its underlying map is
   `z ↦ z ^ Fintype.card K`. The datum identifies that cardinality with
   `q`. Verdict: exact, with the correct inverse convention; the explicit
   enumeration is derived from finiteness and adds no hypothesis.
3. Arbitrary `k₀`-schemes `X₀,Y₀` and `k₀`-morphism `f₀`. Rendering:
   `(X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))) (f₀ : X₀ ⟶ Y₀)`.
   I read `Scheme.Over`, `Scheme.Hom.IsOver`, `isOver_iff`, and the bundled
   over-category API. Its morphisms contain exactly the structure-map
   compatibility. Verdict: exact; no finite-type, separation, reducedness,
   connectedness, nonemptiness or smoothness hypothesis.
4. Scalar extensions `X,Y` and `f = f₀ × id_k`. The objects in the theorem
   are the domains of `D.galoisMap X₀.hom γ` and `D.galoisMap Y₀.hom γ`,
   namely `pullback X₀.hom u` and `pullback Y₀.hom u`, where
   `u = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`.
   Rendering of `f`: `((Over.pullback u).map f₀).left`. I opened
   `CategoryTheory.Over.pullback`: its object is the second projection and
   its map is the lift with projections `fst ≫ f₀.left` and `snd`.
   I read the recorded `pullback`, projections, `lift`, and `map` in
   Mathlib, and `Spec`, `Spec.map`, `map_id`, `map_comp`.
   Verdict: exactly the dependency's chosen fibre products and induced map.
5. `g_X = id_X₀ × Spec γ`, `g_Y = id_Y₀ × Spec γ`. Rendering:
   `D.galoisMap X₀.hom γ` and `D.galoisMap Y₀.hom γ`. I read the complete
   current `Sheaf.AlgebraicGeometry.FrobeniusDetailed` using
   `scompile.py --source`, including `specGaloisMap_over`, `galoisMap`,
   `galoisMap_inverse`, `geometricFrobenius`, `galoisMap_projections` and
   `galoisMap_affine`. The actual definition is `baseChangeMap` induced
   by `Spec.map γ.toRingHom` over the finite base; the projection theorem
   fixes the model and has the specified semilinearity. Verdict: exact.
   Using unrestricted `galoisMap` is essential: the convenience
   `geometricFrobenius` requires a finite-type model, which this node does
   not. No private or duplicate notion was introduced.
6. Conclusion 1, isomorphisms with the specified inverses. Rendering: first
   four conjuncts, the two composites of `D.galoisMap Z₀.hom γ` with
   `D.galoisMap Z₀.hom γ.symm` equal `𝟙 _`, for each of `Z₀ = X₀,Y₀`.
   Verdict: exact two-sided inverse identities, equivalent to the stated
   isomorphisms with these precise inverses, not an existential substitute.
7. Conclusion 2, `f ∘ g_X = g_Y ∘ f`. Rendering: fifth conjunct,
   `D.galoisMap X₀.hom γ ≫ f = f ≫ D.galoisMap Y₀.hom γ` with `f` expanded.
   Verdict: exact; Lean's composition order is the reverse of ordinary
   function-composition notation.
8. Conclusion 3, the Cartesian square with identification `(g_X,f)`.
   Rendering: sixth conjunct `IsPullback g_X f f g_Y`, with all maps
   expanded. I read `IsPullback`, `isoPullback`, `isoPullback_hom_fst`
   and `isoPullback_hom_snd` in Mathlib's `IsPullback.Defs`. The limiting
   cone uses precisely `g_X,f`; its comparison to `pullback f g_Y`
   projects to these maps, so uniqueness identifies it with
   `pullback.lift g_X f h.w`. Verdict: exactly the specified comparison
   being invertible, including its identification, not an unrelated iso.
9. Base specialization `Y₀ = Spec k₀`, `Y ≅ Spec k`, `g_Y = Spec γ`,
   and the Cartesian structure-map square. Rendering: seventh conjunct
   `IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of D.k₀))) u)` gives the
   particular identification through the second projection; the last
   conjunct is `IsPullback g_X (pullback.snd X₀.hom u)
   (pullback.snd X₀.hom u) (Spec.map (CommRingCat.ofHom γ.toRingHom))`.
   Its commutativity is exactly the requested equation with `a_X`.
   For the identity model, `galoisMap_projections` gives
   `g_Y ≫ b_Y = b_Y ≫ Spec γ`, so this particular identification conjugates
   `g_Y` to `Spec γ`. The same pullback uniqueness identifies the
   scalar-extended structure morphism with `a_X`. Verdict: the complete
   specialization is retained; no extra arbitrary choice or restriction.

Edge cases: an empty source model is allowed; when the target model is empty,
a morphism to it forces the source to be empty, and the theorem adds no
incompatible inhabitedness condition. Nonreduced schemes are allowed because
these maps act only on coefficients. The identity morphism and identity/base
model are included; the seventh conjunct uses that exact model. All primes,
including 2, and `a = 1` are allowed. `a = 0` is excluded by the fixed datum,
as it is in the node; there is no separate iterate `n` or index set to restrict.
There is no zero ring in the fixed field datum; the zero affine model is the
empty-scheme case. Every universe is explicitly bound by `universe u` and
`FiniteFieldDatum.{u}`: the fields and schemes use the dependency's common
universe at arbitrary `u`, with no added universe equation or small test-object
quantifier. No coefficient category, site or limit index is present.

Independent searches (queries differ from the first reader's semantic query):

- `msearch.py`, LeanFinder: "Naturality of scalar extension with respect to
  a coefficient field automorphism yields an isomorphism of pullback squares".
  Eight results about algebra pushouts, scalar extension and differentials;
  no scheme Frobenius-square statement.
- `msearch.py`, Loogle: `CategoryTheory.IsPullback.of_horiz_isIso`.
  One result, read in `IsPullback.Basic`: it assumes both horizontal maps
  invertible and the square already commutative, so supplies only the
  Cartesian ingredient, not the inverse/naturality/base clauses.
- `msearch.py`, LeanSearch: "Base change of a scheme morphism commutes with
  a field automorphism and gives a cartesian square". Service returned
  Internal Server Error and the wrapper recorded it unavailable; no
  conclusion about absence is drawn from this failed search.
- `rg` over Mathlib algebraic geometry, project `lean/Sheaf`, and upstream
  `WeilConjectures`, using `coefficient action`, `semilinear`, `GaloisMap`,
  Cartesian/Frobenius combinations, and then the narrower
  `isPullback.*Frobenius|frobenius_square_cartesian|def galoisMap|def geometricFrobenius`.
  Read upstream `GeometricFrobenius.lean` in full. Its
  `geometricFiberMap_comp_geometricGaloisFrobenius`,
  `commSq_geometricGaloisFrobenius`,
  `isPullback_geometricGaloisFrobenius_geometricFiberMap` and
  `isPullback_geometricGaloisFrobenius` concern `AlgebraicClosure k`, not
  this datum's arbitrary closure; no one declaration has the whole node's
  explicit inverse/base-identification bundle. The other match in
  `Morphisms/Frobenius.lean` concerns power Frobenius and open immersions,
  a different map and square. `SixFunctors/Etale/GeometricFrobenius.lean`
  uses the canonical-closure square for exchange functors, rather than
  stating this node. Project hits give the already-used dependency module.
  No full-item duplicate or name collision was found; the item id and
  proposed theorem name also have no upstream-name-table or upstream hit.

H5/H6/H8/H9 inspection: this module contains exactly one named theorem,
whose whole proof is `sorry`, and no definitions, instances, local notation,
private declarations or axioms. Its module and declaration docstrings carry
both the source and this blueprint id. The proof docstring follows all five
node proof steps: inverse Spec maps, inverse fibre-product maps, naturality,
explicit inverse `r ≫ g_X⁻¹` to the comparison, and the base specialization.
All five statement/proof dependencies have their actual recorded interfaces
available through the imports. Every Lean line is at most 100 characters;
no variable or universe is unbound. A direct textual comparison confirms
that `lean.statement` equals the theorem signature verbatim.

Mismatches and changes: none found in the Lean statement or node. I retained
both unchanged and added only this independent second-reading section.

Validation: independently reran `scompile.py N1
lem-weil-frobenius-square-cartesian` on the delivered module. Both the sandbox
pass (4.2 s) and the library pass (48.8 s) completed with exit code 0,
without errors or warnings, under the default 60-second per-file limit.
