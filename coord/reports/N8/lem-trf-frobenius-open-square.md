## Worker report

The module `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare` states
`WeilConjectures.FiniteFieldDatum.frobenius_open_square`, with `sorry` as its only
proof. It defines no new notion. The node's mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The fixed prime, positive exponent, q = p^a, finite base field of cardinality q,
  and arbitrary fixed algebraic closure are exactly `D : FiniteFieldDatum.{u}`.
- The two arbitrary k₀-schemes are `X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))`.
  The morphism `j₀ : X₀ ⟶ Y₀` includes its compatibility with the structure maps.
  `[IsOpenImmersion j₀.left]` is exactly the open-immersion hypothesis.
- Base change uses `Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap D.k₀ D.k)))`. Its objects have underlying schemes
  `pullback X₀.hom (Spec.map ...)` and `pullback Y₀.hom (Spec.map ...)`.
  Its image of `j₀`, with `.left`, is the canonical morphism j. The two structure
  maps a_X and a_Y are `pullback.snd X₀.hom ...` and `pullback.snd Y₀.hom ...`.
- The absolute q-power scheme Frobenius is
  `Z₀.left.iterateFrobenius D.prime (D.model_characteristic Z₀.hom) D.a`.
  This is exactly the recorded dependency's a-fold p-power Frobenius. The
  equality q = p^a is part of D. `Over.homMk` uses the existing theorem
  `D.model_frobenius_over Z₀.hom` to bundle this as an endomorphism over k₀.
  Applying the above base-change functor and taking `.left` gives Φ_Z.
- `@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
  (Fintype.ofFinite D.k₀) _ _ _` is γ, the inverse of arithmetic Frobenius.
  The explicit Fintype is constructed from the datum's `Finite` instance;
  no enumeration or extra hypothesis is supplied by the caller.
  Its `.toRingHom` under `Spec.map` is g_s. `D.galoisMap Z₀.hom γ` is the
  existing canonical map id × Spec γ on the chosen fibre product.
- `m : ℕ` includes every integer m ≥ 0, including zero. `End.of` changes only
  the presentation of a scheme endomorphism, enabling its categorical power.
- The first `IsPullback` has arrows `(Φ_X^m, j, j, Φ_Y^m)` in the category of
  schemes. The second has `(g_X^m, j, j, g_Y^m)` in that same category.
  `IsPullback` includes commutativity and the universal property.
- The last two conjuncts are `g_X^m ≫ a_X = a_X ≫ g_s^m` and the corresponding
  equation for Y. Composition is written in Lean's diagrammatic order, so these
  are precisely the node's two displayed equations. No k-linearity is assumed
  of any Galois map. No finite-type hypothesis occurs anywhere in the signature.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its fields.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`; the bundled
  equivalent used here is `CategoryTheory.Over`, with `Over.homMk`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the recorded conventions use
  the existing `Over.pullback` for scheme and morphism base change. The module
  is imported through `FiniteFieldFiber`, not replaced by module pullback.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`, and the functorial induced maps.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, with its point and section formulas.
- `Mathlib.FieldTheory.Finite.Basic`: `FiniteField.frobeniusAlgEquivOfAlgebraic`.
  `WeilConjectures.Mathlib.FieldTheory.Finite.Basic` names its inverse as
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber`:
  `WeilConjectures.FiniteFieldDatum.model_characteristic` and
  `WeilConjectures.FiniteFieldDatum.model_frobenius_over` have unrestricted
  signatures. Its `relativeFrobenius` definition was read in full; the statement
  applies its very same defining functor expression directly, since the named
  wrapper unnecessarily requires finite type. No second definition is made.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.galoisMap`, `specGaloisMap_over`,
  `galoisMap_inverse` and `galoisMap_projections` give the existing unrestricted
  coefficient maps. The restricted `geometricFrobenius` wrapper is not needed.
- The two already-landed definition nodes
  `def-weil-relative-frobenius-geometric-fiber` and `def-weil-frobenius-detailed`
  were added to stmt_deps to cite these reused canonical interfaces, as allowed
  by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES). Their source modules were
  confirmed with `scompile.py --source`. Their node files are unchanged.
- Proof-dependency matches were read: `AlgebraicGeometry.isPullback_morphismRestrict`
  in `Mathlib.AlgebraicGeometry.Restrict` and
  `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion` /
  `AlgebraicGeometry.Scheme.Pullback.range_map` in the pullback modules. The
  corresponding proof-only imports are present. No unstated proof dependency
  was replaced by an arbitrary map or by a chosen existence witness.

Edge cases checked mathematically: m = 0 gives identity horizontal arrows and
identity structure equations; the empty scheme and empty open are allowed since
`model_characteristic` asks only for p to vanish, including in the zero ring;
j₀ = identity is included; arbitrary nonreduced and non-finite-type models are
included; a ≥ 1 and p prime are the fields of D. Scheme and fields all use the
same arbitrary universe u, as in the recorded datum, with no extra universe
restriction. The Galois coefficient map is the geometric inverse, not arithmetic
Frobenius, and the scalar equalities use the required contravariant Spec map.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches performed (2026-10-16):

- `msearch.py leanfinder`: “An open immersion of schemes over a finite field gives
  Cartesian squares with the base changed Frobenius and geometric Galois
  Frobenius iterates”. Eight generic hits, including
  `IsOpenImmersion.isPullback` and `Scheme.pullback_map_isOpenImmersion`;
  no exact theorem with the two maps, all iterates, and structure equations.
- `msearch.py loogle`: `AlgebraicGeometry.IsOpenImmersion,
  CategoryTheory.IsPullback`. Twelve hits, generic open-immersion pullback API;
  no complete match.
- `msearch.py grep`: `frobenius|Frobenius` in `AlgebraicGeometry` in Mathlib:
  zero hits. Direct `rg` in upstream `WeilConjectures/AlgebraicGeometry`
  found the genuine absolute Frobenius and fixed-point theorems, not this item.
- `msearch.py leansearch`: “An open immersion commutes with base changed
  Frobenius and gives a pullback square”. Service unavailable (Internal Server
  Error), recorded as unavailable, not treated as a negative search.
- Direct `rg` over `lean/Sheaf` found the landed relative Frobenius and Galois
  maps, used here, and `Sheaf.SixFunctors.FrobeniusSquareCartesian`. The latter
  was read in full: it states only the Galois square for an arbitrary map and
  m = 1, with inverses and a Cartesian structure square; it lacks the scheme
  Frobenius square and the full iterate conjunction, so is not an exact match.
- Direct `rg` for `lem-trf-frobenius-open-square` in upstream WeilConjectures,
  and for `frobenius_open_square|frobeniusOpenSquare|lem-trf-frobenius-open-square`
  in upstream, `dag/lean_names_upstream.json` and `lean/Sheaf`: no existing
  declaration. The new full declaration name does not collide.

Validation: single-file compilation uses the prescribed `scompile.py` wrapper.
The final dry delivery is run with `deliver2.py --no-push`; the second reader
will write the independent second-reading section and deliver.

## Second reading by N8

Independent second reading, 2026-10-16. I opened the sandbox node and complete
Lean module, every statement-dependency node and the declarations actually used,
and the two proof-leaf Mathlib interfaces. The node has no `statement_change`;
there are no new definition nodes or dependency modules in this delivery.

Source verification: the literature directory in the shared checkout contains
only its index files. I located and read the original blueprint at
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-trace-formula/sk-d-weil-push/lem-trf-frobenius-open-square.md`,
and Stacks `varieties.tex` and `schemes.tex` in that same literature copy.
The blueprint states both Cartesian squares for all m >= 0 and the two scalar
equations. Stacks, section Frobenii, introduces only p prime and p zero in the
structure sheaf before definition-absolute-frobenius (03SM); its naturality lemma
assumes only a morphism of characteristic-p schemes. Stacks
lemma-open-fibre-product (01JR) and definition-fibre-product (01JP) impose no
finite-type, reducedness, nonemptiness or Noetherian hypothesis. The explicit
constructions in the node agree with these passages and the blueprint proof.

Item-by-item object, hypothesis and conclusion checklist (all verdicts: exact):

1. Fixed p prime, a >= 1, q = p^a, a field k0 with q elements, and a chosen
   algebraic closure k with its embedding: `D : FiniteFieldDatum.{u}`. I read
   its structure fields in `Sheaf.Paper.FiniteFieldFiber`, including `prime`,
   `exponent_pos`, `cardinality_eq`, `card_base`, and `isAlgClosure`.
   No coefficient prime, coefficient ring, or extra finiteness enters this item.
2. Two arbitrary schemes over k0: `X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))`.
   A morphism over that base: `j₀ : X₀ ⟶ Y₀`. The over-category morphism includes
   exactly `j₀.left ≫ Y₀.hom = X₀.hom`, matching the dependency's scheme-over-base
   notion. Open immersion is exactly `[IsOpenImmersion j₀.left]`, whose Mathlib
   abbreviation refers to the locally ringed space open-immersion predicate.
3. X, Y and j are the chosen scalar extensions, using `Over.pullback` along
   `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`. I read its definition:
   the object is `Over.mk (pullback.snd _ _)` and the morphism is the universal
   lift with first projection followed by `j₀.left` and second projection fixed.
   Thus its `.left` is the required base-changed scheme map. The statement's
   `pullback.snd` terms are exactly a_X and a_Y. This is the recorded
   BaseChangeConventions interface, not module pullback.
4. Absolute p-power Frobenius and its a-fold iterate: the upstream
   `Scheme.iterateFrobenius` is constructed with identity point map and
   `s ↦ s ^ p ^ n` on every section ring. At n = D.a its section exponent is q.
   The two existing dependency theorems `model_characteristic X₀.hom` and
   `model_frobenius_over X₀.hom` (and the Y versions) have arbitrary-scheme
   signatures. They supply characteristic and base-linearity proofs, without
   assuming finite type. `Over.homMk` bundles precisely that absolute iterate;
   `Over.pullback.map` gives its prescribed base change Φ_X or Φ_Y. I read the
   dependency's `relativeFrobenius` definition: its body is this same expression.
   Expanding the existing construction here avoids importing the wrapper's
   finite-type binders and introduces no second definition.
5. γ is `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`, read in upstream
   `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`: it is the inverse of
   `frobeniusAlgEquivOfAlgebraic`, whose Mathlib formula is power by `#k₀`.
   `Fintype.ofFinite D.k₀` supplies an enumeration of D's already finite field;
   the caller need not supply another hypothesis. `Spec.map` of γ's ring map
   is exactly g_s, with the required contravariance.
6. `D.galoisMap X₀.hom γ` and its Y counterpart are g_X and g_Y. I read their
   full definition: `baseChangeMap` of the coefficient morphism, fixing the
   model projection and composing the scalar projection with `Spec γ`.
   `specGaloisMap_over` supplies only the fact that γ fixes k0. This canonical
   map, its inverse and projection theorems are unrestricted interfaces already
   recorded by `def-weil-frobenius-detailed`; no arbitrary map is quantified.
7. Every nonnegative m is `(m : ℕ)` after the models and j0. The first
   `IsPullback` has arguments `(Φ_X^m, j, j, Φ_Y^m)`, exactly the first square.
   I checked `IsPullback`'s signature and fields: it includes the commuting
   square and the limit universal property in Scheme, not in schemes over k.
8. The second `IsPullback` has arguments `(g_X^m, j, j, g_Y^m)`, exactly the
   second square, in that same category. `End.of` packages an existing scheme
   endomorphism and `^ m` is its iterate, with zeroth power the identity.
9. The third conjunct is `g_X^m ≫ a_X = a_X ≫ g_s^m`, and the fourth is its
   Y counterpart. Diagrammatic composition renders exactly the node's
   `a_X g_X^m = g_s^m a_X` and `a_Y g_Y^m = g_s^m a_Y`.
   There is no k-linearity hypothesis or conclusion on these Galois maps.

Edge cases: m = 0 gives identity horizontal maps, Cartesian identity squares,
and identity scalar equations. Empty X0, empty Y0, and an empty open image are
allowed; the upstream absolute Frobenius accepts `(p : Γ(X, ⊤)) = 0`, including
zero section rings. Nonreduced schemes and arbitrarily large non-finite-type
models are included. An identity immersion is included. The finite field's
characteristic is forced by its specified cardinality and positive exponent;
no characteristic-zero or composite-p case is silently assumed. There is no
index family or coefficient object whose zero/empty case could be excluded.
The single arbitrary universe u is exactly that of the recorded finite-field
datum and `Scheme.{u}`; there is no equality imposed on independent site or
coefficient universes, and no test-object quantifier with a smaller universe.

Independent searches, with different wording from the worker:

- LeanFinder via `msearch.py`: “The inverse image of an open subscheme under
  absolute Frobenius is the same open subscheme, and the resulting square is
  cartesian”. Eight results, chiefly ideal-sheaf pullback comparisons and
  `pullbackRestrictIsoRestrict`; no complete two-Frobenius statement.
- Loogle via `msearch.py`: `AlgebraicGeometry.Scheme.iterateFrobenius` is unknown
  to its Mathlib index, as expected for an upstream declaration. A further query
  `CategoryTheory.IsPullback.of_horiz_isIso` found the generic categorical lemma,
  useful for the Galois proof but not an existing statement of this node.
- LeanSearch via `msearch.py`: “The Frobenius of an open subscheme is the pullback
  of Frobenius on the ambient scheme”. The service returned Internal Server
  Error; this is an unavailable search, not evidence of absence.
- `msearch.py grep` for `frobenius|Frobenius` found ring and field APIs. Direct
  `rg` over Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  `lean/Sheaf` used `frobenius.*[Oo]pen|[Oo]pen.*[Ff]robenius|galoisMap|iterateFrobenius`.
  I additionally opened upstream `AlgebraicGeometry/Morphisms/Frobenius.lean`:
  `Scheme.Hom.IsFrobenius.isPullback` requires the source of the open immersion
  to be `Spec R` and addresses absolute Frobenius only, so it is a proof
  ingredient, not this statement. The existing project
  `frobenius_square_cartesian` was read in full: it covers one Galois step for
  an arbitrary morphism, with inverse and structure-square clauses, but lacks
  the scheme-Frobenius square and this all-iterate conjunction. Neither is an
  exact reuse candidate. Searches for the item id and both spellings
  `frobenius_open_square|frobeniusOpenSquare` in upstream, the upstream name
  index, and the shared project found no collision.

No mathematical mismatch, duplicate notion, missing prerequisite or unbound
binder was found. I left the correct Lean module and node signature unchanged.
The sole theorem has exactly `sorry` as its proof, and there are no definitions,
local instances, private copies or extra proved statements. Its docstring gives
the source, blueprint id, and all five node proof steps: restriction of absolute
Frobenius, inverse-image open pullback, scalar base change with its universal
lift, the inverse Galois action, and the scalar projection equations. The
proof-only imports cover the two Mathlib proof leaves. A mechanical comparison
confirmed `lean.statement` is verbatim the signature and all Lean lines are at
most 100 characters. The second reading adds this source-backed checklist and
independent search audit only; compilation and delivery checks follow below.

Validation result: `scompile.py N8 lem-trf-frobenius-open-square` compiled the
sole delivered module in both sandbox and library modes with exit code zero,
without errors or warnings. `deliver2.py N8 lem-trf-frobenius-open-square
--no-push` printed OK: preflight passed and compilation passed. The final
delivery command repeats those required checks before pushing.
