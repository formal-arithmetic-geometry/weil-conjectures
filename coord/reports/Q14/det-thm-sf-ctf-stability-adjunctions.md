## Worker report

The item is stated in `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` as
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_adjunctions`.
The only postponed proof in this delivery is this theorem.
Definitions contain real data. No statement of a DAG node was changed.

Hypotheses and conventions, checked against the node and its source:

- A commutative condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`
  with `MonObj Λ` and `IsCommMonObj Λ`. Admissibility is exactly
  `IsLocalizingAdmissibleCoefficient ℓ Λ`, including finite discrete rings, Z_l, Q_l,
  finite extensions, their valuation rings, and all continuous functions into Qbar_l.
- The standing setting is explicit: `Fact ℓ.Prime`, a field `k : Type u`,
  `Fact (ringChar k).Prime` and `Fact (ringChar k ≠ ℓ)`, and X,Y over `Spec k`.
  Their structure maps are locally of finite type, quasi-compact, and separated.
  The morphism `f` is over this same base, locally of finite type, quasi-compact,
  and separated. Locally finite type plus quasi-compact is finite type.
- Dctf is the recorded `ConstantModelConstructibleFiniteTor Λ X`, the full
  subcategory of `constantModelBoundedConstructible Λ X` intersected with
  `DerivedCategory.finiteTorAmplitude`. Neither constructibility nor the tensor
  nor the derived category is redefined.

Clause-by-clause rendering:

1. The first conjunct applies `HasCompatibleRestriction` to the recorded
   `derivedUpperStarLowerStarAdjunction Λ f`, whose functors are the total left
   derived `upperStar` and total right derived `lowerStar`. Both inclusions are
   precisely the Dctf full inclusions. In particular no preservation hypothesis
   has been added: the existence of restriction functors is in the conclusion.
2. The second conjunct quantifies over every `K : ConstantModelConstructibleFiniteTor Λ X`.
   `derivedTensorHomAdjunction Λ K.obj` is transported along the published
   `BraidedCategory.tensorLeftIsoTensorRight`, using the explicitly supplied
   `DerivedCategory.braidedCategory` on the actual module-object category.
   Thus the left functor is **- tensor K**, not K tensor -, and the right one is
   the recorded `derivedHom` at K. The derived braiding is descended from the
   Koszul braiding on K-flat complexes; no arbitrary braiding is assumed.
3. For every chosen `BoundaryCompactification f`, the final conjunct **asserts
   existence** of membership proofs `h`, a localizing right adjoint `G`, and its
   adjunction `a : localizingLowerShriek Λ c.obj.obj h ⊣ G`, together with the
   compatible restriction to Dctf. Thus the exceptional clause is not a vacuous
   implication conditional on existence of an unspecified adjoint. The left
   functor is exactly the dependency's `Rp_* D(j_!)` lift. The inclusion
   `constantModelFiniteTorToLocalizing` is the existing `ObjectProperty.ιOfLE`:
   its containment proof directly applies the defining containment condition
   in `localizingClosureProEtale`. It adds no assumption on objects or maps.
   All choices of the right adjoint are uniquely adjunction-isomorphic by the
   dependency theorem, so the existential witness is precisely the f! of that
   theorem. There is no ambient exceptional adjunction on all unbounded complexes.

The packaging definition `CategoryTheory.Adjunction.HasCompatibleRestriction`
spells out the source's phrase "as the restriction": existential functors F',G',
natural comparison isomorphisms with the included ambient functors, an adjunction,
and equality of its Hom bijection with the ambient Hom bijection after these
comparisons. The equation has type `iC M -> iC (G' N)` on both sides. Therefore
units and counits are those induced by the ambient adjunction. This is a helper
for writing this node's three clauses, not a replacement tensor, coefficient
category, or alternative restriction construction. Mathlib's existing
`Adjunction.restrictFullyFaithful` constructs precisely the witnesses required.
Both helpers are documented with this item's blueprint id and recorded in
`lean.declarations`.

Dependency declarations used (all signatures and docstrings read):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`,
  with generic `Functor.leftDerivedFunctor` and `Functor.rightDerivedFunctor`.
  This serves both pushpull dependency nodes; their composites are not copied.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `derivedTensorHomAdjunction`, `derivedHom` in the same CondensedRing namespace;
  its imported Tensor module supplies the relative derived tensor.
- `Sheaf.Paper.CondensedConstantConstructibility` (publicly imported through the
  closure): `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, and its publicly
  imported `Sheaf.Paper.LocalizingClosure.localizingClosureProEtale` (declaration
  in namespace `AlgebraicGeometry.ProEtale`).
- `Sheaf.Paper.LocalizingExceptionalAdjoint`: the recorded
  `CondensedRing.localizingLowerShriek`, `localizingLowerShriekCommShift`, and
  `exists_localizingExceptionalAdjoint`. The existing NJ theorem already takes
  `IsLocalizingAdmissibleCoefficient ℓ Λ`, exactly as required; it is imported directly.
- The recorded standing-setting module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  is publicly imported by the exceptional interface; its `compactificationOverField`
  signature and setting were read. The standing setting is rendered as explicit
  binders, and the chosen compactification is parametrized as in the dependency.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided`:
  `DerivedCategory.braidedCategory`; Mathlib `BraidedCategory.tensorLeftIsoTensorRight`.
- Mathlib `Adjunction.restrictFullyFaithful`, `ObjectProperty.ι`, `ιOfLE`, and
  `ObjectProperty.FullSubcategory` give the existing full-inclusion infrastructure.

The two item proof dependencies about direct-image and internal-Hom preservation
have no Lean record at the time of this delivery, so there is no module to import.
The proof docstring names them and explains the full restriction argument. Their
preservation conclusions are not silently assumed as hypotheses of this theorem.

Edge cases checked before writing: the empty scheme and zero complex are not
excluded; K=0 is quantified in clause 2; the identity and proper morphisms are
included in clauses 1 and 3; all six admissible coefficient types, including the
zero finite ring, remain permitted. No finite-cohomological-dimension assumption,
extra smoothness, nonemptiness, rational-coefficient restriction, or equality of
site object/morphism universes is introduced. The generic helper has independent
category object and morphism universes; the pro-etale specialization uses the
published `Scheme.{u}` and `Ab.{u+1}` convention.

Searches (2026-10-18):

- `msearch.py ... leansearch "An adjunction restricts to full subcategories
  preserved by both adjoint functors"`: eight hits, including
  `Adjunction.restrictFullyFaithful` and its compatibility lemmas; no exact
  pro-etale constructible finite-Tor statement.

- `msearch.py ... leanfinder "Restriction of the derived pullback pushforward,
  tensor internal Hom and exceptional adjunctions to constructible finite Tor
  amplitude complexes"`: eight hits, including underived sheaf/module adjunctions
  and generic derived functors; no match for this statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction.restrictFullyFaithful"`:
  the generic restriction construction and its five compatibility lemmas.
- `msearch.py ... grep "restrictFullyFaithful|RestrictedAdjunction"
  CategoryTheory/Adjunction`: the generic restriction construction and unit,
  counit, Hom-equivalence lemmas, not this pro-etale finite-Tor theorem.
- `rg` in Mathlib's Adjunction, Braided, and Closed files located the exact
  restriction and tensor-swap APIs. `rg` in upstream WeilConjectures and side
  Sheaf found finite-coefficient pro-etale trace-formula restrictions and etale
  finite-ring restrictions, which concern different categories. The published
  bounded-constructible module-object adjunctions do not restrict finite Tor and
  use the older constructibility predicate. None is this theorem.
- Searching the item id in upstream WeilConjectures and side Sheaf returned no
  matching declaration. Searching all three new declaration names in upstream,
  Mathlib/category theory, `dag/lean_names_upstream.json`, and side Sheaf found
  no existing names. Searches for derived braidings located the published
  `DerivedCategory.braidedCategory`, which is used explicitly rather than copied.

No STATEMENT-DISPUTED flag is warranted. Compilation and delivery preflight are
performed using the prescribed wrappers, with the result recorded below.

## Second reading by Q14

I reopened the item's DAG statement, its main-20261015 blueprint source, the
complete item module, and the current dependency module for this repair. This
is the assigned worker's self-check; the maintainer supplies independent review.

- The source's admissible commutative condensed ring is exactly the variable
  `Λ` with `MonObj`, `IsCommMonObj`, and `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`.
  The standing setting's prime, positive characteristic distinct from ℓ, common
  base field, separated finite-type schemes, and separated finite-type base
  morphism are the explicit `Fact`, `Over`, `IsOver`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` binders. No preservation assumption is added.
- Every occurrence of Dctf is the recorded full subcategory on
  `constantModelBoundedConstructible Λ X` intersected with
  `DerivedCategory.finiteTorAmplitude`; I checked its abbreviation in
  `CondensedConstantConstructibility.lean`. The ambient categories use module
  objects over the actual pulled-back condensed ring, not abelian sheaves alone.
- Clause 1 is the first conjunct, applying `HasCompatibleRestriction` to
  `derivedUpperStarLowerStarAdjunction Λ f`. Its source inclusion is Dctf(Y)
  and its target inclusion is Dctf(X), so the left adjoint is f* in the correct
  direction and its right adjoint is Rf*. Both are the recorded total derived
  functors on the unbounded module-object categories.
- Clause 2 is the second conjunct, with `∀ K : ConstantModelConstructibleFiniteTor Λ X`.
  I read `derivedTensorHomAdjunction`, whose left functor is K tensor -, and
  checked its transport by `ofNatIsoLeft` along `tensorLeftIsoTensorRight`.
  The resulting left functor is - tensor K and the right functor remains
  RHom(K,-). The explicit `DerivedCategory.braidedCategory` supplies the
  published Koszul braiding; no extra braiding hypothesis is introduced.
- Clause 3 is the final conjunct, for each `BoundaryCompactification f`.
  Its existential `h`, `G`, and `a : localizingLowerShriek Λ c.obj.obj h ⊣ G`
  provide the ambient exceptional adjunction and its compatible restriction.
  Thus it asserts the adjunction's existence, rather than making a conditional
  claim when a right adjoint happens to exist. Both Dctf inclusions into the
  closures are the canonical `ObjectProperty.ιOfLE`; their membership proof
  applies the defining containment condition. The existing dependency's
  uniqueness of the right adjoint identifies the existential G with f!.
- For "as the restriction" in all three clauses, I checked the two comparison
  directions `eF : iC ⋙ F ≅ F' ⋙ iD` and `eG : iD ⋙ G ≅ G' ⋙ iC` and the
  equation in `HasCompatibleRestriction`. Its right side first maps g into
  the ambient target, precomposes by eF, applies the ambient Hom equivalence,
  and postcomposes by eG. Both sides lie in `iC M ⟶ iC (G' N)`.
  This is the formula of `restrictFullyFaithful_homEquiv_apply` after mapping
  the fully faithful preimage back into the ambient category, so it fixes the
  induced Hom bijection, unit, and counit as the source requires.

The mismatch found in the returned packet was duplication of a usable dependency,
not a defect in these three clauses. I read the full current signature and
proof docstring of `exists_localizingExceptionalAdjoint` in
`Sheaf.Paper.LocalizingExceptionalAdjoint`: its coefficient binder is already
`_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`, including the all-continuous-map
algebraic-closure case. The return identifies this as NJ's repair at 90213fcc05,
already present in the parent chain of returned head 24fb8af9aa7b. The previous
report's claim that this base theorem still used `padicAlgClRingObj` was false.
I deleted `LocalizingExceptionalAdjointAdmissible.lean`, omitted the dependency
node copy so the base's NJ record is preserved, changed the item's public import
to `Sheaf.Paper.LocalizingExceptionalAdjoint`, and removed the dependency-repair
section. The item signature and its three declarations remain unchanged. There
are no new nodes, dependency modules, or statement corrections in this repair.

I rechecked the empty scheme, zero complex and K=0, identity and proper morphisms,
and all six coefficient cases, including the zero finite ring. None is excluded.
The explicit independent universes in the generic helper and the existing
Scheme/Ab size convention introduce no new size constraint. The only theorem
body in this delivery is `sorry`; both helper definitions have real data.

## Validation

The initial saved-packet dry run passed mechanically as commit 3730e005b0,
but still contained the duplicate identified by the maintainer. The repair above
removes it. The repaired one-module packet then passed `scompile.py` with exit 0, no errors
and no warnings: sandbox-path check 22.5 s, library-path check 33.8 s. Its
recorded theorem signature was checked verbatim against the file, and all Lean
lines are within 100 characters. The final `deliver2.py --no-push` checks the
rebased packet with server preflight and compilation before the required push.

## Maintainer review fix

The helper `AlgebraicGeometry.ProEtale.CondensedRing.constantModelFiniteTorToLocalizing`
duplicated the landed `AlgebraicGeometry.ProEtale.constantModelFiniteTorToLocalizing`
(Sheaf.Paper.RationalExceptionalRestriction, blueprint sk-thm-restriction): same type
and the same `ObjectProperty.ιOfLE` body (delivery-errors H4). The copy is deleted, the
module `Sheaf.Paper.RationalExceptionalRestriction` is imported, and the unchanged
statement text now names the recorded inclusion. The fixed file compiles clean with
`nt_compile.py` (49.1 s and 54.4 s, no error, no warning).
