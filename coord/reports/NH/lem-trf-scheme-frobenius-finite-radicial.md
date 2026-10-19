## Worker report

The delivery states `WeilConjectures.FiniteFieldDatum.relativeFrobenius_isFinite_isRadicial`
in `Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial`.  It renders the item's
finite-field datum by `D : FiniteFieldDatum`, the model by
`X₀ : Over (Spec (CommRingCat.of D.k₀))`, and finite type by the two recorded
class hypotheses `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.  The datum fields `p`, `prime`, `a`, `exponent_pos`, `q`,
`cardinality_eq`, `k₀`, `card_base`, `k` and the field/algebra/`IsAlgClosure`
instances supply precisely the prime, positive exponent, cardinality and fixed
algebraic closure hypotheses. The map in
the conclusion is exactly the dependency's scalar-extended q-power Frobenius
`D.relativeFrobenius X₀`, whose definition is the base change of the model
iterate Frobenius and whose affine theorem gives `a ⊗ b ↦ a^q ⊗ b`.

The conclusion has two clauses:

* `IsFinite (D.relativeFrobenius X₀)` renders that the scalar-extended Frobenius
  is finite, i.e. Mathlib's affine finite morphism predicate recorded for
  `def-weil-finite-integral-morphism`.
* `UniversallyInjective (D.relativeFrobenius X₀)` renders radiciality.  The
  recorded Mathlib match for `def-weil-radicial-morphism` is its theorem
  `tfae_universallyInjective`, which equates this predicate with injectivity on
  field-valued points, injectivity plus purely inseparable residue extensions,
  and surjective diagonal.  Thus this is the exact radicial clause, without
  adding reducedness or separatedness.

The dependency declarations used are:

* `Sheaf.Paper.FiniteFieldFiber`, declaration
  `WeilConjectures.FiniteFieldDatum` and `WeilConjectures.FiniteFieldDatum.geometricFiber`.
* `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber`, declarations
  `WeilConjectures.FiniteFieldDatum.relativeFrobenius` and its projection and
  affine characterization theorems.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`, declaration
  `AlgebraicGeometry.IsFinite`.
* `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`, declaration
  `AlgebraicGeometry.UniversallyInjective`.
* `def-weil-finite-type-morphism` is rendered by Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
* `def-pc-base-change` is rendered inside the recorded `relativeFrobenius`
  construction using `CategoryTheory.Over.pullback`; no private base-change
  notion is introduced.
* `def-weil-finite-integral-morphism` is rendered by `IsFinite`, and
  `def-weil-radicial-morphism` by `UniversallyInjective` via its recorded
  `tfae_universallyInjective` equivalence.

The proof docstring records the source route: apply the n-fold relative
Frobenius finiteness result with `n = a`; factor the iterate into one-step
relative Frobenius maps, use their universal-homeomorphism/radicial property,
identify the final twist using `c^q=c` in `k₀`, then use stability of finite and
universally injective morphisms under scalar base change.  No proof is attempted
at stage 2.

Edge cases checked: `a ≥ 1` is part of `FiniteFieldDatum`; the empty scheme and
zero rings are covered by the recorded Frobenius construction; `X₀` need not be
separated or reduced; no nonemptiness or extra characteristic hypothesis is
added; the construction handles `a = 1` and the affine formula's tensor factors.
The finite-type hypotheses are exactly the node's locally-finite-type plus
quasi-compact conditions.

Searches made:

* `msearch.py leansearch` for “The Frobenius of a finite type scheme over a
  finite field, after scalar extension to an algebraic closure, is finite and
  universally injective”: eight hits, consisting of ring/field Frobenius
  declarations and the generic `UniversallyInjective` definition and constructor;
  none is this scheme theorem.

* `msearch.py leanfinder` for “q-power Frobenius of a finite-type scheme over a
  finite field is finite and radicial after scalar extension”: eight ring/field
  Frobenius hits, including `FiniteField.frobeniusAlgHom` and
  `IsPurelyInseparable.iterateFrobeniusₛₗ`; no exact scheme theorem.
* `msearch.py loogle` for `"Frobenius", "IsFinite"`: zero hits.
* `msearch.py grep` for `Frobenius|frobenius|radicial` in Mathlib
  `AlgebraicGeometry` returned zero hits; `rg` over `WeilConjectures` and
  `lean/Sheaf` found no declaration of this finite-and-radicial scalar-extended
  result; the upstream `Scheme.Hom.IsFrobenius` results require a different
  explicit pullback witness and do not state this item.
* Read the full recorded declarations in each statement dependency and the
  source definitions of `relativeFrobenius`, `iterateFrobenius`, `IsFinite`, and
  `UniversallyInjective`.

The proof-only `Mathlib.FieldTheory.Finite.Basic` import supplies
`FiniteField.pow_card`. The general relative-Frobenius proof nodes have no Lean
record yet in the base read for this delivery, so no nonexistent proof module
is imported; the already stated absolute-Frobenius and base-change interfaces
are imported through the dependency module.

The module compiled with `scompile.py` successfully (only the expected `sorry`
warning is suppressed by the module option).  No statement correction or new
node was needed.

## Second reading by NH

I independently read the node, its three proof steps, all seven statement
prerequisite records, the delivered module, and the actual declarations used.
The source places checked are `varieties.tex` lines 7015–7180 and 7254–7295
(Tags 0CCB, 0CCD, 0CCG), and `morphisms.tex` Tags 01S3/01S4, 0472 and 01WL.
The tags file confirms the three varieties labels. Section 33.36 assumes a
prime p and characteristic p; the relative finiteness lemma assumes only
locally finite type. Neither that lemma nor the universal-homeomorphism lemma
assumes reducedness or separatedness. The finite-field specialization and
scalar extension in the node follow these sources exactly.

Object/hypothesis/conclusion checklist (each item passes):

1. Prime p: `D : WeilConjectures.FiniteFieldDatum.{u}` supplies `D.p : ℕ`
   and `D.prime : D.p.Prime`; no additional prime hypothesis is imposed.
2. Positive integer a: `D.a : ℕ` and `D.exponent_pos : 1 ≤ D.a` encode
   precisely the node's positive integer, including a = 1.
3. q = p^a: `D.q` and `D.cardinality_eq : D.q = D.p ^ D.a`.
4. Finite base field k₀ with q elements: `D.k₀ : Type u`, its `Field` and
   `Finite` instances, and `D.card_base : Nat.card D.k₀ = D.q`.
5. Fixed algebraic closure k and inclusion: `D.k : Type u`, its `Field`,
   `Algebra D.k₀ D.k`, and `IsAlgClosure D.k₀ D.k` instances. The inclusion
   used by the construction is `algebraMap D.k₀ D.k`, not an arbitrary map.
6. Model X₀ over k₀: `X₀ : Over (Spec (CommRingCat.of D.k₀))` supplies
   `X₀.left` and its specified structure map `X₀.hom`. This is the bundled
   form of the recorded `Scheme.Over` convention, not a different notion.
7. Finite type: `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`
   are exactly the two properties in `def-weil-finite-type-morphism`.
   Although 0CCD needs only the first, retaining both matches this node.
8. Geometric fibre X = X₀ ×_{k₀} k: the domain and codomain of the
   conclusion's map are `(D.geometricFiber X₀).left`. I opened
   `FiniteFieldFiber.lean`: this is `(Over.pullback (Spec.map
   (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀`, with the second
   projection as its structure morphism. The recorded base-change module's
   current source confirms this convention; no module pullback is confused
   with scheme base change.
9. Specified endomorphism Φ: both clauses use exactly
   `D.relativeFrobenius X₀`. I opened its full definition and projection and
   affine signatures, and fetched its current source through
   `scompile.py --source`. Its data apply `Over.pullback.map` to
   `X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a`,
   using `model_frobenius_over` only as the required commuting proof.
   I also opened the upstream `iterateFrobenius`: its underlying map is the
   identity and its map on sections is p^a-th power, including zero rings.
   Thus Φ is the node's scalar-extended model Frobenius. The dependency's
   tensor-map signature is `Algebra.TensorProduct.map
   (FiniteField.frobeniusAlgHom D.k₀ A) (AlgHom.id D.k₀ D.k)`, giving
   u ⊗ b ↦ u^q ⊗ b as required.
10. Finite clause: `IsFinite (D.relativeFrobenius X₀)`. I read Mathlib's
    class: affine morphism plus finiteness of every affine-open section
    map, exactly `def-weil-finite-integral-morphism`.
11. Radicial clause: `UniversallyInjective (D.relativeFrobenius X₀)`.
    I read the recorded match and Mathlib's class and
    `tfae_universallyInjective`: universal injectivity is equivalent to
    injectivity plus purely inseparable residue-field extensions. This is
    the full radicial conclusion of Tag 01S4, not just pointwise injectivity.
12. No separatedness or reducedness: neither binder nor construction requires
    either instance. The conjunction adds no other conclusion, and the
    quantifier order is datum, model, finite-type proofs, then both properties.

Dependency/interface and edge-case checks:

* No new definition node or dependency module is delivered; H12/H13 therefore
  require no new-node audit. All notions above reuse the recorded interfaces.
  The only data construction used is a real pullback of an explicit morphism;
  the postponed commuting/characteristic theorems do not choose unknown data.
* Empty X₀ is allowed. Its zero rings of sections satisfy p = 0 and the
  explicit Frobenius construction; its scalar extension remains empty and
  the stated properties hold. No `Nonempty`, `Nontrivial` or reducedness
  hypothesis is hidden in the new signature. The finite base itself is a
  field, exactly as the node requires, so a zero base field is not a case.
* Nilpotent models, for example Spec(k₀[ε]/ε²), are included: Frobenius may
  kill ε without ceasing to be finite or radicial. Nonseparated finite-type
  models are also included.
* a = 0 is excluded by the source datum, not by a new restriction. There is
  no separate n binder or index set in this statement; hence n = 0 and an
  empty index set impose no missing case. The iterated construction itself
  supports n = 0. Every prime characteristic, including p = 2, is admitted;
  characteristic zero is incompatible with the finite-field datum.
* `universe u` is explicit and arbitrary, and the bundled model and datum
  use the same `Scheme.{u}`/`Type u` convention as the dependencies. No
  smaller independent universe of test algebras or schemes is quantified
  over. Finite fields and algebraic closures can be represented in that
  universe; no bound on the size of the model or equality of independent
  site/coefficient universes is added.

Independent searches (different queries from the first reader):

* LeanSearch through msearch: “A finite type scheme over a finite field has
  finite universally injective Frobenius after extension of scalars” gave
  eight hits: finite-field Frobenius declarations and generic universal
  injectivity infrastructure, with no exact theorem.
* LeanFinder through msearch: “Finiteness of the geometric Frobenius
  endomorphism on a finite type variety over a finite field and universal
  injectivity” gave eight finite-field/ring/Galois Frobenius hits, none this
  scheme theorem.
* Loogle through msearch: `"iterateFrobenius", "IsFinite"` gave zero hits.
* `rg` independently searched upstream WeilConjectures, project `lean/Sheaf`,
  and Mathlib's AlgebraicGeometry for both orders of Frobenius and finite,
  radicial, or universally injective. I opened the upstream
  `Scheme.Hom.IsFrobenius.isFinite`,
  `isUniversalHomeomorphism_of_isPullback`, `isFinite_of_isPullback`, and
  ProEtale's `isFinite_and_isUniversalHomeomorphism_relativeFrobenius`.
  The first interfaces quantify over an arbitrary map with an explicit
  `IsFrobenius` witness and pullback/projection witnesses; the ProEtale result
  concerns a relative Frobenius between two models and a different map to a
  twist. None has the exact datum-bound `D.relativeFrobenius X₀` statement.
  Their availability does not duplicate this missing specialized statement.
  The full new declaration name is absent from `dag/lean_names_upstream.json`.

Mismatch found and repaired:

The first report said both general relative-Frobenius proof nodes lacked Lean
records. On the current base, `lem-trf-relative-frobenius-universal-homeomorphism`
now records
`Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism`.
I opened its full source, fetched its current source with `scompile.py --source`,
and checked its existential map against the node: it supplies characteristic
of the source, both canonical projections, integral and universal-homeomorphism
properties, and uniqueness, without a finite-type assumption. I added that
module as a non-public proof import, as required by stage-2 import rule 7.
`lem-trf-relative-frobenius-finite` still has no Lean record, so its absent
module is not imported. The finite/radicial permanence leaf is supplied by the
existing public Mathlib imports; `FiniteField.pow_card` has its proof import.

No mathematical statement, declaration signature, node field or existing
definition needed changing. The three-step proof docstring accurately records
finiteness at n = a, identification of the iterated relative Frobenius through
its projections and F_S^a = id, and preservation of both properties under the
specified scalar extension. The only theorem proof remains `sorry`; there
are no extra definitions, local notation/instances, unbound universes or
variables, or lines over 100 characters in the delivered module.

Validation: `scompile.py NH lem-trf-scheme-frobenius-finite-radicial
lean/Sheaf/AlgebraicGeometry/SchemeFrobeniusFiniteRadicial.lean` passed, compiling
the newly imported overlay and both sandbox/library checks under the standard
60-second limit. There were no errors or warnings. The node's `lean.statement`
was checked verbatim against the unchanged declaration signature.
