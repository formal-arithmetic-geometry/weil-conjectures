## Worker report

Item: prop-exc-finite-etale-adjoint. Worker N5, stage 2, 2026-10-16.
The item module is `Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction`.
It has two named theorem statements, both with `sorry`, a finiteness instance
obtained from the published finite-coefficient theorem, and a real-data helper
transporting the recorded inverse image to the intrinsic module presentation. No claim of a
completed proof is made. The theorem docstrings contain the six-step DAG proof:
localization, finite local splitting, biproduct comparison and gluing, explicit
unit/counit and triangles, unbounded localization, and the identity compactification.

The node's statement, proof and all dependencies are unchanged. The current
published finite-level pullback interface supplies exactly the operation consumed here.
The module uses the intrinsic constant-ring module presentation already fixed by
its site and direct-image dependencies. Object universes of the pro-etale site are
u+1 and morphism universes u; these have not been identified.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in both theorems. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| n at least one | `(n : ℕ)` and exponent `n + 1` throughout. Every positive exponent is uniquely of this form; the parameter n=0 means exponent one. |
| A=O_E/varpi_E^n | `Padic.coefficientExtensionRing l E (n + 1)`, the dependency's actual quotient. The finiteness instance calls `Padic.finite_coefficientExtensionRing`; finiteness is not an extra hypothesis. |
| Arbitrary schemes V,X | `{V X : Scheme.{u}}` in the first theorem, without Noetherian, finite-type or nonemptiness assumptions. |
| ell invertible on V and X | `_hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v)` and the analogous `_hX`. These are invertibility in every local ring. |
| Finite etale e | `(e : V ⟶ X) [IsFinite e] [Etale e]`. |
| Small pro-etale module categories | `proEtaleDerivedCategory` of the recorded site module, over `proEtaleConstantRing`; the direct-image and pullback functors fix their source and target categories. |
| Module direct image exact | The first two conjuncts of `finiteEtale_proEtale_exact_derived_adjunction` are `PreservesFiniteLimits` and `PreservesFiniteColimits` of `proEtaleConstantModuleDirectImage e A`. These are exactness for this additive functor between the abelian module categories. |
| Total derived direct image computed termwise | The third conjunct is the natural isomorphism between `DerivedCategory.Q ⋙ proEtaleConstantDerivedDirectImage e A` and `(proEtaleConstantModuleDirectImage e A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q`. |
| Re_* left adjoint to e^* | The fourth conjunct is `Nonempty (proEtaleConstantDerivedDirectImage e A ⊣ finiteEtaleAdjunction_inverseImage e A)`. The direction is the reverse adjunction requested in the node. |
| Exact inverse image applied termwise | `finiteEtaleAdjunction_inverseImage` transports the recorded `ProEtale.upperStar` by the published canonical `sfIntrinsicModuleEquivalence`, then uses `mapDerivedCategory`. Thus it is exactly the same inverse image in the intrinsic constant-ring module presentation, applied termwise. Its definition contains real data and only exposes the existing additivity instances. |
| Entire possibly unbounded derived categories | The categories are ordinary `DerivedCategory` and complexes are indexed by all of ℤ; no boundedness or constructibility predicate is a binder. |
| Compact-support ambient finite-field datum | `(D : WeilConjectures.FiniteFieldDatum.{u})`, which carries p,a,q,k0,k and the algebraic-closure structure. `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` gives p≠ell. |
| V,X finite type over k | `V X : Over (Spec (CommRingCat.of D.k))`, with `[LocallyOfFiniteType V.hom] [QuasiCompact V.hom]` and the corresponding X instances. |
| e a k-morphism, finite etale | `e : V ⟶ X` in the over-category, with `[IsFinite e.left] [Etale e.left]`. The over-category morphism supplies the commuting structural maps. |
| Proper compactification c=(id_V,e) | `Compactification.ofIsProper e.left`: its defining data are intermediate scheme V, open immersion identity, and proper map e; finite implies proper by the Mathlib instance. |
| Re_!^c = Re_* | First conjunct of `finiteEtale_proEtale_identityCompactification_adjunction`: `Nonempty (sfIntrinsicCompactSupport (Compactification.ofIsProper e.left) A ≅ proEtaleConstantDerivedDirectImage e.left A)`. Equality of functors here means the natural identification in the node. |
| Re_!^c left adjoint to e^* | Second conjunct of that theorem is the requested `Nonempty (... ⊣ finiteEtaleAdjunction_inverseImage e.left A)`. Together with the first theorem's comparison this also gives its termwise interpretation. |
| Usual compactification-independent notation on the established subcategory | The identification is on the entire category for the designated compactification, hence restricts to the etale-origin subcategory. Suppression of the superscript invokes only the separately established compactification independence there, as explained in the theorem docstring. No unbounded independence assertion is added. |

Direct dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  imports: `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- Mathlib morphism definitions: `AlgebraicGeometry.IsFinite`, `Etale`,
  `LocallyOfFiniteType`, `QuasiCompact`; `IsProper.instOfIsFinite` supplies properness.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, `proEtaleConstantRing`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleConstantModuleDirectImage`, `proEtaleCoefficientInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`:
  `proEtaleConstantDerivedDirectImage`. The recorded wrapper module
  `Sheaf.Paper.SfDerivedDirectImage` is also imported.
- Recorded `AlgebraicGeometry.ProEtale.upperStar`, imported through the compatible
  smaller module `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
  The dependency's broad `Derived.Hom` import also imports the older generic
  `UpperLowerStar.Defs`; mixing it with the already published finite-coefficient
  intrinsic framework duplicates `ProEtale.lowerStarComp`. The smaller module
  supplies the very same recorded inverse-image declaration, its sheaf-pullback
  construction, adjunction, exactness and additivity. No tensor or internal Hom is
  used by this item. The owning-module helper `finiteEtaleAdjunction_inverseImage`
  only transports this fixed functor through `sfIntrinsicModuleEquivalence` and
  applies the published exact-functor derived construction.
- Delivered `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`, using published
  `sfIntrinsicExtensionByZero` and its exactness instances and the canonical
  finite-coefficient intrinsic realization equivalence.
- `WeilConjectures.Compactification.Defs`: `Compactification.ofIsProper`.

Proof imports retain `ProEt.weaklyEtale_localization`,
`SheafOfModules.localizedModuleAdjunctionIndependent` and
`SheafOfModules.localizedModuleExactIndependent`,
`AlgebraicGeometry.finite_etale_etale_local_split`, and
`SheafOfModules.existsUnique_hom_of_cover`. The compactification formula uses
the delivered intrinsic presentation instead of mixing it with the older
category-valued-sheaf lower-shriek interface.

Edge cases checked: empty V, empty X, empty fibres and zero sheet rank; disconnected
bases with varying sheet count; identity and isomorphism maps; exponent one; the
zero object and complexes unbounded in either direction. No global constant rank,
nonempty-fibre or constructibility hypothesis is present. The characteristic
restriction is imposed only where the node imposes its finite-field ambient
setting. The ordinary statement retains ell-invertibility on both schemes.

Searches (before introducing the statement):

- `msearch.py N5 prop-exc-finite-etale-adjoint leanfinder "right adjoint finite etale direct image derived pro etale sheaves"`:
  general site and etale declarations, no finite-etale pro-etale reverse derived adjunction.
- `msearch.py ... loogle "rightDerivedLowerShriek, rightDerivedUpperStar, Adjunction, DerivedCategory"`:
  no match; unknown `rightDerivedLowerShriek` in Mathlib. A fresh valid declaration query
  `CategoryTheory.Adjunction, DerivedCategory` returned zero hits.
- `msearch.py ... grep "finite.*etale.*adj|adj.*finite.*etale|finiteEtale.*Adj"`:
  no Mathlib match.
- The earlier grep with subdirectory `WeilConjectures` found no directory inside
  Mathlib; it was replaced by the valid whole-Mathlib grep above.
- `msearch.py ... leansearch "finite etale pushforward exact left adjoint inverse image unbounded derived category"`:
  search provider returned Internal Server Error; the other searches and source reads completed.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` trees, including
  `finite.*[Ee]tale`, adjunction names, direct-image and coefficient-comparison names:
  found the ordinary-etale reverse adjunction and the pro-etale ordinary pullback/
  direct-image framework, but no declaration of this pro-etale theorem.
- `rg` for this node id in the upstream project found no match.
- The blueprint source was read from the available master blueprint copy under
  `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`.
- `scompile.py --source` checked missing/stale records against the current live
  sources. The published finite-level pullback interface is now recorded on
  `def-weil-derived-pullback-tensor-hom`; all unpublished integral, rational and
  common-stage repairs from the earlier sandbox attempt have been excluded.
- Fresh prescribed searches: LeanFinder query
  `finite etale pushforward exact left adjoint inverse image unbounded derived category`
  returned eight general site/sheaf-adjunction and derived-category results;
  Loogle `CategoryTheory.Adjunction, DerivedCategory` returned zero hits;
  Mathlib grep `finite.*etale.*adj|adj.*finite.*etale|finiteEtale.*Adj` returned zero hits.
  Source-tree searches found no exact pro-etale reverse-adjunction theorem.

No STATEMENT-DISPUTED flag and no statement correction for this item.

## Dependency modules

`def-compact-support-direct-image-detailed` is repaired under §1(B), changing only
its `lean` record. The recorded `rightDerivedLowerShriekOfCompactification` is on
category-valued sheaves, whereas this item's recorded direct image and derived
categories use modules over the intrinsic constant-ring sheaf. The delivered
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` defines exactly the same
`R(c.g)_* (c.i)_!` in that presentation. Its extension by zero is the published
`sfIntrinsicExtensionByZero`, transported by the fixed constant-scalar realization;
its proper direct image is the published `proEtaleConstantDerivedDirectImage`.
The definition has real data and no postponed proof. It makes no claim of
compactification independence on all unbounded objects. The separately cited
independence, refinement comparisons and coherence remain in their stated scope.

No new nodes and no statement changes. The item node copy differs only in `lean`.
The earlier attempt's larger recursive dependency packet is archived under
`scratchpad/superseded-packet` and is not part of this delivery.

Validation: both delivered modules are compiled separately by `scompile.py`;
`deliver2.py --no-push` performs the required preflight and compilation dry run.

## Second reading by N5

I independently read the base node, both delivered Lean modules, the dependency
node records and declaration sources, blueprint order 2062 and its unit
`sk-prop-sf-rf-shriek-preservation/_section.md`, and blueprint order 1486.
I also read Stacks `proetale.tex`, section-morphism (09A5), and
`sites-modules.tex`, lemma-extension-by-zero (03DI) and
lemma-extension-by-zero-exact (03DJ), in the available literature checkout
`/home/ubuntu/work-bp/sheaf/literature/stacks-project`. The ordinary clause
is the unrestricted finite-etale assertion; the finite-type geometric
finite-field context belongs to the compact-support clause. The unit's
constructible exceptional-adjoint assertion is not being replaced by an
unbounded compactification-independence assertion.

Here is my object/hypothesis/conclusion checklist against the node, in order.
All verdicts below are pass.

| Node object, hypothesis or conclusion | Lean rendering checked and verdict |
| --- | --- |
| A prime ell | `l : ℕ` and `[Fact l.Prime]` in both statements. Pass. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. This is the coefficient dependency's general finite extension, not a fixed field or closure. Pass. |
| Positive exponent | `n : ℕ`, always used as `n + 1`. This reindexes precisely the positive integers and includes exponent one. Pass. |
| A = O_E/(varpi_E^n) | `Padic.coefficientExtensionRing l E (n + 1)`. I opened `CoefficientExtension.lean`: the ring is the quotient by the power of the ideal spanned by the recorded uniformizer. `finiteEtaleAdjunction_coefficientFinite` uses the dependency theorem `Padic.finite_coefficientExtensionRing`, so `[Finite A]` required by realization is supplied, not added to the hypotheses. Pass. |
| Arbitrary schemes V and X | `{V X : Scheme.{u}}` in the ordinary theorem, with no finite-type, Noetherian, separated, or nonemptiness binder. Pass. |
| ell invertible on both schemes | `_hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v)` and `_hX` with X. These are invertibility in every local ring, exactly the scheme condition. Pass. |
| Finite etale morphism e | `(e : V ⟶ X) [IsFinite e] [Etale e]`. I opened Mathlib's class signatures: affine finite ring maps for `IsFinite`, etale affine ring maps for `Etale`. No surjectivity or constant rank is assumed. Pass. |
| Small pro-etale sites and A-module categories | `proEtaleDerivedCategory` unfolds to the unbounded derived category of `SheafOfModules` over the ring-forgotten constant CommRingCat sheaf. The coefficient object is `ULift.{u+1,u} A`, not a completed or condensed ring. I opened `ProEtaleDerivedCategory`, `ProEtaleInverseImage`, and the realization modules. Pass. |
| The module direct image e_* | `proEtaleConstantModuleDirectImage e A`, the recorded `SheafOfModules.pushforward` through the sheafified constant-section ring map. Its source, target, scalar action, sections and maps are those of the node. Pass. |
| Direct image exact | The first and second conjuncts are `PreservesFiniteLimits` and `PreservesFiniteColimits` for that same additive direct image. Between the recorded abelian module categories these give precisely exactness. Pass. |
| Its total derived functor | `proEtaleConstantDerivedDirectImage e A` unfolds to `(proEtaleConstantModuleDirectImage e A).rightDerivedFunctor`, constructed with K-injectives. `sfFiniteDerivedDirectImage` in the recorded wrapper uses exactly this functor. Pass. |
| Computed termwise | The third conjunct identifies `DerivedCategory.Q ⋙ Re_*` with the integer-indexed termwise image followed by `DerivedCategory.Q`, by a natural isomorphism. This is the functorial termwise computation on every representative. Pass. |
| Re_* left adjoint to e^* | Fourth conjunct: `Nonempty (proEtaleConstantDerivedDirectImage e A ⊣ finiteEtaleAdjunction_inverseImage e A)`. The adjunction direction agrees with the node, and the `Nonempty` asserts existence of adjunction data, not an arbitrary choice of inverse-image functor. Pass. |
| e^* exact inverse image applied termwise | The helper's real body transports the recorded `ProEtale.upperStar` through `(sfIntrinsicModuleEquivalence X A).inverse` and `(sfIntrinsicModuleEquivalence V A).functor`, then applies `mapDerivedCategory`. I opened the upper-star construction (sheafified Kan extension along base change), its exactness instances, the canonical realization body, and `sfIntrinsicModuleEquivalence`. This is a fixed canonical transport of the recorded functor. The `letI`s expose existing additive instances only. Pass. |
| Entire possibly unbounded derived categories | Complexes have shape `ComplexShape.up ℤ`, and there is no bound or constructibility predicate on objects. Pass. |
| Additional geometric finite-field setting for compact support | `D : WeilConjectures.FiniteFieldDatum.{u}` gives p prime, q=p^a, a positive, the finite field k0 of cardinality q, and an algebraic closure k. I read its actual structure fields. `_hl : l ≠ D.p` is the required characteristic restriction; characteristic p follows from the finite-field datum. Pass. |
| Finite-type k-schemes V and X | `V X : Over (Spec (CommRingCat.of D.k))` with `LocallyOfFiniteType` and `QuasiCompact` on each structural map. I opened those Mathlib class signatures; their conjunction is finite type, without adding separatedness of the schemes. Pass. |
| e is a k-morphism, finite etale | `e : V ⟶ X` in `Over` supplies the commutation with structural maps, with `[IsFinite e.left] [Etale e.left]`. Pass. |
| Specified proper compactification (id_V,e) | `Compactification.ofIsProper e.left`. I opened its structure body: Z=V, i=identity, g=e. Finite implies proper by the existing Mathlib instance, with no new hypothesis. Pass. |
| Re_!^c = Re_* on the whole derived category | First conjunct of the compactification theorem is the natural isomorphism from `sfIntrinsicCompactSupport (Compactification.ofIsProper e.left) A` to the same `proEtaleConstantDerivedDirectImage`. Pass. |
| Re_!^c left adjoint to e^* | Its second conjunct gives the adjunction to the identical inverse-image helper; the ordinary theorem supplies termwise computation. Pass. |
| Suppress c on the already established independence subcategory | The theorem docstring states this restriction of the ambient natural identification. It adds no independence assertion outside that subcategory. This clause is interpretation using the dependency's separately stated coherence, not new adjunction data. Pass. |

Dependency-module review (H13): I read the unchanged statement of
`def-compact-support-direct-image-detailed`, its source order 1486, and the
previous `rightDerivedLowerShriekOfCompactification` construction. The previous
functor has category-valued sheaves as endpoints; the item uses intrinsic
constant-ring modules. The delivered `sfIntrinsicCompactSupport` has exactly
body `(sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
proEtaleConstantDerivedDirectImage c.g A`. I read the extension's body: it
transports the existing open-immersion sheafified extension by zero by the same
canonical realization equivalence. Thus the replacement is the specified
`R(c.g)_* (c.i)_!` in the required presentation, not another compact-support
operation or a compactification-independent choice. Its more general signature
allows a specified compactification and any finite commutative ring; substituting
the node's data gives exactly its definition. The finite-type and coefficient
context of the separately cited independence/coherence statements is not made
into extra data of the construction. The replacement has no `sorry` and its
`lean.note` identifies the precise endpoint mismatch. There are no new nodes.

Edge cases: an empty source, empty target (hence source empty), empty fibres,
rank zero, identity/isomorphism, disconnected targets and varying finite rank
are all covered; neither statement assumes a nonempty sheet set or a uniform
rank. The zero module and zero complex are included. Both directions of
unboundedness are included. `n=0` in Lean means the first positive level;
exponent zero is outside the node, not silently included as an extra case.
There is no characteristic-zero or nonempty-scheme hypothesis; the ordinary
clause asks exactly for ell to be a unit, while the compact-support clause has
p different from ell. Universe `u` is arbitrary and the existing site retains
objects in `u+1` and morphisms in `u`; coefficient sheaves use the dependency's
`u+1` lift. No equality of the site's two universes or extra smallness instance
has been imposed.

Independent one-definition searches:

- LeanFinder, `finite covering ambidextrous pushforward left adjoint pullback
  sheaf modules`: eight generic module pushforward/pullback adjunction hits;
  I checked that their direction is the ordinary pullback-left adjunction,
  not the finite-etale reverse adjunction.
- Loogle, `CategoryTheory.Adjunction, CategoryTheory.Sheaf`: twelve generic
  sheafification/localization results; no match.
- LeanSearch, `For a finite etale map pushforward of sheaves is also a left
  adjoint to inverse image`: provider unavailable (Internal Server Error),
  recorded as unavailable and not as a negative search verdict.
- Prescribed Mathlib grep, `lowerStarUpperStarAdjunctionOfIsFinite|finiteEtale.*adjunction|ambidextr`:
  no hits. Direct `rg` with finite-etale/adjunction, ambidexterity, and the new
  helper names searched Mathlib, the upstream `WeilConjectures` source, and
  project `lean/Sheaf`. It found the etale-site reverse adjunction. I opened
  `Etale.lowerStarUpperStarAdjunctionOfIsFinite`: its endpoints use the small
  etale site, so it does not state this node. The pro-etale framework supplies
  the ordinary pullback-left adjunction and the canonical transports, already
  used here, but no declaration of this reverse derived adjunction.
- I separately searched the intrinsic inverse-image and compact-support
  names/transport formulas. The existing intrinsic comparison is the
  etale-to-pro-etale comparison on one scheme, not inverse image along e.
  The existing `proEtaleConstantModulePullback` constructs a module object,
  and its map helper supplies maps, without the exact derived functor needed
  here. The item helper uses the explicitly recorded finite-level upper-star
  interface; no new mathematical notion is introduced.

I found no mismatch requiring a Lean or node change. Both node copies retain all
non-`lean` fields verbatim from the base. I mechanically checked that each
`lean.statement` occurs verbatim as its declaration signature and that every
Lean line has at most 100 characters. All variables and universes are explicitly
bound (`autoImplicit false`). Both new definitions contain real construction
data; the only postponed proofs are the two named statements of this item.
Their docstrings carry the five ordinary proof steps and the sixth
identity-compactification step, with the required source and blueprint tags.
The second reading adds this report only; the worker's correct Lean is retained.

Second-reader validation completed: prescribed `scompile.py` returned exit 0 for
both delivered modules, with no warnings or errors. The prescribed
`deliver2.py --no-push` printed `OK (dry run)` for commit `1ba4e8da2e`, confirming
preflight and compilation of this two-module packet. Delivery follows with the
same Lean and node records and this validation note.
