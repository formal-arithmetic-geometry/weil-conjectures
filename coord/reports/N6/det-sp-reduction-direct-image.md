## Worker report

Item: `det-sp-reduction-direct-image`. The source is the current main-20261015
blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-direct-image.md and its proof, together with the standing setting
in sk-def-sfb-dc-setting. No natural-language statement or proof plan changes.

The delivered module is `Sheaf.SecSmoothPurity.ReductionDirectImage`.
Its two postponed theorems are `AlgebraicGeometry.ProEtale.reductionDirectImage_isIso`
and `AlgebraicGeometry.ProEtale.reductionDirectImage_cocycle`. The four definition helpers now live in
`Sheaf.SecSmoothPurity.ReductionDirectImageComparison`; all are real constructions
from published functors, adjunctions and normalized comparisons.
The main theorem's docstring carries all eleven steps of the node's proof. The
cocycle docstring also explains its counit-transpose and open-unit calculation.

### Hypotheses and clauses

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ)` and `[Fact ℓ.Prime]` |
| Field k of characteristic p > 0, p different from ell | `(pchar : ℕ)`, `(hp : 0 < pchar)`, `(hℓ : pchar ≠ ℓ)`, `(k : Type u) [Field k] [CharP k pchar]` |
| X, Y, Xbar in the standing separated finite-type setting | `{X Z Y : Scheme.{u}}`, each with `.Over (Spec (.of k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map; `Z` denotes Xbar |
| All morphisms are k-morphisms | `[f.IsOver ...]`, `[j.IsOver ...]`, `[p.IsOver ...]` |
| Specified compactification f = p j | `(f : X ⟶ Y)`, `(j : X ⟶ Z) [IsOpenImmersion j]`, `(p : Z ⟶ Y) [IsProper p]`, `(hf : j ≫ p = f)` |
| Finite commutative unital coefficient rings and map | `{A B : Type u}`, `CommRing`, `Finite`, `(φ : A →+* B)` |
| Each ring killed by a power of ell | `hA` and `hB`, each `∃ n : ℕ, ∀ x, (ℓ ^ n) • x = 0` |
| Ordinary uncompleted constant-ring derived category | `proEtaleDerivedCategory X A`, the recorded standard localization of constant-ring `SheafOfModules`; no completion or condensed-module object is substituted |
| M has bounded cohomology | `hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor ... i).obj M)}`; a finite subset of the integers is bounded and a bounded integer interval is finite |
| Intrinsically constructible cohomology | `hconstructible : ∀ i, IsConstructibleProEtaleModuleSheaf X A (H^i M)`; positive finite constructible locally closed partition, local constancy and finite geometric stalks |
| Finite Tor amplitude | `hTor : HasFiniteProEtaleTorAmplitude X A M`; existential ordered common interval, testing all module sheaves in degree zero |
| K_B has its B-action | `scalarExtensionFunctor φ T`, the published K-flat scalar extension with target constant-ring module category over B |
| Rf! = Rp* j! with recorded extension by zero | `reductionCompactSupport A j p` is `(sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙ directImageConstantPush A p` |
| Specified proper comparison | `directImageScalarComparison φ p`, the published mate of `directImageScalarPullbackIso φ p` under the normalized geometric derived adjunctions; its transpose is scalar extension of the A-counit |
| Canonical extension-by-zero tensor comparison | `reductionOpenScalarIso φ j`; its middle map is the published `openScalarIso`; outside maps are the unit-preserving coordinate identification `reductionOpenModel` and its inverse |
| b is precisely proper comparison followed by Rp* of open comparison | `reductionDirectImageComparison φ j p` is the composite of the corresponding left and right whiskerings |
| Isomorphism in Dctf(Y,B) | `reductionDirectImage_isIso` asserts `IsIso` of that actual component, followed by the three Dctf conditions for its source and the same three conditions for its target; fullness of the subcategory makes this precisely an isomorphism there |
| Natural in M | `reductionDirectImageComparison` is a `NatTrans`, built by whiskering and composing the published natural comparisons. Its `.naturality u` reads `(scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j p).map u) ≫ b(M') = b(M) ≫ (reductionCompactSupport B j p).map ((scalarExtensionFunctor φ X).map u)` |
| No flatness or finite projective dimension of B/A | There are no such binders, algebra instances, perfectness assumptions or flat-model hypotheses |
| Every further finite commutative ell-primary B → C | `reductionDirectImage_cocycle` repeats all geometric and input hypotheses, adds `[CommRing C] [Finite C]`, `hC`, and `(ψ : B →+* C)` |
| Actual alpha for successive coefficient extensions | Exactly `(scalarExtensionFunctor_composition φ ψ T).hom.app K`, whose dependency fixes it uniquely on balanced K-flat tensors |
| Coefficient cocycle equation | The theorem states `alpha_(Rf!M) ≫ b_(ψ.comp φ)(M) = scalarExtensionFunctor ψ Y .map (b_φ(M)) ≫ b_ψ(M_B) ≫ Rf!_C.map (alpha_M)`, in Lean's left-to-right composition order; this is the displayed equation of the node |

### Dependency declarations used

- `sk-def-sfb-dc-setting`: its closed upstream compactification declarations were
  read, including `HasCompactification.of_isOver` and
  `ProEtale.CondensedRing.compactificationOverField` in the framework's
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  This item takes the compactification explicitly, so it uses the ordinary
  `Scheme.Over`, structure-map finiteness and separation, and `IsOver` instances,
  with `WeilConjectures.Compactification.NagataCompactification` imported. It does
  not introduce a condensed coefficient category or choose another compactification.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `FiniteCoefficientModules` and `FiniteCoefficientDerivedCategory`; their constant
  realization was read. The already-published `Scheme.proEtaleDerivedCategory` is
  their intrinsic constant-ring presentation, also the exact input category required
  by the recorded scalar extension and extension-by-zero interfaces.
- `def-weil-proetale-constructible-sheaf`: existing
  `Scheme.IsConstructibleProEtaleModuleSheaf` from
  `Sheaf.Paper.ProEtaleConstructibleSheaf`, rebound under section 1(B), as below.
- `def-weil-proetale-tor-amplitude`: existing `Scheme.HasProEtaleTorAmplitude` and
  `Scheme.HasFiniteProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`, rebound under section 1(B).
- `det-sp-scalar-extension-functor`: `ProEtale.scalarExtensionFunctor` and
  `ProEtale.scalarExtensionFunctor_composition` from
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`. Their full K-flat counit and
  balanced-tensor normalization were read, not only their names.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, canonical constant-ring
  comparison, module pullback and adjunction, and exact derived pullback. Direct
  image is their `proEtaleRingDerivedDirectImage`, with
  `proEtaleRingDerivedAdjunction`, specialized to those same constant comparisons.
- `def-weil-extension-by-zero`:
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `Scheme.sfIntrinsicExtensionByZero`; the main comparison uses this functor itself.
  `reductionOpenModel` identifies it with the existing adjunction-based presentation
  by `leftAdjointUniq`, using the published unit-preserving pullback model. Neither
  an arbitrary isomorphism nor a new extension-by-zero functor is assumed.
- Reexported through `def-sp-reduction-direct-image-comparison` (not cited as an exchange theorem):
  `Sheaf.SecSmoothPurity.DirectImageScalarExchange`, specifically
  `ProEtale.directImageScalarComparison`, `directImageConstantPush`, and
  `directImageScalarPullbackIso`. These supply the actual proper counit mate.
- Reexported through the same definition node (not cited as an open-square theorem):
  `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`, specifically
  `Scheme.openSquarePullbackModel`, whose unique section-unit normalization fixes
  the extension coordinate change. Its older exchange theorem is not invoked.
- `ProEtale.openScalarIso` and `openExtension` from the scalar dependency's public
  `Sheaf.SecSmoothPurity.OpenScalarExchange`; their right-adjoint comparisons fix
  the tensor normalization used here.

Every presently recorded proof-dependency module is imported. The two proof
nodes without a recorded module at repair time are
`lem-sp-direct-image-change-ring-transpose` and
`sk-prop-sf-rf-shriek-preservation`. The newly published
`lem-sp-direct-image-etale-mate-isomorphism` is now imported through
`Sheaf.Paper.SpDirectImageEtaleMate`. They are needed only to prove this statement;
none is assumed to define b, so there is no dependency wait or cycle. Their
mathematical roles remain explicit in the proof docstring. The new definition node depends only on the four recorded foundational interfaces;
none depends on this item. The earlier two exchange theorem citations are removed.

### Edge cases and checks

- Empty X or Y: no nonempty, inhabited, positive-dimension or surjectivity hypothesis
  occurs. Zero cohomology has empty support; the intrinsic constructibility predicate
  permits one empty stratum.
- The zero complex and zero coefficient ring: no nontriviality condition is placed
  on A, B or C; exponent zero is permitted when it kills the zero ring. Zero input
  satisfies the boundedness and Tor conditions.
- Identity coefficient maps, identity open immersion, and a proper morphism with
  the identity compactification are retained. The cocycle uses the actual alpha,
  hence includes the recorded identity/unitor case, with no unequal-level condition.
- Nonflat and infinite-projective-dimension quotients, for example
  Z/(ell^2) → Z/ell, are allowed. No tensor-invertibility assumption was inserted.
- The proof docstring keeps the finite-window argument and the bounded-below checks
  on the etale tensors. It never assumes a bounded constructible flat model or
  applies an etale fully faithful comparison to an unbounded-below tensor.
- The small pro-etale site has object universe u+1 and morphism universe u;
  the intrinsic module sections live in u+1. No equality between these site
  universes or alternate small-site model is imposed. The ring-size convention is
  precisely the published scalar extension's `A : Type u`; the rings are finite.
- Both postponed theorems have the standing and input hypotheses. The canonical
  natural transformation itself is constructed on the ambient categories, which
  supplies naturality upon restriction without additional hypotheses.

### Searches

- `msearch.py`, LeanFinder, query `compactly supported direct image commutes with
  derived extension of finite coefficients`: eight unrelated compact-support
  function results, no matching theorem.
- `msearch.py`, Loogle, query `IsIso, Functor`: zero hits; service reports unknown
  identifier `IsIso` for that query.
- `msearch.py`, Mathlib grep, `scalar.*[Cc]omparison|[Cc]oefficient.*[Cc]hange` in
  CategoryTheory: zero hits.
- `msearch.py`, LeanSearch, query `proper direct image derived tensor finite constant
  coefficients compact support`: eight results on proper finite morphisms, constant
  sheaves and unrelated compactly supported functions; no comparison theorem.
- `rg` on upstream `WeilConjectures` for this item's blueprint id: no matching
  declaration. Concept searches found the trace-formula theorem
  `nonempty_rightDerivedLowerShriek_comp_iso`; its full signature assumes both
  proper and open commutation and an arbitrary coefficient functor. It is not this
  node's canonical comparison theorem, so it cannot be an existing match.
- `rg` on `lean/Sheaf`: found `DirectImageScalarExchange` and `OpenScalarExchange`,
  which supply the maps and are reused; found `CompactSupportCoefficientChange`,
  whose invertibility theorem concerns specific DVR quotients and a finite-field
  datum. Its coefficient cocycle uses universal presentations. It does not state
  invertibility for the arbitrary finite ell-primary rings and field of this item.
- Direct source reads found the exact intrinsic constructibility and Tor predicates
  already published. They are reused through existing records, not restated.

There is no STATEMENT-DISPUTED issue and no statement correction. The earlier
stage-1 repair note is resolved and asks to preserve the statement; this delivery
leaves the source statement and the eleven-step proof split unchanged.

### Validation

The repaired two-module packet passed the required `scompile.py` wrapper without
errors or warnings. The new definition module compiled in the private overlay
(18.3 s), preliminary placement (8.6 s), sandbox (21.8 s), and installed module
path (6.9 s). The theorem module compiled in the sandbox (11.7 s) and installed
module path (2.9 s). Every individual compile stayed below the unchanged 60-second
limit. Both files bind their variables and universe explicitly and set autoImplicit
false. The definition module contains no sorry; the theorem module contains its
two expected sorry proofs. Both primary `lean.statement` fields were compared with
their file signatures and are verbatim. The item changes only `lean` and adds the
new definition node to the original `stmt_deps`; both dependency copies change
only `lean`. No global build or direct shared-source/Git mutation was performed.

## Dependency modules

`def-weil-proetale-constructible-sheaf`: lean-only section 1(B) repair to the existing
`Sheaf.Paper.ProEtaleConstructibleSheaf` declaration
`Scheme.IsConstructibleProEtaleModuleSheaf`. The current fixed-ModuleCat predicate
cannot directly accept the intrinsic `SheafOfModules` cohomology objects used by
the recorded scalar and open-extension functors. The already-published intrinsic
predicate is exactly the same node's finite positive constructible locally closed
stratification, local constancy and finite geometric stalks. No module is copied or
rewritten; the fixed-module declaration remains available. The only changed field
of this dependency is `lean`, with the reason in `lean.note`.

`def-weil-proetale-tor-amplitude`: lean-only section 1(B) repair to the existing
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` declarations
`Scheme.HasProEtaleTorAmplitude` and `Scheme.HasFiniteProEtaleTorAmplitude`.
The current fixed-ModuleCat interface cannot accept the intrinsic derived objects
of this comparison. The existing intrinsic formulation tests all degree-zero
module sheaves using K-flat tensor on all resolutions, with the same ordered
interval and existential finite-amplitude condition as the node. No new tensor,
completion, object, or test restriction is introduced. No dependency module source
is copied or changed. Only `lean`, including the explanatory `note`, changes.

## New nodes

`def-sp-reduction-direct-image-comparison` owns
`Sheaf.SecSmoothPurity.ReductionDirectImageComparison`. It introduces the comparison
package from the item's proof Steps 1-2, before invertibility is asserted. It publicly
reexports the existing definitions `directImageScalarExtension`, `directImageConstantPush`,
`directImageScalarPullbackIso`, `directImageScalarComparison`, `openExtension`, `openScalarIso`,
`openSquarePullbackModel` and its full `openSquarePullbackModel_existsUnique` characterization.
The existing names and implementations are preserved: copying those definitions would
violate one definition per notion. Its own four declarations are the moved
`reductionOpenModel`, `reductionOpenScalarIso`, `reductionCompactSupport`, and
`reductionDirectImageComparison`. The item cites this definition node, and no longer
cites the direct-image scalar exchange or open-square exchange theorem as a statement
prerequisite. Neither exchange equality nor `openScalarExchange` is used to construct b.

The new node includes the unit-preservation condition, not merely an unspecified
pullback isomorphism. With the existing declaration open, its `∃! e` quantifies over
each ring A, arbitrary scheme map f, module M, site object V, and section s. Its
component over the base change of V sends the tensor-pullback unit of s to the
intrinsic-pullback unit of s. This is exactly the equation reproduced in the new
module docstring. `openSquarePullbackModel` is the choice from that unique
characterization. `reductionOpenModel` then uses `leftAdjointUniq` under this fixed
right-adjoint comparison, rather than a bare Nonempty choice.

The new node's four cited interfaces are the ordinary finite module categories,
scalar extension, normalized ringed operations, and sheafified extension by zero.
The proper map and open comparison are defined on the entire ambient categories:
there is no properness, finiteness over a field, constructibility, or Tor hypothesis
in these definitions. The item's theorem retains all those hypotheses.

New searches (2026-10-18): LeanSearch for the canonical compact-support counit-mate
comparison returned eight ordinary ModuleCat adjunction and categorical mate hits;
LeanFinder for the unit-preserving pullback/compact-support scalar comparison returned
eight compactly supported continuous-function and test-function hits. Mathlib grep
for `reductionDirectImageComparison|openSquarePullbackModel|directImageScalarComparison`
in CategoryTheory returned zero. The same search in upstream WeilConjectures returned
zero; in lean/Sheaf it found the existing constituent definitions in the three
exchange modules, which are reused. DAG declaration searches found their theorem
nodes, and blueprint_refs search `pullback model` returned zero. The package had no
definition node. Exact tool queries and returned hit names are in the new node's
`mathlib_searches`.

## Returned points repaired

R1: the new definition interface above supplies the item's canonical comparison,
including the full unit normalization. The item module now imports it publicly.
Its `lean.declarations` lists only its two theorem conclusions; the four helper
constructions belong to the new node. The source statement and the two theorem
signatures are unchanged.

R3: both former interfaces remain available with their original signatures and
implementations. `Sheaf.Paper.ProEtaleFixedModuleConstructible` still declares
`Scheme.IsConstructibleProEtaleFixedModuleSheaf` on
`Sheaf (ProEt.topology Y) (ModuleCat.{u+1} A)` for `A : Type (u+1)`.
It still imports the intrinsic constructibility module and defines precisely the
positive finite locally closed constructible stratification, with local constancy
and finite stalks. No source is modified or removed. Likewise
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude` still
exports `ProEtale.DerivedCategory.torAmplitudeIn` and `finiteTorAmplitude` on
`DerivedCategory (Sheaf (ProEt.topology X) A)` for its general coefficient category A.
I read this live source through `scompile.py --source`; its generic monoidal-category
binders and degree-zero test convention are retained. The recorded primary bindings
select the already-existing intrinsic interfaces to type this item's cohomology;
no old declaration is renamed, removed, or retyped. Existing consumer imports and
applications retain their old declarations. Both dependency `lean.note` records now
explicitly document these preserved modules and names. Only `lean` changes in those
two node copies, checked against the current shared node files.

## Second reading by N6

R2: I reopened the item node, both final Lean files, the new definition node, and
the two dependency predicate sources for a separate reading after the refactor.
This is an actual second reading by the current worker; no other worker was started,
as the dispatcher explicitly forbids subagents. It is not claimed to be a review by
another person or agent. The maintainer supplies the independent reading.

I matched the hypotheses afresh: `Fact ℓ.Prime`; `hp` and `hℓ`; `Field k` and
`CharP k pchar`; all three `Over` structures and their finite-type/separated
structure-map instances; `IsOver` for f,j,p; open j, proper p, and `hf`; arbitrary
finite commutative A,B and their ell-power annihilators; the actual ring map φ;
boundedness, intrinsic constructibility of every cohomology sheaf, and one common
finite Tor interval for M. The cocycle repeats every one of these hypotheses and
adds the same conditions for C and ψ. No flatness, etale-origin, bounded flat model,
nonzero-ring, nonempty-scheme, or unequal-coefficient hypothesis appears.

For the conclusion I checked both endpoints of b explicitly: source is scalar
extension after the A-valued composite Rp_* j_!, target is the B-valued composite
after scalar extension on X. The first conjunct asserts invertibility of that
actual map; the next six assert boundedness, intrinsic constructibility and finite
Tor amplitude of each endpoint. Thus fullness gives the stated Dctf isomorphism.
The definition is a NatTrans, so its naturality is part of its type. In the second
theorem the source alpha is evaluated at Rf! M; the right side extends b_AB to C,
then applies b_BC to M_B, then Rf!_C to alpha_M. This is exactly the node's cocycle.

I also reread every clause of the new node against its interface: the existing
mateEquiv constructs gamma from the specified pullback isomorphism and geometric
adjunctions; the full `∃!` unit equation fixes the chosen ordinary pullback model;
`leftAdjointUniq` and termwise descent fix the open coordinate comparison;
`openScalarIso` uses the canonical restriction/pullback right-adjoint comparison;
the two outside whiskerings transport that same open comparison; and the final
whiskerings give Rp_*(e) gamma in that order. The second reading found one notation
mismatch in the new TeX description of beta: its functors had been written in Lean
composition order within conventional mathematical notation. I corrected it to
`T_Z J_j^A ≅ J_j^B T_X`. No Lean expression changed for that correction.

Empty schemes, the zero input and zero rings are still allowed. Identity j and
identity coefficient maps are retained, as is the arbitrary-ring nonflat quotient
Z/(ell^2) to Z/ell. The small site's object universe remains u+1 with morphisms u,
and coefficient-module sections u+1; the refactor adds no universe constraints.
Every declaration moved to the new module has its new owning blueprint id and
source docstring. The imported unique-normalization theorem retains its existing
DAG owner and proof docstring; no extra sorry or arbitrary data choice is added.

The repaired dry run found two record-shape issues, now fixed: because this item is
a direct blueprint node, preflight requires `blueprint.from.via = []`; and
`lean.declarations` lists only declarations physically introduced in its module.
The new record therefore lists the four moved helpers, while its `lean.note` and
module docstring identify all reexported canonical definitions and the full
unit-normalization theorem by their unchanged published names. The reexports
remain public and are used by the actual construction; no definition is copied.
The newly landed etale-mate proof dependency is now explicitly imported as well.
