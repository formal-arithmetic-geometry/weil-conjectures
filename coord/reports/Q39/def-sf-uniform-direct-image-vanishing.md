## Worker report

Defines `AlgebraicGeometry.Etale.UniformDirectImageVanishing` in
`Sheaf.Paper.UniformDirectImageVanishing`. This is a real Prop-valued definition,
with no theorem and no `sorry`. The node's statement and dependencies are unchanged.

Source read: the master blueprint definition `def-sf-uniform-direct-image-vanishing.md`,
order 1788, and its parent `_section.md`, in
`sec-smooth-purity/sk-prop-sf-fullcd-etale-origin`. The shared checkout lacks these
literature files; the identical master blueprint source is available in the local
`work-bp/sheaf/literature/blueprint/master/blueprint` archive. The definition asks for
vanishing for every module sheaf on the small etale site, not constructibility or
pro-etale vanishing. Also read the seven statement-dependency nodes and the signatures
and docstrings of the declarations below.

Hypotheses and clauses, in source order:

- The global tuple `(p,a,q,k₀,k)` is `(D : WeilConjectures.FiniteFieldDatum.{u})`.
  Its fields require primality, positive a, q = p^a, cardinality q for k₀, and a
  fixed algebraic closure k of k₀. No new version of this datum is introduced.
- The coefficient prime is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- A finite extension E/Q_l is `(E : Type (u + 1)) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- Positive level n is `(n : ℕ+)`, equivalent to a natural integer at least one.
  The coefficient ring throughout the body is precisely
  `Padic.coefficientExtensionRing l E (n : ℕ)`. Its definition is the quotient
  of `coefficientExtensionIntegers` by the nth power of the principal ideal of
  `coefficientExtensionUniformizer`. Thus it uses the dependency's fixed choice
  of uniformizer, as the source permits; it is not an arbitrary finite ring.
  The dependency's `finite_coefficientExtensionRing` supplies the stated
  positive-level finiteness. Changing the choice does not change the ideal,
  as the dependency node explains.
- X and Y are `Scheme.{u}` with `Over (Spec (CommRingCat.of D.k))` structures.
  Each structure morphism has both `LocallyOfFiniteType` and `QuasiCompact`.
- f is `(f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
  `IsSeparated` means that its diagonal is a closed immersion. Properness is
  not required. The source introduces a scheme morphism, so no additional
  compatibility equation with the two structure morphisms is imposed.
- The fixed nonnegative integer bound is `(N : ℕ)`, outside the quantifier
  over M. There is no existential quantifier for a bound.
- Every A-module sheaf is quantified by
  `∀ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` with the displayed
  coefficient quotient substituted for A. This is the project's standard
  encoding of modules over the constant ring sheaf; there is no constructibility,
  finite-generation, or separate torsion assumption on M.
- Every integer degree is `(r : ℤ)` with `(N : ℤ) < r`. The body is
  `IsZero (higherDirectImage A f r M)`, a zero object of the target module-sheaf
  category, not `IsZero` on its underlying type. The existing higher direct image
  is exactly `Plus.homologyFunctor` applied to bounded-below derived lower star
  of `Plus.singleFunctor ... 0`, namely H^r(Rf_*(M[0])).
- The statement's torsion observation follows from the finite quotient having
  positive additive characteristic: that integer kills every module. It is an
  explanation of the input quantifier, not another condition of UDV. Similarly,
  the reference to FIN is an analogy only; no FIN hypothesis or constructibility
  or base-change clause occurs in the definition.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including
  its registered field and algebraic-closure instances.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public import
  `Sheaf.NumberTheory.Padics.CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  `Padic.coefficientExtensionIdeal`, and `Padic.coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imports:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its imports:
  `AlgebraicGeometry.IsSeparated` (the node's separatedness clause, not IsProper).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, with
  `Scheme.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, and
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` already packages their
  required cohomology as `AlgebraicGeometry.Etale.higherDirectImage`, used directly.
- `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness`:
  `AlgebraicGeometry.ProEtale.ConstructibleDirectImageFiniteness` and its helpers
  were read and imported for the source's FIN comparison. This is not a clause
  of UDV and introduces no restriction to constructible sheaves.

Edge cases checked: N = 0 asks only for positive-degree vanishing, and r = N
is excluded by strict inequality. Negative degrees cannot exceed this nonnegative
bound. n = 1 is included, while n = 0 is excluded by the source's positive-level
condition. The zero sheaf and empty schemes are allowed. M ranges over all sheaves,
including those with arbitrarily large stalks in the prescribed coefficient universe;
no Finite/constructibility restriction is made on M. The scheme universe is u and
module objects live in u+1, exactly as the existing etale direct-image API requires;
the finite extension E and its finite quotient are placed in u+1 without equating
site object and morphism universes. The selected prime can be any prime unequal
to p. No bound or vanishing under base change is claimed.

Searches actually run:

- `msearch.py ... leanfinder "Uniform vanishing of higher direct images of all module
  sheaves on the small etale site above a fixed bound"`: eight hits, including
  `DerivedCategory.isLE_iff` and one-object t-structure vanishing results. Read
  `TStructure.lean` lines 107-122; no all-sheaf uniform predicate.
- `msearch.py ... loogle '"rightDerived", "isZero"'`: one hit,
  `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`. Read its
  signature/docstring at `RightDerived.lean` lines 153-158; it only treats
  injective input objects, not the required all-input predicate.
- `msearch.py ... grep 'Uniform.*Vanishing|uniform.*vanish|cohomologicalDimension'`:
  zero Mathlib hits.
- `rg` of `WeilConjectures` and `lean/Sheaf` for the node id and
  `Uniform.*Vanishing|uniform.*vanish`: no matching predicate; the upstream
  stability/direct-image module mentions uniform vanishing in a theorem's
  docstring, but its conclusion is preservation of constructible Tor amplitude.
- `grep -rn 'def-sf-uniform-direct-image-vanishing' WeilConjectures`: zero hits.
- `rg` of `dag/lean_names_upstream.json` for `UniformDirectImageVanishing`,
  `Uniform.*DirectImage`, and `higherDirectImage`: no uniform predicate;
  higher-direct-image results concern other statements.
- Source inspection of `SmoothBaseChange.Defs.lean` found the canonical existing
  `Etale.higherDirectImage` at lines 111-116. It is used without redefining it.

No statement dispute, correction, new node, or dependency repair was needed.
Verification: `scompile.py Q39 def-sf-uniform-direct-image-vanishing` passed
cleanly for the delivered module, both sandbox and library compilation. The module
has no lines exceeding 100 characters, and the node record contains its exact
verbatim signature. The required `deliver2.py --no-push` check is the final step;
the second reader will supply the independent reading and perform delivery.

## Second reading by Q39

Verdict: repaired H4 and use the existing published declaration
`AlgebraicGeometry.Etale.HasUniformDirectImageVanishingLE`, module
`WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`. Removed the
sandbox module `lean/Sheaf/Paper/UniformDirectImageVanishing.lean`, changed only
the item's `lean` record, and retained the node's statement and dependencies.
The preceding worker's claim of absence is superseded by this reading.

Source reading: opened the exact archived master blueprint file
`sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/def-sf-uniform-direct-image-vanishing.md`
(order 1788) and its parent `_section.md` in the local `work-bp/sheaf/literature`
archive. This is a blueprint definition, not a Stacks-tagged theorem. Its
standing setting is the global finite-field datum, positive finite coefficient
stage, and separated finite-type morphism of finite-type k-schemes. Its parent
unit discusses proper maps and pro-etale base changes in its proposition;
those are not additional conditions of the UDV definition. The node accurately
expands the blueprint definition. No statement correction is needed.

I opened the node, the whole worker module, all seven statement-dependency
nodes, and the declarations below. Independently read the existing declaration
at lines 65-78 of the shared upstream module, including its ambient coefficient
binder, then fetched its current published source with
`scompile.py --source WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`.
The server source agrees. This module is absent from the older local
slopmaster2 source checkout: searching that checkout alone missed it.

Objects, hypotheses, and conclusion, item by item:

1. Global tuple `(p,a,q,k₀,k)`, q = p^a and fixed algebraic closure: the
   dependency's `WeilConjectures.FiniteFieldDatum.{u}` has fields `p`, `a`, `q`,
   `prime`, `exponent_pos`, `cardinality_eq`, `k₀`, `card_base`, `k`, and
   `[IsAlgClosure k₀ k]`. Read its actual structure in
   `Sheaf.Paper.FiniteFieldFiber`. PASS. In the existing predicate this remains
   the ambient setting in which the node uses f and A; it is not a clause of
   vanishing and needs no duplicate predicate with an unused D parameter.
2. Prime l different from p: the specialization uses `(l : ℕ) [Fact l.Prime]`
   and the node's hypothesis `l ≠ D.p`. PASS. These specify the permitted
   coefficient stage; the existing definition does not require an additional
   characteristic assumption and therefore imposes no stronger condition.
3. Finite extension E/Q_l, valuation ring, and chosen uniformizer: read
   `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
   `coefficientExtensionIdeal`, and `coefficientExtensionRing` in
   `Sheaf.NumberTheory.Padics.CoefficientExtension`. E has `[Field E]`,
   `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`. The ring is
   the actual quotient by the nth power of the principal uniformizer ideal.
   PASS; neither an arbitrary map nor a hollow coefficient object is used.
4. Positive n and finite local stage A: specialize the existing ambient
   `(Λ : Type (u + 1)) [CommRing Λ]` to
   `Padic.coefficientExtensionRing l E (n : ℕ)` with `n : ℕ+`. Read the
   positive-level `finite_coefficientExtensionRing` signature and docstring
   in the dependency's recorded module. PASS. The existing predicate accepts
   this commutative ring directly and does not demand a new finiteness,
   Noetherian, topological, or constructibility instance.
5. Finite-type k-schemes X,Y: use `{X Y : Scheme.{u}}` with the recorded
   `Over (Spec (CommRingCat.of D.k))` structures and `LocallyOfFiniteType`
   and `QuasiCompact` on each structure morphism. Read the Mathlib class
   signatures in `Morphisms.FiniteType` and `Morphisms.QuasiCompact`. PASS.
   These are ambient restrictions on the schemes in this node, not clauses
   of the predicate. Its general X,Y binders cover every such pair.
6. Separated finite-type f:X→Y: the existing `(f : X ⟶ Y)` is exactly that
   morphism, used in the node with `[LocallyOfFiniteType f] [QuasiCompact f]`
   and `[IsSeparated f]`. Read `IsSeparated` in `Morphisms.Separated`: its
   field is `IsClosedImmersion (pullback.diagonal f)`. PASS. No properness
   is imposed. A general definition usable on these f is not a change to
   the node's geometric setting.
7. Fixed nonnegative bound: existing `(N : ℕ)` is outside both quantifiers
   in the body. It represents precisely an integer N≥0. PASS; no existential
   bound and no dependence on M.
8. Every A-module sheaf on the small etale site: the body is
   `∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ...`.
   Read the recorded `Scheme.smallEtaleTopology` definition and its
   jointly-surjective-cover characterization. PASS. Module-valued sheaves
   give the standard constant-ring module encoding. No finite stalk,
   constructible, or separate torsion restriction appears.
9. Every integer r>N: existing `(q : ℤ), (N : ℤ) < q → ...` has exactly the
   node's quantifier and strict inequality; the worker's r and existing q
   differ only by a bound-variable name. PASS.
10. Vanishing is the zero target sheaf: existing
    `IsZero (Etale.higherDirectImage Λ f q M)` is verbatim the worker's body
    after coefficient substitution. Read `higherDirectImage` in
    `SmoothBaseChange.Defs`: `Plus.homologyFunctor` of bounded-below derived
    lower star applied to `Plus.singleFunctor ... 0`. Read the recorded
    `lowerStar` in `UpperLowerStar.Defs` (objectwise pullback evaluation) and
    `rightDerivedLowerStarPlus` in `Derived.UpperLowerStarCoherence`.
    PASS; these are the node's H^q(Rf_*(M[0])) in the module-sheaf category,
    not a pro-etale or abelian-only replacement and not IsZero of a bare Type.
11. Every input is torsion: the positive finite quotient has finite additive
    characteristic, which kills any module. PASS as the node's explanatory
    observation; it does not add a quantified hypothesis to UDV.
12. FIN analogy: opened the recorded
    `ProEtale.ConstructibleDirectImageFiniteness` and its two quantified
    clauses in `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness`.
    It concerns constructible pro-etale sheaves; only its fixed-bound
    vanishing clause is being compared. PASS. UDV has no constructibility,
    base-change, or existence-of-bound clause. It does not invoke FIN as
    a condition and needs no dependency repair.

The existing declaration is more general in its allowed ring and morphism
parameters, but its specialized defining formula is exactly equal to the
node's predicate. It asserts no vanishing theorem for these more general
parameters. Consequently using it adds no hypothesis, drops no conclusion,
and requires no statement_change. The `lean.statement` is copied verbatim
from its source (`def Etale.HasUniformDirectImageVanishingLE ... : Prop`);
its ambient coefficient parameters are documented in `lean.note`.

Edge cases: N=0 includes all positive degrees; q=N is excluded; negative q
cannot exceed a natural-number bound. n=1 is included; n=0 is outside the
node's scope even though the general upstream predicate can also be used
with that coefficient ring. Zero sheaves, empty X or Y where f exists,
and arbitrary sheaf sizes within ModuleCat.{u+1} are included; no nonempty
index family is assumed. All primes unequal to p remain allowed. The
universe u of schemes is arbitrary and the coefficient/module universe is
u+1, the same size convention as the direct-image dependency; no equality
of the site's object and morphism universes is imposed. The general API
also admits the zero ring, without excluding any node case.

Independent searches, with different wording from the worker:

- Ran `msearch.py Q39 def-sf-uniform-direct-image-vanishing leanfinder`
  with “A predicate bounding the cohomological dimension of the pushforward
  functor on every sheaf of modules on an etale site”: eight generic hits,
  including the two etale topologies, but no Mathlib UDV predicate.
- Ran Loogle with `"cohomological"`: twelve spectral-object/spectral-sequence
  hits, not a uniform all-input direct-image predicate. Also read the actual
  signatures of `DerivedCategory.isLE_iff` and
  `Functor.isZero_rightDerived_obj_injective_succ`; the former bounds one
  object and the latter restricts to injective inputs, so neither replaces UDV.
- Ran msearch grep `HasUniform|CohomologicalDimension|cohomologicalDimension`:
  no Mathlib hits. Searches were written by msearch to `searches.jsonl`.
- Independently ran rg on the project and both upstream locations with the
  node id, UDV, and uniform-vanishing/cohomological-dimension vocabulary.
  This FOUND the exact shared/published upstream definition at
  `lean/WeilConjectures/SixFunctors/Etale/Derived/DirectImageVanishing.lean:75`.
  Read its actual signature, ambient Λ binder, docstring and full body.
  `dag/lean_names_upstream.json` has no corresponding name: that older
  index is not evidence that the published declaration is absent.
- Read the alternative `ProEtale.HasUniformCohomologicalDimensionLE` in
  `ProEtale/ExceptionalAdjoint`: it quantifies over pro-etale sheaves and
  site-object base changes. It is a different predicate and is not used.
  No duplicate UDV declaration was found under `lean/Sheaf`.

Mismatch found and repaired: H4, the worker introduced a second definition
because the newer published upstream module was not searched. Dropped its
module and attached the existing definition; no other mathematical mismatch
was found. No new node, dependency module, theorem, sorry, or proof is delivered.

Verification: compiled the scratch-only `ExistingCheck.lean` through the required
`scompile.py Q39 def-sf-uniform-direct-image-vanishing` wrapper. Its `#check`
confirms the complete existing type and its coefficient specialization; an
`Eq.refl` typecheck verifies definitional equality with the node's full
all-sheaf/integer-degree/strict-bound/zero-sheaf formula. The scratch file is
outside `lean/` and is not delivered. The local overlay had a stale duplicate
K-flat import collision; the wrapper's automatic current-server confirmation
passed cleanly in 5.0 seconds (nice 19, two threads, 60-second limit). There
is no remaining tool failure and no new module needing compilation. Delivery
also independently compiles an import and `#check` probe of the existing name.
