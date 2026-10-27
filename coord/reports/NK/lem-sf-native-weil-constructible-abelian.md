## Worker report

Maintenance resolution (2026-10-22): server commit
`b2439f9ebb910696ee9d7bbd5527c7c6883eefb3` explicitly names the existing native
Grothendieck instance `instIsGrothendieckAbelianProEtaleWeilSheaf`. This is the exact
name Lean already generated; its type, binders, proof and instance behavior are preserved.
The retained node's `lean.statement` now includes the explicit name. Earlier
wrong-refusal reports described the source before that maintenance repair; they are retained
in the sandbox archive `report.previous-retries.md.bak`.
The unchanged server `check_existing` now accepts this attachment. The module passed
`tools/lean_file.sh` in the maintenance sandbox and the library within the 60-second limit,
and was registered through `tools/land.sh` as landing
`20261022T073902-maint-NK-1792653584-1399488`. Run the prescribed delivery dry run against
current sources before delivering. No new statement module is required.

This is an existing-declaration attachment, not a new statement module. The complete node is
already expressed by the native category instance and the existing forgetful and object-property
instances publicly imported by `WeilConjectures.WeilSheaf.Category`. Only the item's `lean`
field changes. No definition, theorem, dependency, or source statement is changed.

The primary declaration is
`AlgebraicGeometry.instIsGrothendieckAbelianProEtaleWeilSheaf`, Category.lean:146.
Its literal source signature is recorded in `lean.statement`; its parameters are supplied by the
surrounding explicitly bound Frobenius section. The additional declarations in `lean.declarations`
cover the other clauses; the primary declaration alone is not claimed to encode those clauses.

Hypotheses and objects, checked against both statement dependencies:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime different from the characteristic: `(l : ℕ) [Fact l.Prime]`
  and `[Fact (ringChar k₀ ≠ l)]`. The ambient Grothendieck assertion actually works without the
  characteristic restriction; its specialization to the required context is used here.
- Scheme over the finite field: `(X : Scheme.{u})`
  `[X.Over (Spec (CommRingCat.of k₀))]`.
- Locally finite type: `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]`.
  No quasi-compactness, global finite type, separatedness, or nonemptiness is imposed.
- The actual coefficient category is
  `ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber`.
  Module.lean:55 defines it as module objects over `adicConstantSheaf` in vector-space sheaves.
  Ring.lean identifies the coefficient algebra sectionwise with locally finite continuous
  functions, with the usual pointwise algebra and restriction by precomposition.
- `ProEtaleWeilSheaf k₀ l X` is literally
  `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)` (Category.lean:143).
  The Frobenius functor is the pushforward along the inverse geometric Galois Frobenius,
  canonically isomorphic to its pullback; its IsEquivalence instance is already supplied.
- The full constructible subcategory is `(WeilSheaf.objectProperty k₀ l X).FullSubcategory`.
  Category.lean:150 defines the property as `adicConstructibleSheaf.inverseImage` along the
  forgetful functor, hence exactly constructibility of the underlying native module sheaf.
  The local finite-stratification, finite-rank, variable-rank-on-cover definition was read in
  Adic/Constructible.lean:82-151. No different coefficient category is substituted.

Each conclusion and the existing declaration that supplies it:

1. Grothendieck abelian: `IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l X)` is the
   primary native instance. `CategoryTheory.Endofunctor.IsoAlgebra.abelian` supplies the ambient
   abelian structure. Mathlib's Grothendieck class includes a separator and AB5; it implies all
   small colimits. These three component instances were checked separately in the consumer probe.
2. Exact forgetting: with `F = WeilSheaf.frobeniusPullback k₀ l X`, the functor is
   `CategoryTheory.Endofunctor.IsoAlgebra.forget F`. The existing
   `IsoAlgebra.instPreservesFiniteLimitsForget` and
   `IsoAlgebra.instPreservesFiniteColimitsForget` apply to this exact additive autoequivalence.
   Preservation of finite limits and finite colimits is the standard exact-functor interface
   between the abelian categories in the node.
3. Conservative forgetting: `IsoAlgebra.instReflectsIsomorphismsForget` is precisely reflection
   of isomorphisms by the same functor.
4. Contains zero: `ProEtale.instContainsZeroAdicSheafAdicConstructibleSheaf`, transported by Mathlib's
   `ObjectProperty.instContainsZeroInverseImageOfIsClosedUnderIsomorphismsOfPreservesZeroMorphismsOfHasZeroObject`,
   gives `(WeilSheaf.objectProperty k₀ l X).ContainsZero`. Together with isomorphism closure
   this includes the chosen zero object, not only some isomorphic representative.
5. Isomorphism invariance: `ProEtale.instIsClosedUnderIsomorphismsAdicSheafAdicConstructibleSheaf` and
   `ObjectProperty.instIsClosedUnderIsomorphismsInverseImage` give
   `(WeilSheaf.objectProperty k₀ l X).IsClosedUnderIsomorphisms`.
6. Kernel closure: `ProEtale.instIsClosedUnderKernelsAdicSheafAdicConstructibleSheaf` and
   `ObjectProperty.IsClosedUnderKernels.inverseImage` give
   `(WeilSheaf.objectProperty k₀ l X).IsClosedUnderKernels`. The locally Noetherian geometric
   fibre required by the underlying instance is derived by
   `AlgebraicGeometry.isLocallyNoetherian_geometricFiber` from the node's locally finite type
   assumption. The instance quantifies over every morphism whose two endpoints have the property.
7. Cokernel closure: `ProEtale.instIsClosedUnderCokernelsAdicSheafAdicConstructibleSheaf` and
   `ObjectProperty.IsClosedUnderCokernels.inverseImage` give the identical cokernel assertion.
8. Extension closure:
   `AlgebraicGeometry.instIsClosedUnderExtensionsProEtaleWeilSheafObjectProperty` gives
   `(WeilSheaf.objectProperty k₀ l X).IsClosedUnderExtensions`. Its field is exactly
   `S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂` for every ambient short complex.
   It imposes neither a splitting nor a constructibility assumption on the middle term.

Dependency declarations and source signatures read:

- `def-sf-native-weil-derived-framework`: its recorded entry module is
  `WeilConjectures.WeilSheaf.LowerShriek` and primary declaration is
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`. Its complete signature and docstring were
  read at LowerShriek.lean:144-160; this compact-support operation itself is not used here.
  The recorded supporting declarations used here are `AlgebraicGeometry.ProEtaleWeilSheaf`,
  `AlgebraicGeometry.WeilSheaf.frobeniusPullback`, and
  `AlgebraicGeometry.WeilSheaf.objectProperty` in WeilSheaf/Category.lean:134-153,
  `AlgebraicGeometry.ProEtale.AdicSheaf` in Adic/Module.lean:55, and the three lisse/stratified
  lisse/constructible predicates in Adic/Constructible.lean. They are used unchanged.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` is used on the structure morphism.
  Its full class signature and docstring were read at FiniteType.lean:39-46.
  `QuasiCompact` is also recorded by the dependency, but the present node requires only local
  finite type and does not add quasi-compactness.
- Forgetful declarations were read at
  `WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor`:114-143.
  The general Grothendieck theorem and its proof explanation were read at
  `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`:366-389.
- Underlying closure declarations and their proofs were read at
  `WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`:315-336,
  `WeilConjectures.SixFunctors.ProEtale.Adic.Abelian`:492-552, and
  `WeilConjectures.SixFunctors.ProEtale.Adic.Extension`:317-340.
  The generic kernel/cokernel transports are in
  `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels`:28-42.

The source proof agrees with the DAG's seven steps: identify the actual module category and its
Grothendieck structure; apply the autoequivalence fixed-pair theorem; transport zero and
isomorphisms; derive local Noetherianity of the geometric fibre; refine two local finite
stratifications; use the lisse kernel/cokernel stratifications and exact restriction; and use
lisse extension closure stratum by stratum. The existing instances already express the results
of these steps. No additional proof is supplied by this delivery.

Edge cases checked: the empty scheme is allowed (local constructibility is vacuous there);
zero has the rank-zero model, including the empty finite sum; variable ranks over different
cover members are retained; neither a nonempty stratum index nor a global finite stratification
is imposed; non-quasi-compact locally finite type schemes are retained. Scheme and field have
the common arbitrary universe `u` of the recorded native framework, whose sheaf Hom and small
colimit universe is `u + 1`. No additional universe equality is imposed. The coefficient prime
and noncharacteristic assumptions are exactly those in the statement.

Searches (2026-10-22):

- `msearch.py ... leanfinder`: “Frobenius equivariant constructible pro etale sheaves form a
  Grothendieck abelian category exact conservative forgetful functor weak Serre subcategory”.
  Eight results on condensed module and generic sheaf categories; no native Weil match.
- `msearch.py ... loogle '"IsClosedUnderKernels"'`: nine generic object-property declarations,
  including the closure class and full-subcategory abelian infrastructure; no native Weil result.
- `msearch.py ... grep 'IsoAlgebra|adicConstructibleSheaf|IsAdicConstructibleSheaf'`: one
  unrelated AlgCat hit. Direct `rg` of WeilConjectures found the native Category, Constructible,
  Abelian, Extension and IsoAlgebra results above. Searching the exact item id in
  `lean/WeilConjectures` gave no hit. Direct `rg` of `lean/Sheaf` found consumers and other
  coefficient frameworks; no new native construction is necessary.
- Mathlib direct searches read ContainsZero, ClosedUnderIsomorphisms, Kernels, Extensions and
  GrothendieckCategory.Basic to check the exact meaning and transport of each closure property.

Validation: `scompile.py NK lem-sf-native-weil-constructible-abelian` compiled a scratch consumer
with the required module header, public imports, `set_option autoImplicit false`, explicit
universes and binders. All ten `#synth` checks passed on the live published server library. Separate checks for
small colimits, AB5 and a separator also passed, with no warnings. The first name-only check
found four incorrectly guessed anonymous-instance names; the record and this report now use
the exact `...AdicSheafAdicConstructibleSheaf` names printed by successful `#synth` checks.
The scratch file is outside `lean/`, is not delivered, and introduces no new declarations.
The delivery wrapper additionally checks every attached declaration by name.

No statement dispute or node fault was found. There are no new nodes or dependency repairs.

## Second reading by NK

The same worker reread the node, the source declarations, and every hypothesis/conclusion mapping
above after the successful consumer check. No mismatch was found: in particular local finite type
is used only to derive local Noetherianity, the forgetful functor is the ambient native one, and
extension closure uses arbitrary ambient short exact sequences. This is a self-reread, not a
claim of an independent agent review. The dispatcher brief forbids starting other agents and
assigns the independent reading to the maintainer's delivery review.

## Current validation (2026-10-22)

The required initial `deliver2.py NK lem-sf-native-weil-constructible-abelian --no-push`
passed server preflight and compilation at dry-run commit `e0f5fd4f8a9`.
The earlier generated-instance name rejection is resolved by the maintenance source repair.
A fresh prescribed `scompile.py` check of `scratchpad/ExistingChecks.lean` then passed
both sandbox (8.0 s) and library (11.4 s) modes without errors or warnings. It resolves
the explicitly named primary instance and synthesizes every ambient, forgetful and
constructible-closure assertion, plus small colimits, AB5 and a separator.

The current node, both dependency records, their relevant full source signatures and
docstrings, the native coefficient and constructibility definitions, the general
fixed-pair theorem, and the kernel/cokernel/extension interfaces were reread. The
recorded primary signature preserves the current source line break verbatim.
Comparing with the shared node finds only the authorized `lean` change.
The maintenance repair note is explicitly stage 1 (proof splitting); it is not a
stage-2 interface withdrawal and the proof is unchanged in this delivery.
No source module, launcher tool, live node, or declaration index was edited.
