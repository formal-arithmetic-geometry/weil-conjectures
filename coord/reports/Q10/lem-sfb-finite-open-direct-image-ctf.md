## Worker report

The module `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` states exactly the node as
`AlgebraicGeometry.ProEtale.CondensedRing.finiteOpenDirectImage_constantModel_torAmplitude`.
Its sole theorem has proof `by sorry`; it adds no definitions or axioms. The node's
statement, dependencies and proof are unchanged. No statement dispute was found.

Source read: the current blueprint main-20261015,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), finite-coefficient quasi-compact open immersion sentence. The seven-step
proof in the node is included in the theorem docstring, naming its supporting nodes.
There is no repair note for this item.

Hypothesis and conclusion correspondence:

- The prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`. The positive characteristic p and the
  inequality p ≠ ℓ are `(p : ℕ) [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)`;
  `(k : Type u) [Field k]` is an arbitrary field, with no separable-closedness assumption.
- Schemes U,X are `{U X : Scheme.{u}}`, each with `[T.Over (Spec (.of k))]`.
  For each structure map, `[LocallyOfFiniteType ...] [QuasiCompact ...]` is finite
  type and `[IsSeparated ...]` is separatedness. These are precisely the setting's
  hypotheses. No compactification is chosen or assumed because this theorem uses none.
- The quasi-compact open k-immersion is `(j : U ⟶ X)` with
  `[j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]`.
- The coefficient ring is `(A : Type u) [CommRing A] [Finite A]`, including the zero ring.
  `[TopologicalSpace A] [DiscreteTopology A]` supplies its discrete topology, not any
  extra property of A; topological-ring compatibility follows by instance synthesis.
  `_hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ : A) ^ n = 0` is exactly ℓ^n 1_A = 0 for some n ≥ 1.
- The condensed ring is the recorded
  `Profinite.continuousMapRingObjOfUniverse.{u, u} A`, the underlying additive sheaf
  of S ↦ C(S,A) with pointwise multiplication and precomposition. The recorded `continuousMapRingObjOfUniverseMonObj` and
  `isCommMonObj_continuousMapRingObjOfUniverse` are registered as global instances
  using `attribute [instance]`. These are exactly the dependency's supplied structures;
  no new instance declaration, choice of structure, or extra assumption is introduced.
- For both T=U,X, `condensedRingObj ... T` is exactly p_T^* underline(A), and
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj ... T)` is the
  category of internal modules. `DerivedCategory` is its ordinary unbounded derived
  category. There is no completion or restriction to the bounded-below category.
- `moduleObjectDerivedPushforward ... j` is the dependency's named total right
  derived functor of the full underived module direct-image composite. The output
  is this actual functor applied to K, not a chosen isomorphic replacement.
- `∃ d : ℤ, 0 ≤ d ∧ ∀ (a b : ℤ), a ≤ b → ∀ K, ...` expresses the single nonnegative
  integer d_j chosen for the fixed j and A, independently of K,a,b.
- The input predicate `constantModelBoundedConstructible ... U K` is the recorded
  constant-model bounded constructibility condition. `DerivedCategory.torAmplitudeIn
  _ a b K` quantifies over every internal module placed in degree zero, not just flat,
  finite, constant, or constructible test modules.
- The conclusion is the conjunction of that same bounded constructibility predicate
  on X for Rj_*K, and `DerivedCategory.torAmplitudeIn _ a (b + d)` for that same object.
  Thus only the upper endpoint increases, by the common d_j, and the output tests
  all degree-zero A_X-modules too.

Dependency interfaces read and used:

- `sk-def-sfb-dc-setting`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  is publicly imported. Its setting is rendered by the explicit over-field binders;
  its `compactificationOverField` is not needed for this open-image assertion.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and the exported `QuasiCompact` interface
  from `Morphisms.QuasiCompact`. Both signatures and defining conditions were read.
- `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse`, based on
  `continuousMapRingSheafOfUniverse`, with its canonical monoid and commutativity
  constructions. The signature uses the recorded underlying ring-object construction.
- `sk-def-sfb-pulled-back-coefficients`: upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `condensedRingObj`,
  `coefficientRing`, and the commutative pullback structure. This module is exported
  by the imported derived-module framework; the coefficient is inverse image from
  the point under its canonical strong monoidal functor.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`. Its definition uses
  canonical t-structure boundedness and constructibility of every cohomology module,
  with finite constant local models on strata, and the affine-local convention.
- `det-def-sfb-constructible-tor-amplitude`: `Sheaf.Paper.ConstantModelTorAmplitude`
  publicly exports those same notions and their well-definedness, using
  `DerivedCategory.torAmplitudeIn` from
  `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`. Its full definition
  was read: for all F in the underlying module category it tests K tensor single_0(F).

All nine recorded project-module proof dependencies are imported without `public`.
The two qcqs proof dependencies are Mathlib matches supplied through the existing
scheme-morphism imports. `lem-sfb-ordinary-proetale-direct-image-plus-comparison` has
neither a Lean declaration nor a Mathlib match in the current DAG, so there is no
module to import for that future proof step; its mathematical role remains in the
docstring. It is not needed to type this theorem statement.

Edge cases checked before writing:

- A=0: no `Nontrivial A` binder occurs. The nilpotence assumption holds for any n≥1;
  internal unital modules vanish, and d=0 works.
- K=0 and U empty: the source objects and their images vanish; all Tor intervals
  are permitted, including negative endpoints. There is no nonemptiness binder.
- j=id and an empty target: both satisfy the declaration's geometric conditions;
  the statement allows d=0 and requires no strictly positive enlargement.
- a=b: accepted by `a ≤ b`; negative a,b and negative a with b≥a are all included.
- Nonzero rings with nilpotents, e.g. Z/ℓ², are included; no field or regularity
  assumption is placed on A.
- k with unbounded absolute cohomological dimension remains included: d bounds the
  relative open direct image only. The proof plan never uses a bound on cd(k).
- A nontrivial upper enlargement is allowed (e.g. punctured curves), so this is not
  an erroneous claim that the original Tor interval is preserved exactly.
- The single explicit universe u is the existing internal-module framework's scheme
  and small coefficient convention. A is finite and may be represented in that
  universe; no field is required to be finite and no site universes are equated.

Existing-declaration searches:

- msearch.py, LeanFinder: "Finite discrete torsion coefficients open immersion
  derived pushforward preserves bounded constructibility with a uniform Tor amplitude
  bound". Eight hits: ordinary open-immersion structure-sheaf pushforward, derived
  t-structure bounds, and Grothendieckness of light condensed modules; none states this.
- msearch.py, Loogle: `"torAmplitudeIn", "rightDerivedFunctor"`: zero hits.
- msearch.py, grep: `(openImmersion|[Oo]pen).*([Tt]orAmplitude|[Cc]onstructible)|
  ([Tt]orAmplitude|[Cc]onstructible).*(rightDerived|pushforward)`:
  thirteen hits, on constructible subsets/topologies of spectra and spaces; no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: open Tor bound, finite-open direct
  image, and continuous-coefficient searches. Existing `OpenTorBoundArbitraryField`
  treats ordinary etale coefficients and projection hypotheses; it is a proof input,
  not this internal-module uniform constructibility conclusion. Existing
  `AdmissibleDirectImage` gives existence of some finite Tor amplitude but does not
  assert the uniform interval [a,b+d_j]; it is the parent theorem, not an exact match.
- grep for this node id in `lean/WeilConjectures`: no existing declaration.
  The proposed full name and its stem also have no hits in project sources or
  `dag/lean_names_upstream.json`.

Validation: scompile.py compiled the initial draft in sandbox and library mode
cleanly (15 seconds each). The final declaration uses the recorded continuous-map
coefficient construction directly. Its supplied monoid and commutativity declarations
need instance registration; registering those existing declarations resolves the
instance-synthesis failure without changing any mathematical hypothesis. The final
file compiled cleanly in sandbox mode (28.9 seconds) and library mode (25.2 seconds),
with no warnings. Delivery preflight and per-file compilation run through
deliver2.py --no-push.

## Second reading by Q10

The dispatcher explicitly forbids starting another agent and assigns independent
review to the maintainer after delivery. This is a worker self-check, not a claim of
independent review. Re-reading the node alongside the declaration confirms the
hypothesis and clause correspondence above. In particular, d is outside all three
quantifiers, the two output predicates refer to the same actual Rj_*K, both Tor tests
range over all internal modules, zero coefficients are retained, and the field is
arbitrary subject to the stated characteristic conditions. No mathematical statement
change, new node, or dependency repair is needed.
