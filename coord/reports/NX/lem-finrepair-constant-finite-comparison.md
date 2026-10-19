## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ConstantFiniteComparison.lean` states
`AlgebraicGeometry.Etale.constructible_constant_of_finite_comparison`, with one `sorry`
and no new definitions. The node statement is unchanged. The source is the blueprint
`sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-constant-finite-comparison.md`, read in full,
together with the node's seven expanded proof steps. The theorem docstring carries all
seven steps and their dependencies. No statement dispute or dependency fault was found.

Hypothesis and conclusion correspondence:

- The ground field is `(k : Type u) [Field k]`. The schemes are `X S Y Z : Scheme.{u}`.
  The structures `X.Over (Spec (.of k))` and `S.Over (Spec (.of k))` make X and S
  k-schemes. Each pair `LocallyOfFiniteType` and `QuasiCompact` on its structure map
  is exactly finite type, as required by the scheme conventions. There is no independent
  finiteness hypothesis on Y: finiteness of nu makes it finite type over X and hence k.
- The proper morphism is `(f : X ⟶ S) [IsProper f]`. The equality `hf` states that f
  commutes with the two k-structure maps, so it is a morphism of k-schemes.
- The comparison is `(ν : Y ⟶ X) [IsFinite ν] [Surjective ν]`. Its composite v is
  written `ν ≫ f` throughout; no separately chosen map v is introduced.
- The reduced closed subscheme is `(i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]`.
  The condition that f restricted to Z is finite is `[IsFinite (i ≫ f)]`.
- `U : X.Opens` and `hU : ∀ x, x ∈ U ↔ x ∉ Set.range i` specify precisely the open
  complement of Z. `hν : IsIso (pullback.snd ν U.ι)` says that nu is an isomorphism
  over that complement. U is an explicit name for the uniquely determined complement,
  not an extra geometric assumption; its existence follows because i is a closed immersion.
- The ring is `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]`. The positive annihilator
  and invertibility convention is `hΛ : IsSmoothBaseChangeCoefficients N Λ S`, namely
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
  Invertibility pulls back to X, Y and Z; there is no additional coefficient restriction.
  The separate Finite instance permits use of the recorded constructibility predicate.
- The finite module is `(M : ModuleCat.{u + 1} Λ) [Finite M]`, a finite underlying set,
  not merely a finitely generated module over an arbitrary ring.
- On a scheme T, the constant sheaf is exactly
  `(constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`.
  `_root_.DerivedCategory.singleFunctor _ 0` places it in degree zero, and
  `(lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor` is its total direct image.
  `_root_.DerivedCategory.homologyFunctor _ (q : ℤ)` takes its q-th cohomology sheaf.
  These are the imported ambient-foundation objects, with no substitute sheaf category.
  The unbounded right derived functor restricted to a sheaf in degree zero computes the
  same bounded-below direct image specified in the node.
- `hv : ∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf ...` is the hypothesis on every
  higher direct image under v. The first conjunct repeats precisely this predicate for f.
  Higher direct images of sheaves are indexed by nonnegative q; negative cohomology of
  their right derived direct image vanishes, so nothing is lost by using natural indices.
- The second conjunct is `∀ q : ℕ, 2 ≤ q → IsIso (...)`. Its morphism is explicitly the
  q-th cohomology of the following composite: apply Rf_* to the derived adjunction unit
  for nu on the degree-zero constant sheaf, then to Rnu_* of the exact-pullback/single
  comparison followed by the canonical constant-sheaf pullback isomorphism; finally apply
  `rightDerivedLowerStarComp ... ν f`. Thus the target is exactly R(v)_* constant M on Y.
  The derived unit is the canonical lift of the underived unit specified in the node.
  On an injective representative this is the unit/composition comparison of proof step 5,
  not an arbitrarily chosen isomorphism between the cohomology objects.

Statement dependencies used, with their source signatures and docstrings inspected:

- `def-weil-pbc-scheme-conventions` is explicitly a convention record with no declaration
  or module. Use its Mathlib properties: `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsProper`, `IsFinite`, `Surjective`, and `IsClosedImmersion`.
- `sbc-def-coefficient-conventions`: module
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`, declaration
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `def-weil-pbc-constructible-complexes`: module
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, declarations
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory`. For the sheaf clause it
  publicly imports `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` and uses
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`; the theorem uses exactly
  this predicate, not upstream's distinct `Scheme.IsConstructibleSheaf`.
- `def-weil-pbc-direct-image` and `def-weil-pbc-inverse-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declarations
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
  The recorded `rightDerivedLowerStarPlus` is defined in the publicly available
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; the theorem uses
  the generic total `Functor.rightDerivedFunctor`, as the upstream derived formalism does.
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` supplies
  `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction` and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarComp`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, declaration
  `CategoryTheory.constantSheaf`, the sheafification of the constant presheaf.
  `WeilConjectures.ConstructibleSheaf.Defs` supplies the proof dependency
  `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`; its signature and construction by
  uniqueness of left adjoints were read. Mathlib's
  `Functor.mapDerivedCategorySingleFunctor` supplies compatibility with degree-zero objects.

All proof-dependency modules which have a recorded module are imported (without public
imports when they are only used by the proof). For geometric-stalk exactness, whose
mathlib_match is a multi-file record, the three files Point.Basic, Point.Skyscraper and
ShortComplex.ShortExact are imported explicitly. `lem-fin-finite-morphism` has no recorded
Lean declaration yet and therefore cannot be imported; it is retained in the proof
and docstring for stage 3. No other proof dependency is silently removed.

Edge cases checked before writing:

- Zero M and the zero coefficient ring are allowed. No Nontrivial hypotheses occur.
- Empty schemes and the empty complement are allowed; no Nonempty or dense-open condition
  occurs. If Z is empty the comparison is globally an isomorphism. If Z is all of X,
  the required finite restriction is the correct hypothesis; U is empty.
- Reducible and nonnormal X and Y are allowed. Despite the title, nu need not be an
  actual normalization, birational, or have reduced source. Only Z is required reduced.
- Degree zero and one assert constructibility only; the isomorphism conclusion starts
  at degree two. The cohomological shift is zero and the index is positive q, not -q.
- No algebraic closure, perfection, characteristic-zero, connectedness or projectivity
  assumptions have been introduced. The invertibility restriction is exactly the given
  smooth-base-change coefficient convention.
- The single scheme universe u and coefficient universe u+1 are the existing six-functor
  encoding and include all schemes/modules of the node; there is no separate undersized
  test-object universe or vacuous quantification.

Searches performed using `/home/ubuntu/weil-launcher-nt/msearch.py` (NX, this item):

- LeanFinder: “Higher direct images of constant finite sheaves under a finite surjective
  map isomorphic away from a closed subscheme finite over the base are isomorphic in
  degrees at least two”. Eight hits, including affine-transition limits, coherent-site
  local surjectivity and sheaf pullback unit results. None states this comparison.
- Loogle: `CategoryTheory.Functor.rightDerived, AlgebraicGeometry.Etale.lowerStar`.
  Zero hits; the service reports the project-specific lowerStar identifier unknown.
- grep: `rightDerived.*[Cc]omp|finite.*constructible`, Mathlib CategoryTheory.
  Eleven hits: generic right-derived transformation composition and localization
  comparison maps. These are tools, not the requested finite geometric statement.
- LeanSearch: “Constructibility and higher direct image comparison for constant sheaves
  under finite surjective normalization isomorphism outside a finite closed subset”.
  Service unavailable (Internal Server Error); no result or verdict claimed for this search.
- `rg` in the upstream WeilConjectures source and side `lean/Sheaf` for finite/constant
  comparison, derived composition, and constant-unit names found the existing direct-image
  composition formalism and `ConstantModulePushforwardFunctoriality.lean`, whose map is
  degree zero only. No existing theorem asserts this node's conclusions.
- Exact node-id search in upstream WeilConjectures returned no hits. The proposed full
  declaration name was also searched in the upstream source, side Lean and
  `dag/lean_names_upstream.json`, with no existing declaration found.

Validation: server-only `scompile.py`, nice 19, two threads, 60 s per file. After correcting
an unavailable Mathlib import spelling and spelling finite type as locally finite type plus
quasi-compact, the entire theorem elaborated in 9.0 s with no errors or warnings.
The final explicit proof imports are also checked by the delivery dry run. No local Lean,
Lake build, upstream edit, or push was performed by this worker. A fresh second reader
will review and deliver this sandbox.

## Second reading by NX

I independently read the node, the complete blueprint source at
`sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-constant-finite-comparison.md`,
the six statement-dependency nodes and their recorded declarations, and the Lean file.
The source of this node is the blueprint, rather than a single Stacks theorem.
I also read Stacks `etale-cohomology.tex` at
`proposition-finite-higher-direct-image-zero` (03QP),
`lemma-constructible-abelian` (03RZ), and
`lemma-finite-pushforward-constructible` (095R), including their hypotheses.
The last lemma requires finite presentation, which follows for the finite maps here
because their targets are finite type over a field and therefore locally Noetherian.
The Noetherian coefficient requirement follows from finiteness of the ring.
No extra geometric hypothesis is needed.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. A field k and finite-type k-schemes X and S: `(k : Type u) [Field k]`,
   `(X S Y Z : Scheme.{u})`, the two `Over` instances, and
   `LocallyOfFiniteType` plus `QuasiCompact` on each structure map. This is precisely
   the finite-type convention, without an added separatedness assumption on S.
2. A proper k-morphism f: `(f : X ⟶ S) [IsProper f]` and `hf` asserting compatibility
   with the two structure maps. Y and Z obtain their k-structures by composition;
   separate choices or extra assumptions on those structures are unnecessary.
3. A finite surjection nu: `(ν : Y ⟶ X) [IsFinite ν] [Surjective ν]`.
   The morphism v is consistently the composite `ν ≫ f`.
4. A reduced closed subscheme Z with finite restriction of f:
   `(i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z] [IsFinite (i ≫ f)]`.
   Neither X nor Y is required reduced, normal, or a curve.
5. Nu is an isomorphism off Z: `U : X.Opens` with
   `hU : ∀ x, x ∈ U ↔ x ∉ Set.range i`, and
   `hν : IsIso (pullback.snd ν U.ι)`. The second pullback projection has target U,
   so this is the base change of nu, not the projection to Y. Naming the unique open
   complement introduces no restriction.
6. Positive N and the finite commutative ring killed by N, invertible on the schemes:
   `N`, `Λ`, `[CommRing Λ] [Finite Λ]`, and
   `hΛ : IsSmoothBaseChangeCoefficients N Λ S`. I opened the definition: it is
   `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
   Pullback of the unit supplies invertibility on X, Y and Z. The explicit finite
   instance merely makes the same coefficient assumption available to elaboration.
7. A finite module M: `(M : ModuleCat.{u + 1} Λ) [Finite M]`;
   this is finiteness of the underlying set, as the node requires.
8. Constant coefficients: `(constantSheaf T.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)).obj M`. I checked Mathlib's definition as sheafification of
   the constant presheaf and the source's `upperStarConstantSheafIso` declaration.
9. All higher images for v are constructible: `hv : ∀ q : ℕ, ...` uses
   `DerivedCategory.homologyFunctor _ (q : ℤ)` of
   `(lowerStar ... (ν ≫ f)).rightDerivedFunctor` applied to `singleFunctor ... 0`
   of that constant sheaf. I read `lowerStar`, `upperStar` and their adjunction in
   `UpperLowerStar/Defs.lean`; these are the recorded small-etale module-sheaf functors.
   The unbounded derived functor on this degree-zero object computes the recorded
   bounded-below derived image. Negative images vanish; natural indices do not exclude
   an additional case of the assertion.
10. All higher images for f are constructible: the first conjunct is the identical
    predicate and construction with `f` replacing `ν ≫ f`, quantified over every q.
    The predicate is `Scheme.IsConstructibleEtaleModuleSheaf`, which I opened through
    `BoundedConstructibleComplexes`: it uses finite constructible locally closed
    strata and etale trivializations with finite constant module values. The distinct
    upstream `IsConstructibleSheaf` predicate has not been substituted.
11. The specified comparison is an isomorphism for q at least two: the second conjunct
    is `∀ q : ℕ, 2 ≤ q → IsIso (...)`. I traced its arrows in order: derived unit at
    the degree-zero constant sheaf on X; Rnu_* applied to the exact-pullback/single
    isomorphism and canonical constant-sheaf pullback isomorphism; Rf_* of this map;
    then `rightDerivedLowerStarComp ... ν f`; finally q-th homology. I opened the
    derived adjunction and composition definitions in `Derived/UpperLowerStar.lean`.
    The latter has direction `Rnu_* ⋙ Rf_* ≅ R(ν ≫ f)_*`, exactly as used here.
    Thus this asserts invertibility of the prescribed map, not existence of some iso.

Edge cases: zero M, the zero coefficient ring, empty schemes, U empty, Z empty,
and Z equal to X are all admitted. Surjectivity correctly forces Y empty if X is empty.
Degrees zero and one assert constructibility without an unjustified iso; degree two
is included. N = 0 is excluded by the source's positivity convention, and positive
characteristic is constrained only by invertibility of N. No algebraic closure,
perfection, connectedness, or density condition occurs. The shared scheme universe u
and coefficient/module universe u+1 are the established small-etale framework;
there is no independent universe of test schemes that could make a condition vacuous.
There is no index family whose empty case is omitted.

Independent searches, using different formulations from the first worker:

- LeanFinder via msearch: “A proper morphism and a finite surjective modification that
  is an isomorphism away from a finite closed locus induce isomorphic higher direct
  images of a constant finite module in degree at least two”. Eight hits concerned
  generic sheaf pushforward, module pullback, or condensed solidification; no match.
- Loogle via msearch: `IsFinite, IsProper, IsIso`; zero hits, with `IsFinite` reported
  unknown by that service. This is not treated as evidence of absence by itself.
- grep via msearch: `IsIso.*rightDerived|constructible.*constant`; nineteen generic
  localization/right-derived comparison hits, none the geometric theorem.
- Direct rg over Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `finite.comparison`, normalization/constant combinations, and the proposed full name.
  I opened the upstream curve-normalization transfer theorem in `Curve/Reductions.lean`:
  it concerns reduced curves over algebraically closed fields, smooth normalization,
  extension by zero and the curve assertions; it is not this statement.
  I also opened `ConstantModulePushforwardFunctoriality.lean`: its existing map is
  underived, not this higher-image comparison theorem. No duplicate was found.
- LeanSearch via msearch with “Constructibility of higher direct images descends along
  finite surjective morphisms that are isomorphisms off a closed subscheme finite over
  the base” was unavailable (Internal Server Error); no mathematical verdict is inferred.

There are no new definition nodes or dependency modules in this delivery, and no
statement correction. No mismatch was found; the Lean module and node were retained
unchanged. The module has no new definition, private substitute, hollow data, local
notation or local instance. Its sole theorem has proof `sorry`; its docstring records
all seven proof steps and their dependencies, with the required source and blueprint id.
All variables and the sole universe are explicitly bound. I compared the node's
`lean.statement` to the theorem signature verbatim: equal.

Validation: I compiled the delivered file through server-only `scompile.py` with
nice 19, two threads, and the 60-second per-file limit. The coefficient overlay
compiled in 1.4 s and `ConstantFiniteComparison.lean` in 8.5 s, with no errors or
warnings. The initial invocation from the repository used a sandbox-relative path
and failed to locate the file before compilation; rerunning with its absolute sandbox
path succeeded. No local compiler, global build, repository git command, or upstream
write was used.
