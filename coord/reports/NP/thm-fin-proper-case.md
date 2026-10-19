## Worker report

The module `Sheaf.AlgebraicGeometry.ProperCaseConstructibility` states
`AlgebraicGeometry.Etale.properCase_constructible_and_vanishing`, with `sorry` as its
entire proof. The module and declaration docstrings identify the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/thm-fin-proper-case.md`. The declaration docstring
reproduces all seven steps of the node's proof and their cited ingredients.

Statement correspondence, checked against the node and its blueprint source:

- The field is `(k : Type u) [Field k]`.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`. The integer is `(N : ℕ)`. The hypothesis
  `hcoeff : IsSmoothBaseChangeCoefficients N Λ S` is exactly `0 < N ∧ Finite Λ ∧
  (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`: positivity, annihilation, and invertibility
  on S. Annihilation of the unit is equivalent to annihilation of every element.
  The finite instance supplies the recorded constructibility predicate's interface.
- The schemes are `{X S : Scheme.{u}}`; S is over k through
  `[S.Over (Spec (.of k))]`. Its structure morphism has both
  `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
  `[QuasiCompact (S ↘ Spec (.of k))]`, exactly finite type.
- The given morphism is `(f : X ⟶ S) [IsProper f]`. No extra structure morphism
  on X, compatibility hypothesis on f, separatedness of S over k, or Noetherian
  hypothesis is introduced.
- The bound is `(d : ℕ)`. `hfib` quantifies over every `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω]` and every `(s : Spec (.of Ω) ⟶ S)`, following the recorded
  geometric-point size convention. Its fibre is the chosen `pullback f s` and
  `topologicalKrullDim ↥(pullback f s) ≤ (d : WithBot ℕ∞)` is exactly the bound.
- The sheaf is `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, with
  `(hF : Scheme.IsConstructibleEtaleModuleSheaf F)`, the recorded finite
  locally constant stratification notion used by the bounded-constructible node.
- The first conjunct quantifies over every `q : ℕ` and asserts
  `Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)`.
- The second conjunct quantifies over every `q : ℕ` and asserts
  `2 * d < q → IsZero (higherDirectImage Λ f (q : ℤ) F)`. `IsZero` says that
  the actual module sheaf is zero, not merely that chosen sections vanish.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  its separated, universally closed, locally finite type definition agrees with
  finite type because universally closed implies quasi-compact.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the inline geometric
  point is the declaration form specified by `def-weil-geometric-point` (whose
  `Scheme.SpecToEquivOfField` identifies its point and residue-field map).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, available on schemes through the imports.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : WithBot ℕ∞`, the
  dimension of chains of irreducible closed subsets.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, whose sheaf
  clause uses `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. The theorem uses
  that same sheaf predicate, rather than copying a constructibility definition.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, composition with etale base change.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`:
  `AlgebraicGeometry.Etale.higherDirectImage`, defined as degree-q homology of
  the derived pushforward of F in degree zero, is the needed existing interface.

The recorded proof-dependency modules are imported without `public` for the
future proof: `ConstructibleHigherDirectImages`, `ConstructibleSheaf.Pullback`,
`Mathlib.AlgebraicGeometry.Pullbacks`, `Morphisms.FinitePresentation`,
`GeometricFiberFinite`, `Sites.FibrewiseCohomologicalDimension`, and `Sites.EtalePoint`.
The proper constructibility completion theorem has no recorded module yet; this
is a proof prerequisite only and does not prevent stating this node.

Edge cases checked before drafting: d = 0 gives vanishing in positive degrees,
and q = 0 is included in constructibility without a spurious vanishing assertion.
The empty base and empty fibres are retained: fibre dimension is bottom for the
empty scheme, no geometric point is required to exist, and coefficient invertibility
is asserted on S itself, not on the ground field. The zero coefficient ring and
zero sheaf are permitted. No characteristic is excluded beyond invertibility of N
on S. The geometric field is not assumed to be k or given a separately constrained
k-algebra structure. All universes and variables are explicit; no extra small test
universe, hidden `let`, local notation, or file-local instance is used.

Searches actually run:

- `msearch.py ... leanfinder`: “For a proper morphism of schemes over a field,
  higher direct images of constructible finite etale module sheaves are
  constructible and vanish above twice the geometric fibre dimension”. Eight hits,
  headed by `Scheme.Hom.isConstructible_image`; none states this sheaf theorem.
- `msearch.py ... loogle`: `"higherDirectImage", "IsProper"`; zero hits.
- `msearch.py ... grep`:
  `constructible.*[Pp]roper|[Pp]roper.*constructible|higherDirectImage`; zero hits.
- Direct `rg` of the upstream WeilConjectures tree and `dag/lean_names_upstream.json`
  for `thm-fin-proper-case`: no existing declaration.
- Direct `rg` of upstream and project Lean sources for proper/constructible phrases
  and higher direct images found `EtaleProperDirectImageFiniteness.lean`.
  Its `proper_directImage_finiteness` was read in full: it takes Noetherian and
  finite-dimensional source and target, a bound on chosen algebraic-closure fibres,
  and stalkwise invertibility of additive orders. It is not the present node's
  field/finite-type/all-geometric-fibres statement, so it is not re-recorded as exact.
  `ConstructibleHigherDirectImages` defines only the constructibility predicate,
  not this theorem. Other hits concern curves, pro-etale coefficients, or cite this
  node in their docstrings; none is an exact existing statement.

No new nodes, dependency repairs, statement corrections, or disputed statements.

Validation: the delivered file compiled cleanly with `scompile.py NP
thm-fin-proper-case` on the server (nice 19, two threads, default 60 seconds per
file). The initial elaboration required making the scheme-to-underlying-space
coercion explicit as `↥(pullback f s)`; the final signature and node record use
that form. The successful compile reported 3.5 seconds for the library module.


## Second reading by NP

I read the node, its seven proof steps, the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/thm-fin-proper-case.md`, the coefficient
convention source, all eight statement-dependency nodes and their recorded
interfaces, and the delivered Lean file. I also read Stacks
`etale-cohomology.tex`, definition-constructible (095E) and
lemma-proper-base-change-stalk (0DDF). The latter requires a proper morphism
and torsion coefficients; annihilation by the positive N supplies torsion.
The blueprint coefficient convention supplies finite commutative coefficients
and invertibility on the scheme. No separatedness of the base over k is assumed.

Object/hypothesis/conclusion checklist, in node order:

1. Field k: `(k : Type u) [Field k]`. Correct, including positive characteristic.
2. Finite commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   Correct. This is the same coefficient size and module-sheaf category as
   BoundedConstructibleComplexes and its IsConstructibleEtaleModuleSheaf import.
3. Positive N annihilating Λ: `(N : ℕ)` and
   `hcoeff : IsSmoothBaseChangeCoefficients N Λ S`. Reading its definition gives
   `0 < N`, `Finite Λ`, `(N : Λ) = 0`, and `IsUnit (N : Γ(S, ⊤))`.
   Correct: N kills the unit iff it kills every element. The repeated finiteness
   proposition and typeclass impose the same hypothesis, not additional finiteness.
4. Schemes and morphism: `{X S : Scheme.{u}}`, `(f : X ⟶ S) [IsProper f]`.
   Correct. Mathlib IsProper extends IsSeparated, UniversallyClosed and
   LocallyOfFiniteType; universal closedness supplies quasi-compactness, hence
   this is the node's separated, finite-type, universally closed morphism.
5. S finite type over k: `[S.Over (Spec (.of k))]`,
   `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
   `[QuasiCompact (S ↘ Spec (.of k))]`. Correct by the dependency's explicit
   finite-type convention. X gets its k-structure by composition; none is missing.
6. N invertible on S: the final conjunct of hcoeff above. Correct, and does not
   replace invertibility on S by the stronger invertibility on k.
7. Nonnegative dimension bound d: `(d : ℕ)`. Correct.
8. Every geometric point: hfib quantifies over `(Ω : Type u) [Field Ω]
   [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`. Correct, using exactly the recorded
   geometric-point interface. SpecToEquivOfField identifies this with a point
   and its residue-field embedding. No k-algebra structure is separately imposed.
9. Geometric fibre and dimension: `topologicalKrullDim ↥(pullback f s) ≤
   (d : WithBot ℕ∞)`. Correct. I read pullback's chosen-limit interface and
   topologicalKrullDim's definition by chains of irreducible closed subsets;
   these are the dependency objects, with the scheme's underlying space explicit.
10. Constructible Λ-module sheaf on X_et: `F : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)` and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
    Correct. The imported definition requires a finite locally closed partition
    with constructible parts and finite constant module values after etale
    trivialization. It is the sheaf clause used by the recorded bounded
    constructible complex definition, not upstream's different stalk predicate.
11. Higher direct image: `higherDirectImage Λ f (q : ℤ) F`. Correct. I read
    lowerStar's base-change/precomposition construction and higherDirectImage's
    definition as homology of the bounded-below derived pushforward of F[0].
    I also fetched the current server SmoothBaseChange.Defs with scompile --source;
    the interface agrees with the local source. It uses no arbitrary replacement map.
12. Constructibility for every q ≥ 0: the first conjunct is
    `∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf (...)`. Correct, including q=0.
13. Vanishing for q > 2d: the second conjunct is
    `∀ q : ℕ, 2 * d < q → IsZero (...)`. Correct. This is zero as a module
    sheaf. Nonnegative indexing loses no vanishing degrees since d is nonnegative.

Edge cases: the empty base and empty source are allowed; empty fibres have
Krull dimension bottom and satisfy hfib. No geometric point must exist. d=0
asserts vanishing exactly in positive degrees; q=0 remains in constructibility.
N=0 is excluded exactly by positivity; N=1 permits the zero coefficient ring,
as required. The zero sheaf is allowed. Positive characteristic is restricted
only by invertibility on S. The universe u is arbitrary, the fields testing
geometric fibres have exactly the dependency's universe, and the coefficient
universe u+1 is that of the recorded small-etale module-sheaf convention. No
extra universe equality, small independent test universe or hidden binder occurs.
There is no index-set hypothesis. All variables and universes are explicitly bound.

Independent searches performed: msearch leanfinder with “Proper pushforward
preserves finite stratified locally constant etale modules and vanishes in
degrees greater than twice relative dimension” returned eight unrelated etale,
limit and condensed-module results; loogle `"higherDirectImage"` returned no
hits; msearch grep `proper.*directImage|directImage.*proper|cohomological.*dimension`
returned no hits. Direct rg searches of Mathlib, upstream WeilConjectures and
project lean/Sheaf for proper/constructible phrases and higher direct images
found the project theorem `Etale.proper_directImage_finiteness`. I opened its
whole module: its Noetherian, finite-dimensional source/base, chosen
algebraic-closure-fibre bound and stalkwise additive-order coefficient hypotheses
are not this node's signature. Curve assertions and derived stability statements
also do not state this theorem. No exact existing declaration was found.

No mismatch was found, and no Lean or node change was needed. No new definition
nodes, dependency modules or statement correction are present. The module has
one named theorem with sorry as its whole proof and no hollow definition.
Its docstring carries all seven proof steps with their ingredient node IDs;
module and theorem identify the source and blueprint ID. Every line is at most
100 characters, and the node lean.statement is verbatim the file signature.

Validation: I independently ran scompile.py NP thm-fin-proper-case on the sole
delivered Lean file. Both sandbox and library-module compiles passed with no
diagnostics (3.3 s and 3.5 s), using the required server-only compile workflow.
