## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine` states
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_projectiveLine`.
Its sole theorem has proof `sorry`; no definitions or proofs were added.
The source read was the complete blueprint file
`sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-projective-from-line.md`,
together with the node's six-step proof and the coefficient convention in
`sec-smooth-base-change/sk-def-bc/sbc-def-coefficient-conventions.md`.

Hypothesis and conclusion correspondence:

- The fixed field is `(k : Type u) [Field k]`.
- The fixed finite commutative coefficient ring is
  `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` together with
  the recorded `IsSmoothBaseChangeCoefficients N Λ` predicates on every
  coefficient-bearing scheme. These express positivity of N, annihilation
  of Λ by N, and invertibility on the scheme, exactly as the convention
  required by the recorded definition of C specifies.
- “Every finite-type k-scheme T” is `∀ (T : Scheme.{u})
  [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
  [QuasiCompact (T ↘ Spec (.of k))]` inside `hline`.
- The projective line is `ProjectiveSpace (ULift.{u} (Fin 2)) T`:
  the index enumerates homogeneous coordinates, hence two coordinates
  give dimension one. The arrow `… ↘ T` is the canonical first projection.
- The hypothesis C for this arrow is the exact dependency predicate
  `HasConstructibleHigherDirectImages`, with `hP` and `hT` supplying its
  required coefficient proofs. Their universal quantification simply
  restricts the hypothesis to the coefficient convention's schemes.
  The explicit instance arguments use finite type of the composite
  projective-line projection followed by the structure map of T.
  They supply existing typeclass proofs, not additional hypotheses.
- X and S carry the same `Over`, `LocallyOfFiniteType`, and `QuasiCompact`
  binders. There is no separation, smoothness, or properness assumption
  on their structure maps. The node does not require f to respect the
  chosen k-structures, and the statement adds no such requirement.
- The arbitrary morphism is `(f : X ⟶ S)` and the closed-embedding
  projective convention is the recorded `[IsProjective f]`.
- The conclusion is exactly `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  Unfolding the imported predicate quantifies over every q : ℕ and every
  constructible Λ-module sheaf and asserts constructibility of its higher
  direct image. No boundedness or uniform vanishing clause is added.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`,
  `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages`: full
  signature, docstring and body read, including the finite-type and
  coefficient proof binders.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`: full predicate read.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` and `IsHProjective`: canonical upstream
  extracted module read from an available live-source clone, as this module
  is absent from the older slopmaster2 checkout. Its embedding convention
  agrees with the dependency node. The server accepted this canonical import.
  The group clone's older Sheaf module was also read, not imported or copied.
- `def-weil-pbc-scheme-conventions` intentionally has no declaration or module;
  its recorded convention uses Mathlib's finite-type pair. The actual
  `LocallyOfFiniteType` and `QuasiCompact` classes and docstrings were read
  in Mathlib's morphism modules.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace.over`, and
  `ProjectiveSpace.instIsProper`: definitions and docstrings read.
  The projective-space construction is the canonical imported construction.

Proof-only imports preserve the stated proof plan:
`Sheaf.AlgebraicGeometry.RelativeProjectiveSpace` (relative-Proj charts),
`Mathlib.AlgebraicGeometry.Noetherian` (the recorded finite-type/Noetherian
Mathlib matches), and `WeilConjectures.ConstructibleSheaf.OpenClosed`
(the recorded closed-immersion theorem). The bounded-constructible module
is already publicly imported through C. Composition, symmetric-product
finiteness and finite-surjection cancellation have no Lean records on the
inspected base, so there are no modules to import for them yet. The
closed-immersion record covers only its constructibility clause and uses
upstream constructibility; the stronger complete node statement will need
its stage-3 bridge/vanishing argument. This does not affect this signature.

Edge cases checked: empty X, S and T are not excluded; n = 0 for a projective
embedding remains covered, with the identity case explicitly in the proof
plan. `ULift (Fin 2)` fixes the projective line, not projective zero-space or
an empty coordinate set. All characteristics compatible with the coefficient
convention are admitted; no characteristic-zero hypothesis occurs. The zero
coefficient ring and zero sheaf are admitted. The same universe u covers
all schemes over k and Λ lives in u+1, matching the recorded sheaf category.
The auxiliary coefficient-proof arguments do not change the body of C,
whose definition ignores these proof arguments.

Searches actually run:

- `msearch.py` LeanFinder: “Constructibility of higher etale direct images
  for all projective morphisms follows from projective line projections”.
  Eight hits: Proj properness, valued criteria, construction from sections,
  and etale composition results; none states this implication about sheaves.
- `msearch.py` Loogle: `AlgebraicGeometry.ProjectiveSpace,
  AlgebraicGeometry.IsProjective`. Zero hits; unknown identifier
  `AlgebraicGeometry.ProjectiveSpace` in the Mathlib search index.
- `msearch.py` grep: `constructible.*projective|projective.*constructible`.
  Zero Mathlib hits.
- `msearch.py` LeanSearch: “higher direct images constructible etale sheaves
  projective morphisms reduction to projective line”. Service unavailable,
  Internal Server Error; not counted as a negative result.
- `rg` in upstream WeilConjectures and project Sheaf for
  `projective.*(construct|Construct)|[cC]onstruct.*projective` and the item id:
  only unrelated geometry/cohomology and a forward reference in the C module.
  No existing statement was found.
- `rg` of the proposed declaration names in `dag/lean_names_upstream.json`,
  upstream WeilConjectures and project Sheaf: no collision.
- Upstream projective-line base-change theorems concern torsion base change,
  not this constructibility implication, so they are not exact matches.

No node correction, new node, or dependency module was needed. No
STATEMENT-DISPUTED flag is asserted.

Validation: scompile.py compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file; this file took 2.8 seconds).
The first compile exposed an instance-synthesis issue for the composite
structure morphism; explicit composite instance terms resolved it without
changing the mathematical statement. Dry delivery check is run after this report.

## Second reading by NL

I independently read the sandbox node, its full Lean module, the original blueprint
source and its property-C and coefficient-convention sources. The source here is
blueprint Markdown, not a Stacks lemma; I additionally read Stacks morphisms.tex,
Definition 01W8 (definition-projective), for the projectivity convention.

Object/hypothesis/conclusion checklist (H3):

- Fixed field k: `(k : Type u) [Field k]`. Same field context; PASS.
- Fixed coefficients: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`,
  with `IsSmoothBaseChangeCoefficients N Λ` on the schemes in question. I opened
  SmoothBaseChangeCoefficients.lean: this is positivity of N, finite Λ,
  `(N : Λ) = 0`, and invertibility of N in global sections. These are precisely
  the source's standing hypotheses, not an extra characteristic restriction; PASS.
- Every finite-type k-scheme T: `∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]`
  with `LocallyOfFiniteType` and `QuasiCompact` of its structure morphism.
  I opened the convention node and Mathlib's two class signatures. Their pair is
  exactly finite type; neither separatedness nor smoothness is imposed; PASS.
- Projective line and its projection: `ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T`.
  I opened ProjectiveSpace.lean: the coordinates index homogeneous variables;
  two coordinates give P¹, and `ProjectiveSpace.over` is `pullback.fst` over T.
  `ProjectiveSpace.instIsProper` supplies finite type of the projection. The
  explicit composite-instance arguments supply the inherited k-structure's
  finite type and quasi-compactness, without assumptions on T beyond those
  already listed; PASS.
- Line hypothesis: `hline` concludes the exact dependency's
  `@HasConstructibleHigherDirectImages ... hP hT (...)` for every such T.
  Quantifying the coefficient proofs restricts T to the coefficient-bearing
  schemes stipulated throughout the source. Those proofs are ignored in the
  body of C, so their universal quantification adds no mathematical condition;
  PASS.
- Arbitrary finite-type X and S: their `Over`, `LocallyOfFiniteType`, and
  `QuasiCompact` instances are the same ones as for T. The node introduces a
  morphism between these schemes, not an extra compatibility equation with k;
  `(f : X ⟶ S)` follows the recorded C definition without adding one; PASS.
- Projectivity: `[IsProjective f]`. I read the canonical extracted module
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective in a live-source clone:
  `IsHProjective` is a global closed embedding into finite-coordinate projective
  space, followed by its structural morphism, and `IsProjective` extends it and
  `QuasiCompact f`. This is exactly the dependency node's explicitly chosen
  H-projective convention, rather than Stacks' broader projective-bundle notion;
  PASS.
- Conclusion: `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  I opened ConstructibleHigherDirectImages.lean and its constructibility
  dependency IsConstructibleEtaleModuleSheaf.lean: for every q : ℕ and every
  constructible Λ-module sheaf F, the higher direct image is constructible in
  the finite locally closed stratification sense. I also read the upstream
  `Etale.higherDirectImage` definition: it is degree-q homology of derived
  pushforward of F in degree zero. Thus every clause of C is present, with no
  boundedness or uniform vanishing assertion; PASS.

Edge cases: no nonempty hypothesis excludes empty X, S or T. The field remains
nontrivial by the usual field convention. Zero coefficient rings and zero module
sheaves are admitted. No embedding dimension is fixed in the conclusion: n = 0
and arbitrary finite coordinate sets are included. The empty-coordinate embedding
can only embed an empty X, already covered by the claim. The positive-dimensional
line is correctly fixed by two coordinates. There is no characteristic-zero
restriction: precisely the invertibility-of-N convention is present. The arbitrary
universe u covers all schemes in the selected universe; the finite coefficient
ring in u+1 and module sheaves in u+1 agree with the dependency's site encoding.
There is no independent smaller test-scheme universe making hline vacuous.

Independent H4 searches, using wording different from the worker's:

- LeanFinder: “Higher direct images of finite locally constant stratified etale
  module sheaves preserved by projective morphisms from preservation by P1
  projections”: eight hits concerning coherent-site projective objects and
  condensed-module internal projectivity; none states this implication.
- Loogle: `"constructible"`: twelve hits for constructible topological subsets;
  none is a sheaf higher-direct-image statement.
- msearch grep: `higherDirectImage|HasConstructibleHigherDirectImages`: no
  Mathlib hits.
- Direct rg over upstream WeilConjectures, project lean/Sheaf and the upstream
  name census for projective/constructible combinations and the full proposed
  declaration: only an unrelated pro-etale perfect-module comment and C's
  forward reference to this node. No existing statement or name collision.
- LeanSearch: “Reduction of constructibility of higher direct images along
  projective morphisms to projective line bundles”: service unavailable
  (Internal Server Error), explicitly not treated as a negative search result.

H5/H6/H8/H9: the delivered module adds no definitions or instances, and its sole
proof is `sorry`. The module and theorem docstrings cite the precise source and
blueprint id. The six docstring steps match the node's global embedding, chart
finite-type calculation, Noetherianity, product induction, finite-surjection
cancellation including n = 0, and closed-immersion composition. All universes and
variables are bound, imports use the canonical declarations and recorded proof
modules, and no local notation/private copies are introduced. No new definition
node, dependency module, or statement correction is present, so H12/H13 and the
corrected-statement citer check do not apply. The incomplete proof-only record
for lem-fin-closed-immersion is already identified in the worker report; this
module merely imports it and does not assert it supplies positive-degree
vanishing or the separate constructibility bridge.

Mismatches found: none. Lean and node signature were left unchanged. The only
change in this second reading is this detailed independent review report.

Validation of second reading: scompile.py compiled the delivered module cleanly
on the server in 2.8 seconds (nice 19, two threads, 60-second per-file limit).
A textual check confirms lean.statement is verbatim the theorem signature and
every module line is at most 100 characters.
