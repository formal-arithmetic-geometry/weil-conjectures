## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages` states
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_isProjective` with the
whole proof postponed by `sorry`. It introduces no definitions and changes only the
item's `lean` record. Read the immutable item and its blueprint source (order 1619),
the unit context, both statement dependencies and their actual declarations.

Hypothesis and clause correspondence:

- The base field is `(k : Type u) [Field k]`.
- Schemes over that field are `{X S : Scheme.{u}}` with their two
  `Over (Spec (.of k))` instances. Finite type is rendered, for each structural
  morphism, by `LocallyOfFiniteType` and `QuasiCompact`, exactly as in the
  recorded `HasConstructibleHigherDirectImages` interface.
- The fixed finite coefficient ring of `C` is `(Λ : Type (u + 1)) [CommRing Λ]
  `[Finite Λ]`, together with `(N : ℕ)` and `hX`, `hS` of type
  `IsSmoothBaseChangeCoefficients N Λ X/S`. The recorded convention says `N > 0`,
  `N` annihilates `Λ`, and its global section is a unit on each scheme. These
  are the coefficient hypotheses already included in the cited definition of `C`.
- Every projective morphism is `(f : X ⟶ S) [IsProjective f]`, with no
  separateness, smoothness, surjectivity, nonemptiness, or characteristic assumption added.
  As in the node and reduction lemma, no compatibility of `f` with the two
  field structures is additionally imposed.
- The entire conclusion is `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  Its actual definition quantifies over every `q : ℕ` and every
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; constructibility of `F`
  implies constructibility of `higherDirectImage Λ f (q : ℤ) F`.
  Thus all nonnegative degrees and all constructible sheaves are covered,
  without a uniform vanishing clause or a change of coefficient category.

Dependencies used:

- `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`,
  `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages` (public import);
  its coefficient predicate is the existing
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` from
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` (public import). Read the current server
  source using `scompile.py --source`: this extends the closed-projective-space
  embedding predicate `IsHProjective` and `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine`,
  `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_projectiveLine`
  (ordinary proof-only import). Its full signature and proof-plan docstring were read.
  The other proof dependency `thm-fin-projective-line-constructible` has no recorded
  Lean declaration yet, so there is no module to import for it. It is a proof
  dependency, not a missing object in this theorem's statement.

Edge cases checked: degree zero is included because `q` ranges over `ℕ` in the
existing predicate; empty schemes, the zero sheaf and the zero coefficient ring
are not excluded. `N = 0` is excluded precisely by the fixed coefficient convention;
`N = 1` permits the zero ring. Positive characteristic is allowed whenever the
chosen annihilating integer is invertible. There is no dimension bound and no
nonempty-coordinate restriction imposed on projectivity. Universe `u` is explicit,
with the standard module-sheaf coefficient universe `u + 1`. No auto-bound
variables, file-local notation, private definitions or local instances occur.

Searches performed (2026-10-15):

- `msearch.py ... leanfinder "Every projective morphism between finite type schemes
  over a field has constructible higher direct images of constructible finite
  torsion etale module sheaves"`: eight hits, including
  `Scheme.Hom.isConstructible_image`, its locally constructible variant, and
  properness of Proj. These concern subsets or geometric morphism properties,
  not constructibility of module sheaves. Read the Chevalley signature/docstring
  in `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:165`.
- `msearch.py ... loogle '"constructible", "projective"'`: zero hits.
- `msearch.py ... grep 'constructible.*[Pp]rojective|[Pp]rojective.*constructible'`:
  zero Mathlib hits.
- `rg` in the upstream `WeilConjectures` tree and project `lean/Sheaf` for
  `HasConstructibleHigherDirectImages|projective.*[Cc]onstructib|constructib.*[Pp]rojective`:
  project hits include the predicate, reduction lemma, cancellation lemma and
  unrelated coherent-rank results; upstream has only an unrelated perfect-local-model
  docstring. No unconditional theorem matches this item.
- Upstream grep for the item id and chosen full-name suffix, and the upstream
  declaration-name index: no matching declaration.

No statement correction, new node, dependency repair or statement dispute is needed.
The declaration docstring carries both exact DAG proof steps and names their nodes.
Validation: server-only `scompile.py` compiled the proof-dependency overlay (3.7 s),
the sandbox module (3.3 s), and the library-path module (3.7 s), without diagnostics.
`deliver2.py NW thm-fin-projective-constructibility-complete --no-push` printed
`OK (dry run)`: compilation and preflight pass, with the independent second reading
left for the assigned second reader; nothing was pushed.


## Second reading by NW

Read independently against the immutable DAG statement, both complete proof steps,
its blueprint source at order 1619, the unit statement, and the definitions of C,
the coefficient convention and projectivity. The item's source is the blueprint,
not a Stacks theorem. For the projectivity dependency I also read Stacks
`morphisms.tex`, Definition `definition-projective` (Tag 01W8): the blueprint
explicitly selects the H-projective convention, rather than Stacks' broader notion.

Object/hypothesis/conclusion checklist, with the Lean file open:

- Base field k: `(k : Type u) [Field k]`. Matches; there is no algebraic-closure,
  perfection or characteristic-zero assumption.
- Source X and target S over k: `{X S : Scheme.{u}}` and the two
  `.Over (Spec (.of k))` instances. Matches. The source states a scheme morphism
  between finite-type k-schemes, as does the recorded C interface; it does not
  require an additional `IsOver` instance for f.
- Finite type of each scheme: `LocallyOfFiniteType` and `QuasiCompact` on each
  structural morphism. Matches the scheme conventions; there is no extra
  separatedness, Noetherian instance or dimension hypothesis.
- Fixed coefficient data from C: `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`, with `hX` and `hS : IsSmoothBaseChangeCoefficients N Λ X/S`.
  Opened `SmoothBaseChangeCoefficients.lean`: these assert positivity of N,
  finiteness, `(N : Λ) = 0`, and invertibility of the constant global section N
  on the respective schemes. Matches the source's inherited convention.
- Every projective morphism: `(f : X ⟶ S) [IsProjective f]`. Opened the current
  server module through `scompile.py --source
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective` extends
  `IsHProjective f` and `QuasiCompact f`; the former supplies a finite homogeneous
  coordinate type and a closed immersion over S with composite f. This is exactly
  the node's projective-space-embedding convention. Matches.
- Conclusion C(f): `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  Opened `ConstructibleHigherDirectImages.lean`: its body quantifies first over
  every `q : ℕ`, then every `F : Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)`, and assumes `Scheme.IsConstructibleEtaleModuleSheaf F`
  to conclude that same predicate on `higherDirectImage Λ f (q : ℤ) F`.
  Opened the constructibility definition (finite locally closed constructible
  stratification, finite constant module models on etale trivializations) and
  upstream `SmoothBaseChange/Defs.lean` (higher image is homology of derived
  pushforward of F in degree zero). Matches all clauses and quantifiers, with
  no uniform vanishing conclusion.

Opened both statement dependency node records and the proof reduction's actual
signature in `ProjectiveConstructibilityFromLine.lean`. Its conclusion agrees
with this theorem. The two-step proof docstring faithfully supplies the universal
line hypothesis and applies that reduction. The line theorem has no Lean record
in the immutable checkout, so its absent proof-only import is correct and does
not leave a missing object in the present statement. No new nodes or dependency
modules were delivered, and no statement correction requires a citer audit.

Edge cases: q = 0 is included; no negative degree is requested by the node.
Empty X or S, the zero sheaf, the zero ring and projective dimension zero are
not excluded. An empty homogeneous coordinate type in the upstream interface
adds only empty-source cases already covered by ordinary projectivity. N = 0
is excluded exactly by the coefficient convention; N = 1 allows the zero ring.
Positive characteristic is allowed precisely when N is invertible. There are no
index-set binders to restrict. The explicit arbitrary u and the standard u+1
coefficient/sheaf universe match the dependency interfaces; no extra universe
equality or hidden auto-implicit variable occurs.

Independent searches used different wording from the first reader:

- `msearch.py ... leanfinder "Projective pushforward of finite locally constant
  stratified etale module sheaves is constructible in every cohomological degree"`:
  eight results, concerning condensed module constructors and coherent-site
  comparisons, not this theorem.
- `msearch.py ... loogle '"higherDirectImage"'`: zero results.
- `msearch.py ... grep 'higherDirectImage|constructible.*pushforward'`: zero
  Mathlib results. Direct `rg` on Mathlib, upstream WeilConjectures and project
  `lean/Sheaf` for projectivity/constructibility in either order and the proposed
  declaration name found no exact existing theorem. Opened the nearby
  `isConstructibleAbelianSheaf_higherDirectImage_constant_of_projective_curve`:
  it assumes relative dimension at most one and constant finite abelian sheaves,
  so cannot replace this unrestricted module-sheaf statement.

No mathematical mismatch, hollow definition, proof added, missing dependency
interface or unbound variable was found. The only repair is formatting the
node's `lean.statement` to be literally the full multiline signature from the
file (the worker had joined the theorem name and first binder). The Lean file
is unchanged. Source/blueprint docstrings and the proof plan are complete,
imports follow the public/proof-only convention, and all lines meet the limit.
Server-only `scompile.py NW thm-fin-projective-constructibility-complete` compiled
the delivered file in both sandbox and library-path forms cleanly (3.5 s each),
with no diagnostics. Compilation used the mandated isolated server workflow.
