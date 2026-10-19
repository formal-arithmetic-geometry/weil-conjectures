## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm` states
`AlgebraicGeometry.affineGroupoid_invariant_norm`, with its proof `sorry`.
It introduces no definitions and changes no mathematical statement. The only addition
to `stmt_deps` is the already landed `def-a1-scheme-groupoid-laws`, used for the
existing groupoid predicate. The node's other fields are preserved, apart from `lean`.
No repair note exists for this item in the shared checkout.

The source was read in `literature/stacks-project/groupoids.tex`,
`lemma-determinant-trick` (Tag 03BH), including its preceding norm paragraph,
and `lemma-diagram`. The theorem docstring records all three proof steps of the
node: the two pullback squares and their explicit groupoid isomorphism, the two
local determinant base changes, and basis independence followed by sheaf equality.

Clause-by-clause correspondence:

- The affine schemes `U = Spec A`, `R = Spec B` are represented by
  `(A B : CommRingCat.{u})` and the literal schemes `Spec A`, `Spec B`.
  The same explicit universe includes arbitrary rings of the chosen size and
  does not impose a smaller universe of test schemes.
- The source, target, identity, inverse and composition maps are the binders
  `s t : Spec B ⟶ Spec A`, `e : Spec A ⟶ Spec B`, `i : Spec B ⟶ Spec B`,
  and `c : pullback s t ⟶ Spec B`.
- Their groupoid laws on every test scheme are precisely
  `hG : Scheme.IsGroupoid s t e i c`. The recorded definition has the six
  source/target compatibilities and the two identity, two inverse and associativity
  laws on arbitrary test-scheme maps to the pullback. Precomposition gives the
  required functoriality; no arbitrary action or unrelated groupoid is supplied.
- Finite local freeness of both source and target is
  `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]`, the recorded upstream classes
  extending `IsFinite`, `Flat`, and `LocallyOfFinitePresentation`.
- The ring maps sigma and tau are `(Spec.preimage s).hom` and
  `(Spec.preimage t).hom`. These are the unique ring maps inducing the given maps
  of spectra, by the recorded affine-spectrum interface.
- The subring `C = {a | sigma a = tau a}` is exactly
  `RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom`.
- Every `f ∈ A` is the binder `f : A`. Its target pullback is
  `(Spec.preimage t).hom f : B`. The isomorphism `(Scheme.ΓSpecIso B).inv`
  identifies this with a global section of the arrow scheme.
- The phrase "let the norm section be N_sigma(tau(f))" is rendered by a section
  `n : A` and its defining chart property `hn`. For each `x : Spec A`, `hn`
  supplies an affine open `V` containing `x`, a finite free section algebra
  `Γ(Spec B, s ⁻¹ᵁ V)` over `Γ(Spec A, V)` via `(s.app V).hom.toAlgebra`, and
  equality of the restriction of `(Scheme.ΓSpecIso A).inv n` with
  `Algebra.norm Γ(Spec A, V)` of the restriction of that target pullback.
  This is exactly the consequent of `exists_finiteLocallyFree_norm_charts` at
  `W = ⊤`, transported through the coordinate/global-section isomorphisms.
  Its preimage-top section is canonically identified with a global section;
  the explicit restriction from `⊤` avoids a dependent cast for `s ⁻¹ᵁ ⊤ = ⊤`.
  The `letI` only installs the indicated algebra structure; there are no ordinary
  let-bound objects in the statement.
- This witness formulation does not add a mathematical assumption on the groupoid:
  the cited norm-chart theorem supplies such an `n` for every `f`. Nor is `n`
  arbitrary: local determinant compatibility and the sheaf equality axiom uniquely
  determine it. Two choices of charts have common affine refinements, on which
  scalar extension of multiplication determinants agrees, so their sections agree.
  Thus every section satisfying `hn` is the source's norm section, and it agrees
  with the multiplication determinant on every affine open where the algebra is
  finite free. This uses the supplied dependency without introducing a second norm
  definition or choosing data from an unspecified mere existence theorem.
- The conclusion is literally `n ∈ RingHom.eqLocus ...`, hence sigma n = tau n.
  There is no conclusion about any different or merely chosen map.
- There are no constant-rank, reducedness, global-freeness, or relation-monomorphism
  assumptions, exactly as required in the last sentence of the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  `Spec`, `Spec.map`, and `Scheme.ΓSpecIso` (global sections of a spectrum).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage`,
  `Spec.homEquiv`, `Spec.map_preimage`, and `Spec.preimage_map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`, with scheme
  pullbacks provided through `Mathlib.AlgebraicGeometry.Pullbacks`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` (and its degree variant, read but not assumed).
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts`:
  `exists_finiteLocallyFree_norm_charts`; its chart specification is used verbatim
  after the explicit coordinate/global-section transports described above.
- `Mathlib.RingTheory.Norm.Defs`: `Algebra.norm`, on the finite free local charts.
  Its determinant interpretation is the recorded `LinearMap.det` from
  `Mathlib.LinearAlgebra.Determinant`, with `LinearMap.det_toMatrix`.
- The proof-only dependencies `lem-weil-pbc-fibre-product-affine-spectra` and
  `def-weil-pbc-matrix-determinant` are the Mathlib declarations `pullbackSpecIso`
  (with its two projection formulas) and `Matrix.det` / `Matrix.det_apply`.
  Their modules are imported without `public`, along with the endomorphism
  determinant module, to retain the DAG proof plan.
- The additional landed definition is `Scheme.IsGroupoid` from
  `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws` (node
  `def-a1-scheme-groupoid-laws`). No dependency interface repair is necessary.

Edge cases checked before writing:

- If `Spec A` is empty, `A` is the zero ring, `hn` is vacuous, and the unique
  coordinate element is invariant. The theorem does not exclude this case.
- The identity section rules out a rank-zero source fibre over an actual point,
  but no positive-rank assumption is imposed. The chart norm still uses the
  correct empty determinant `1`; the empty base case remains valid.
- Rank may differ on components. Freeness is required only on each local chart,
  not on the global arrow algebra. In particular `Algebra.norm A` of the global
  arrow algebra is deliberately not used, since its fallback when a finite basis
  does not exist would not be this norm.
- Rings with nilpotents and non-free globally projective arrow algebras are covered.
  No integral-domain, field, reducedness, or positive-rank instance occurs.
- The identity groupoid has n = f, so the conclusion is the equalizer of equal
  maps. For `f = 0` or `f = 1` the same chart determinant definition applies;
  no unit or nonzero hypothesis appears.

Searches performed for an existing theorem:

- `msearch.py ... leanfinder` with query "For a finite locally free affine groupoid
  the source norm of the target pullback is invariant under source and target":
  8 hits, all affine pullback/base-change infrastructure; no norm-invariance theorem.
- `msearch.py ... loogle` with query `Algebra.norm, RingHom`: 12 hits, including
  `Algebra.norm_algebraMap`, basis and change-of-ring norm identities, and field
  extension formulas; none have scheme-groupoid hypotheses or this conclusion.
- `msearch.py ... leansearch` with query "The determinant norm of the target
  pullback along a finite locally free affine groupoid is invariant": 8 hits on
  determinant conjugacy, matrix determinants and representation norms; no match.
- `msearch.py ... grep` with query `groupoid.*norm|norm.*groupoid|determinant.trick`:
  8 broad textual hits on manifold normed groupoids, free-group conventions and
  normal subgroupoids, none on this scheme norm.
- Direct `rg` of the upstream `WeilConjectures` and shared `lean/Sheaf` trees with
  `groupoid.*norm|norm.*groupoid|IsGroupoidScheme|IsSchemeGroupoid`: the existing
  groupoid definition and its basis-descent consumer; no invariance theorem.
  The other invariant-integrality module refers to this node only in its proof plan.
- `grep -rn 'lem-a1-affine-groupoid-invariant-norm'` in upstream `WeilConjectures`
  and `rg` of `dag/lean_names_upstream.json`: no declaration for this item.
- Searches for norm charts and norm section interfaces found the recorded
  `exists_finiteLocallyFree_norm_charts` and upstream `Scheme.Hom.normAt`.
  The latter is the free-algebra norm on one open, not the glued norm for an
  arbitrary finite locally free morphism. It cannot replace the chart formulation.
- Reading the landed groupoid definition found a usable interface already carried
  by a DAG node, so there is no new definition node or duplicate predicate.

Validation: the prescribed `scompile.py NS lem-a1-affine-groupoid-invariant-norm`
compiled the delivered module successfully, including its library-name confirmation.
There were no errors or warnings. The sole postponed proof is
`AlgebraicGeometry.affineGroupoid_invariant_norm`. No STATEMENT-DISPUTED flag or
statement correction is needed.

## Second reading by NS

Independent maintainer reading, 2026-10-18, of immutable delivery
`e5c8222fba355fcf6ad5cc99f9b322760ab38c9a`. The reader did not write or previously
second-read this delivery. The packet, item node, all seven statement dependencies,
source passages, delivered module and dependency declarations were opened.

Clause-by-clause findings:

- `A B : CommRingCat.{u}` and `Spec A`, `Spec B` are the stipulated affine schemes.
  `s`, `t`, `e`, `i`, and `c : pullback s t ⟶ Spec B` have exactly the required
  domains and codomains; the composition order is later arrow first.
- `hG : Scheme.IsGroupoid s t e i c` uses the landed predicate. Its six endpoint
  equations, two unit laws, two inverse laws and associativity were checked against
  Tag 0231. The quantified pullback points supply all composable pairs by the
  universal property. Precomposition gives functoriality. The test schemes use the
  same universe as the rings, not an independent smaller universe; testing on the
  scheme domains of the laws already implies the morphism equations, so larger
  test schemes introduce no additional mathematical restriction.
- Both finite locally free hypotheses are present, via the upstream class extending
  `IsFinite`, `Flat`, and `LocallyOfFinitePresentation`. No degree instance is used.
- `(Spec.preimage s).hom` and `(Spec.preimage t).hom` are the canonical sigma and tau,
  by the fully faithful spectrum correspondence. `RingHom.eqLocus` has carrier
  exactly `{a | sigma a = tau a}`.
- `f : A` is arbitrary. `n : A` and `hn` specify its target-pullback source norm.
  `Scheme.ΓSpecIso` has direction `Γ(Spec A, ⊤) ≅ A`, so its inverse in `hn` has the
  correct direction. The algebra structure is exactly `(s.app V).hom.toAlgebra`.
  Each chart is affine, contains the point, and has finite free source section
  algebra. `Algebra.norm` is the determinant of multiplication on these charts.
- This is a legitimate characterized witness, not an extra hypothesis or arbitrary
  map: `exists_finiteLocallyFree_norm_charts` at `W = ⊤` supplies it for every `f`.
  Restriction along `s⁻¹(⊤) = ⊤` transports the input section. Common affine
  refinements, determinant base change, and sheaf separatedness make any two such
  witnesses equal. The same argument identifies the section on every finite-free
  affine chart, not only the chosen cover. No global `Algebra.norm A B` fallback is
  used and no second norm definition is introduced.
- The conclusion `n ∈ RingHom.eqLocus ...` is precisely sigma n = tau n, hence the
  node's norm-invariance assertion. Every conclusion clause is present.

The three proof steps in the theorem docstring match the node and Tag 03BH:
`(a,b) ↦ (c(a,b),b)` and `(h,b) ↦ (c(h,i(b)),b)` are mutually inverse over the
second projection; the source/target equalities have the correct orientation.
Both pulled-back multiplication matrices compute the same endomorphism, and
basis independence followed by the sheaf equality axiom gives the conclusion.
Tag 0BD2 states positive constant degree, but its determinant construction works
on each rank stratum; Tag 03BH itself assumes only finite local freeness. Thus no
constant-degree hypothesis should be added here.

Edge cases: the zero base ring and empty spectra, identity groupoid, `f = 0`,
`f = 1`, varying component ranks, nilpotents, globally nonfree finite projective
arrow algebras, and groupoids with isotropy are all included. An identity section
forces nonempty source fibres over actual points, but no positivity assumption
is imposed. Rank-zero determinants are 1, including the empty-chart case.
No characteristic, reducedness, freeness of the relation, monomorphism, field,
Noetherian or separation assumption appears.

One-definition-per-notion: independently searched the allowed Mathlib,
WeilConjectures and group Sheaf trees for `invariant.*norm`, `norm.*invariant`,
`determinant.trick`, and `normAt`. No existing scheme-groupoid invariant-norm
statement was found. The upstream `Scheme.Hom.normAt` is only a chartwise
`Algebra.norm` and cannot replace the glued locally free norm. The worker's
LeanSearch, LeanFinder, Loogle and textual searches are recorded above; their
partial matches do not state this theorem. The existing norm charts and groupoid
predicate are reused, not copied.

Records and pilot gates: `lean.statement` was compared programmatically with the
exact file signature and is verbatim equal. One theorem, one `sorry`, no new
definitions or local proofs; every binder is explicit or supplied by the bound
scheme objects, and `u` is declared. No line exceeds 100 characters. Both
module and theorem docstrings give source and blueprint, and the theorem carries
all three proof steps. Proof-only imports support the stated proof plan. No new
nodes, dependency repairs, or statement correction are needed. The newly cited
already-landed groupoid-laws dependency is allowed by brief-stage2 §5.

Route pivot: read the shared `origin/newtargets-dag:coord/route-pivot-dropped.txt`;
none of the item's statement/proof dependencies or blueprint ancestor chain are
on it. The named item repair note does not exist. This elementary scheme and
matrix proof introduces none of the dropped machinery and makes no pro-etale
substitution.

Compiler reproduction: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NS
lem-a1-affine-groupoid-invariant-norm <immutable snapshot module>` returned exit 0.
The wrapper compiled `Sheaf/Stage2/Sandbox0.lean` using a private `.lbuild` overlay
(13.9 s reported), then confirmed the library name
`Sheaf/AlgebraicGeometry/AffineGroupoidInvariantNorm.lean` (79.3 s wrapper elapsed,
including orchestration/slot time). Both phases emitted no Lean diagnostics;
the progress explicitly retained the 60 s per-invocation limit after slot acquisition.
The installed wrapper orchestrates server confirmation; no direct ssh was run.
Findings are also recorded in the independent `review.md`.
The sole report defect was the placeholder under this heading (H11). This complete
replacement preserves the Worker report and supplies the actual second reading.
The Lean module and node require no changes. No repository was edited, no branch
head changed, and no global build or live Lean write was performed.
