## Worker report

Repair of return L on immutable head `9137e1e24578`: H1 reported the missing
complete Lean module, missing `lean` record, and incorrect report heading. That
head contained a stage-1 split report and no Lean statement. The retained sandbox
contained only dispatcher marker files. This delivery supplies the complete stage-2
module `Sheaf.AlgebraicGeometry.FiniteSurjectiveAmpleReflection`, the current-base
node with its complete `lean` record, and this stage-2 report. It does not replay
the stage-1 `split_report` change. The mathematical statement is unchanged.

The single declaration is
`AlgebraicGeometry.isAmple_iff_tensorPullback_of_isFinite_surjective`.
It has precisely one `sorry`, for its proof; there are no definitions or auxiliary
postponed theorems. Its docstring carries all seven steps of the node's proof,
including the references used at each step. All variables and the universe are
explicitly bound, and both auto-implicit options are disabled.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring is `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`.
- The two schemes are `(X Y : Scheme.{u})`. Their structure morphisms to
  `Spec R` are given by `[X.Over (Spec (CommRingCat.of R))]` and
  `[Y.Over (Spec (CommRingCat.of R))]`.
- Properness over the base is `[IsProper (X ↘ Spec (CommRingCat.of R))]`
  and `[IsProper (Y ↘ Spec (CommRingCat.of R))]`. No projectivity,
  reducedness, integrality, flatness or dimension assumption is substituted.
- The map with the source and target in the required order is `(f : Y ⟶ X)`.
  Its compatibility with the two structure maps is
  `[f.IsOver (Spec (CommRingCat.of R))]`.
- Finiteness and surjectivity on underlying spaces are `[IsFinite f]` and
  `[Surjective f]`, respectively.
- Every invertible module is `(L : X.Modules) [L.IsInvertible]`.
- Ampleness downstairs is `Scheme.Modules.IsAmple X L`.
- The pullback upstairs is exactly `(Scheme.Modules.tensorPullback f).obj L`,
  the prescribed explicit tensor construction, not the abstract pullback functor.
- Ampleness upstairs is `@Scheme.Modules.IsAmple Y
  ((Scheme.Modules.tensorPullback f).obj L)
  ((Scheme.Modules.invertible_pullback_tensor f).1 L |>.2)`.
  The last term supplies the existing proof that this pullback is invertible.
  It is not a new hypothesis and chooses no module data. Proof irrelevance
  ensures that the ampleness proposition does not depend on that proof term.
- The conclusion is `↔`, so both ascent and reflection are stated.
  Both predicates are the same absolute affine-nonvanishing-locus definition,
  including quasi-compactness and positive tensor exponents; neither is relative
  ampleness nor a degree criterion.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose data are
  `IsNoetherian R R`, equivalently finite generation of every ideal.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  Its universally closed component supplies quasi-compactness, so its locally
  finite type component gives exactly the node's finite type properness.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  the affine morphism with finite section maps over all affine target opens.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`, meaning surjectivity of the underlying map.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local rank-one triviality.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  module of `def-pc-module-pullback`, publicly importing the actual upstream
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` tensor construction.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, read in the project's source.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`, first conjunct,
  second clause. Its current server source was read through `scompile.py --source`;
  it transports invertibility along the left-adjoint uniqueness comparison.
  The already recorded node `lem-weil-pbc-invertible-pullback-tensor` is added to
  `stmt_deps` solely because this existing proof supplies an argument in the
  signature. This is the authorized addition of a landed dependency, not a new node
  or a statement correction. The imported upstream module is used instead of its
  retired duplicate under `Sheaf`.

The module also imports, without `public`, every recorded module of the proof
dependencies: tensor functoriality, projection formula, exact global sections,
enough injectives, affine cohomology, affine ideal products, coherent kernels
and sums, devissage, Serre vanishing, finite coherent pushforward, generic support,
ideal-product stalks, stalk exactness, ample pullback, quasi-coherent tensors,
universal derived delta functors, sheaf cohomology and coherent finite type.
Mathlib leaves use their recorded affine-morphism, separatedness, limits,
Noetherian, quasi-compactness and spectrum-topology modules. The one proof node
`lem-trf-ideal-twist-vanishing-implies-ample` has no recorded module yet, hence
there is no existing module to import for it. No statement dependency is missing.

Edge cases checked against the source and definitions:

- No `[Nontrivial R]` is assumed. The zero ring is covered; its spectrum and both
  schemes over it are empty. The absolute ampleness condition is compactness plus
  a vacuous condition on points, so the equivalence has the expected meaning.
- Empty schemes are allowed. A surjective map with empty source forces empty
  target, and a map to an empty scheme forces empty source.
- The identity map and finite disjoint-union covers are covered. No degree,
  dominance, connectedness, normality or dimension-one assumption is introduced.
- The statement is characteristic independent. All objects share the arbitrary
  ambient scheme universe `u`, with no test-object quantification in a smaller
  independent universe and no additional universe equality.
- The canonical invertibility argument uses only invertibility of L and the
  map f; it does not assume ampleness or a downstream theorem about reflection.

Source check: read `literature/stacks-project/coherent.tex`,
`lemma-surjective-finite-morphism-ample`, Tag 0B5V, including its complete proof.
Its statement is precisely a finite surjective map between schemes proper over a
Noetherian ring, and the equivalence for an invertible module. The node's
absolute ampleness convention agrees with the imported definition. No fault or
`STATEMENT-DISPUTED` remains.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: “For a finite surjective morphism between schemes
  proper over a Noetherian ring, an invertible sheaf is ample if and only if its
  pullback is ample”: eight hits, including stability of finiteness and
  surjectivity under base change and `IsFinite.iff_isProper_and_isAffineHom`;
  none concerns ampleness descent.
- `msearch.py`, LeanSearch: “Ampleness descends along a finite surjective morphism
  of proper schemes over a Noetherian ring”: eight hits on descent of morphism
  properties and the finite-morphism recursor; none states this equivalence.
- `msearch.py`, Loogle: `AlgebraicGeometry.Scheme.Modules.IsAmple,
  AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective`: no hits; the search
  service does not index the project's `IsAmple` declaration.
- `msearch.py`, grep: `IsAmple|isAmple` in Mathlib `AlgebraicGeometry`: no hits.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` trees for
  `IsAmple|isAmple|[Aa]mpleness`, and for finite-surjective ampleness/name
  combinations: found the canonical absolute definition, pullback and tensor
  infrastructure, affine-pullback ampleness, and distinct curve/reduction
  criteria; no exact finite-surjective proper-base equivalence.
- Search for the item ID in the upstream tree: no declaration. Search for the new
  declaration's full name in upstream, project Lean and `dag/lean_names_upstream.json`:
  no collision.

Validation: the initial complete signature and the final module with all recorded
imports and the seven-step proof docstring both compiled cleanly through
`scompile.py`. The final invocation returned exit code 0 with no errors or warnings
for both the sandbox and library-path checks. No global build was run. The node's
recorded signature is byte-for-byte the file's signature, the longest Lean line
is 98 characters, and the only changes against the current node are `lean` and
the additional already landed statement dependency. The UTC date was checked with
`date -u +%F`. `deliver2.py Q38 lem-trf-finite-surjective-ample-reflection --no-push`
returned `OK (dry run)` for commit `94542a6548`: preflight and per-file compilation
both passed. Exactly the module, node record and report were staged.

## Second reading by Q38

The dispatcher instructs this worker to deliver directly and not to start other
agents; the maintainer's independent review is the independent second reading.
This section records Q38's final direct rereading without claiming another agent
performed it.

I reopened the source lemma, the current DAG node, each statement dependency's
record and declaration, and the delivered Lean signature. The source has Y as
source and X as target, and the Lean has `f : Y ⟶ X`. Both properness assumptions,
the Noetherian commutative base ring, the R-morphism condition, finiteness,
underlying-space surjectivity and invertibility of L have their explicit binders
listed above. The conclusion uses the same absolute `IsAmple` on X and Y and the
recorded tensor pullback. It is an equivalence, not just the difficult direction.
There is no additional pullback-invertibility hypothesis: the displayed term
extracts its proof from the existing theorem. No empty/zero/characteristic case
is excluded. The seven-step docstring now includes the complete DAG proof.

The return's three shape faults are repaired: a complete module is present, the
node has the full matching `lean` record, and the report heading is exactly
`## Second reading by Q38`. The first draft used a retired `Sheaf` import for
invertible pullback; the final version uses the node's current upstream module.
The full recorded tensor-pullback interface is imported. The statement dependency
list additionally names the already landed invertible-pullback theorem needed for
the explicit instance term. No new nodes, dependency repairs or statement
corrections were necessary.
