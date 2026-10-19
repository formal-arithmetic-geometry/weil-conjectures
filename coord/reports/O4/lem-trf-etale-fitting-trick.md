## Worker report

The delivery states `AlgebraicGeometry.exists_fg_fitting_factor` in
`lean/Sheaf/RingTheory/EtaleFittingTrick.lean`.  It is the finite-free specialization
of Stacks Project, `flat.tex`, Tag 0812, recorded by the node
`lem-trf-etale-fitting-trick`.

The returned H3 universe defect is repaired: the source ring is `A : Type u`, the
algebra is `C : Type v`, and the affine étale hypothesis uses the canonical
common-universe lift `RingHom.ulift.{max u v, max u v, u, v}` of
`algebraMap A (Localization.Away h)` before `CommRingCat.ofHom` and `Spec.map`.

The binders render the statement as follows.  `A : Type u` and `C : Type v` are
commutative rings with an `A`-algebra structure; `d : ℕ` and
`b : Module.Basis (Fin d) A C` express that `C`
is free over `A` with a basis of `d` elements.  `h : C` names the element at which the
localization `Localization.Away h` is taken.  The typeclass hypothesis
`AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (RingHom.ulift ...)))` is the
étaleness of the canonically lifted `Spec C_h → Spec A`; the `ULift` makes this
morphism well-typed for arbitrary independent ring universes without restricting to
`u = v`.  `K : Ideal C` is
the quotient ideal, and `π : (Fin n → A) →ₗ[A] C ⧸ K` together with `hπ` is the chosen
surjective `A`-linear presentation of `C/K`; `n : ℕ` permits the zero-generator case.

The conclusion introduces an ideal `L` of `C_h`.  Its first conjunct is exactly the
factorization
`map(A → C_h) (π.presentationFittingIdeal 0) =
 map(C → C_h) K * L`.  The second conjunct says that when `K` is finitely generated,
both the zeroth kernel-minor ideal of the chosen presentation and `L` are finitely
generated.  This is the Lean rendering of the node's two final clauses, while retaining
an arbitrary fixed presentation as required by the source statement.

The imported dependency declaration is
`LinearMap.presentationFittingIdeal` and its surrounding module
`Sheaf.RingTheory.PresentationFittingIdeal`; this is the recorded declaration of
`lem-trf-fitting-ideal-independence-base-change`.  The module also imports Mathlib's
`AlgebraicGeometry.Etale`, `AlgebraicGeometry.Spec`, `Localization.Away`, and
`Module.Basis` for the recorded Mathlib dependencies
`def-weil-etale-morphism`, `def-weil-affine-spectrum`,
`def-weil-ring-localization-away`, and `def-weil-pbc-free-module`.

Edge cases checked before writing the statement were `d = 0` (the empty basis and the
zero ring module case), `n = 0` (the unit zeroth-minor convention), `K = ⊥`, `K = ⊤`,
and `h = 0` or nilpotent (the localization and etale hypothesis remain explicit).
No extra hypotheses on Noetherianity, finite type, or nonzerodivisors were introduced.

Searches performed by the previous split and rechecked against the current tree:
`msearch.py ... leanfinder` for the finite-free etale Fitting factorization (semantic
hits only on etale loci and different ideals); `msearch.py ... loogle` for
`Module.fittingIdeal, Ideal` (no hits; `Module.fittingIdeal` is unknown);
`msearch.py ... grep` for `Fitting|fittingIdeal|fitting_ideal` and for
`fittingIdeal|FittingIdeal|Fit_0` (no matching Mathlib declaration of this theorem);
`rg` over `lean/Sheaf` and `WeilConjectures` (only the kernel-row Fitting infrastructure
and the existing higher-level etale ideal-local-factor statement).  Thus no existing
exact declaration was found.

Compilation used the required wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N4 lem-trf-etale-fitting-trick
lean/Sheaf/RingTheory/EtaleFittingTrick.lean`; the sandbox and library compilation both
completed cleanly, with only the expected `sorry` declaration warning suppressed by the
project options.

## Second reading by N4

Fresh repair reading of the retained packet, with the node, module, dependency
records and declaration sources open. No mathematical mismatch was found.
`[CommRing A] [CommRing C] [Algebra A C]` renders the commutative ring map with
independent universes `u` and `v`; the explicit `RingHom.ulift`/`ULift` transport
renders the same canonical affine spectrum morphism in `Scheme.{max u v}`.
`d : ℕ` and `b : Module.Basis (Fin d) A C` render precisely the finite basis.
`h : C` and `Localization.Away h` give the prescribed localization, and
the `RingHom.ulift`-based `Etale (Spec.map ...)` is the stated spectrum morphism's
etaleness with its canonical universe transport. `K : Ideal C` and `C ⧸ K`
render the ideal and quotient. `n : ℕ`, the linear map `π`, and its surjectivity
hypothesis retain every chosen finite free surjection, including rank zero.
The imported `LinearMap.presentationFittingIdeal` is defined by actual
kernel-row minors, with the unit-ideal convention when `n ≤ k`, rather than
an alternative Fitting notion. `Ideal.map` gives exactly the two ideal
extensions; multiplication by the existential `L` gives the factorization.
The conditional conjunct gives finite generation of both the zeroth ideal
and that same `L` when `K.FG`, without requiring finite generation otherwise.
The cases `d = 0`, `n = 0`, `K = ⊥`, `K = ⊤` and trivial localization remain
within the statement. Stacks `flat.tex`, lemma-trick-fitting-ideal (Tag 0812),
agrees with this finite-free specialization. Every binder and universe is
explicit; no definition or additional theorem was introduced.

Compared the sandbox node with current `newtargets-dag`: only `lean` differs,
and the item has no landed Lean record there. The saved module and statement
are retained. The Lean record's date remains the current `date -u` value.
The return on immutable head `d5ae07f465a8` concerned the `--apply-fixes`
packet path `coord/reports/N4/lem-trf-etale-fitting-trick.md`. The prescribed
`deliver2.py` wrapper now packages the sandbox report and the node/module
as the three authorized delivery paths, and its initial dry run passed
(commit `9972bbbfa7`). No reviewer fix files are supplied through the rejected
path. The explicit required `scompile.py N4 lem-trf-etale-fitting-trick
lean/Sheaf/RingTheory/EtaleFittingTrick.lean` check also completed cleanly
for both sandbox and library files during this repair. The Lean universe changes
and this report record the H3 repair and the packaging self-check.
