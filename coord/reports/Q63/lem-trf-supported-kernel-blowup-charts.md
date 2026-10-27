## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedKernelBlowupCharts` states
`AlgebraicGeometry.SupportedKernelBlowupCharts.supported_kernel_blowup_charts`.
Its proof is `sorry`. Its four helpers contain real data or a proposition
packaging a clause of this same statement. They construct the affine centre
using Mathlib's ideal-sheaf constructor, the standard generator chart using the
upstream homogeneous localization equivalence, the actual tilde of the torsion
inclusion, and the sectionwise assertion that this inclusion presents the
supported-section kernel. No independent mathematical notion is replaced.

Sources read: `divisors.tex`, lemma-blowing-up-affine (0804) and
lemma-strict-transform-different-centers (080H), including its affine reduction;
`properties.tex`, lemma-sections-supported-on-closed-subset (07ZP), including the
restriction-kernel description in its proof. Also read the current
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`
to check the ancestry, without changing that unit.

Hypotheses and clauses:

* `A : Type u`, `[CommRing A]`, `I : Ideal A`, `r : ℕ`,
  `g : Fin (r + 1) → A`, and `hg : Ideal.span (Set.range g) = I`
  render the ring and the finite list of generators. Repetition and zero
  generators are permitted. `x : A` has no regularity hypothesis.
* `Spec (.of A)` is S. `center I` is the ideal sheaf induced by I using
  `Scheme.IdealSheafData.ofIdealTop` and the inverse of `Scheme.ΓSpecIso`.
  `(center I).blowup` and `.blowupMap` are exactly the recorded global blowup,
  rather than a second definition of a blowup. `e` identifies it with the
  existing affine Rees blowup, and its equation requires compatibility over S.
* `X : Scheme.{u}`, `f : X ⟶ Spec (.of A)`, `F : X.Modules`, and
  `[F.IsQuasicoherent]` render the arbitrary scheme morphism and quasi-coherent
  module. No finite-type, flatness, coherence, or torsion-free assumption occurs.
* `pullback f (center I).blowupMap` is T, and `pullback.fst` and `pullback.snd`
  are p and q. The category is explicitly `Scheme.{u}` in the object terms to
  avoid confusing a scheme pullback with a pullback of underlying types.
* For every `i`, `chart I e (g i) (hgI i)` is the standard Spec B chart.
  It is the composite of Spec of `homogeneousAwayEquivChart`, the upstream
  `AffineBlowup.chart`, and `e.inv`. The existential `hgI` supplies the
  generator membership proofs forced by `hg`; it adds no assumption.
* The pointwise cover clause finds an affine open `U` above p(z) and a generator
  chart above q(z) for every z in T. The subsequent range equation identifies
  each W with exactly the intersection of these two inverse images. Together
  these are the claimed affine open cover (not merely a family of morphisms).
* An arbitrary affine presentation U = Spec R in X is represented by
  `R : Type u`, `[CommRing R]`, `[Algebra A R]`, an open immersion
  `v : Spec (.of R) ⟶ X`, and `_hv` identifying its composite to S with the
  structural Spec map. This is coordinate data, not a restriction on the
  affine opens. `M : ModuleCat R` and `_eM` are the given identification of
  the restricted/pulled-back module with `tilde M`.
* B is the recorded `AffineBlowup.chartRing I (g i)`. C is the recorded
  `AffineBlowup.BaseChangeChart R I (g i)`, definitionally R tensor_A B.
  The domain of j is Spec C. `IsOpenImmersion j`, its two projection equations,
  and its range equation identify this domain with U times_S Spec B in T,
  with precisely the two canonical tensor-product structural maps. The
  projection equations determine j by the pullback universal property.
* The two preimage equations are exactly the inverse images of V(I) and
  V(I) union V(x); their right sides are V(a) and V(xa) in Spec C. In every
  occurrence, a and x act through `algebraMap A C`. In particular the ideal
  I is not replaced with its radical in the ring construction.
* E identifies the restriction of p-star F to W with `tilde (C ⊗[R] M)`.
  This is N in the node with tensor factors reversed by the standard tensor
  symmetry: C tensor_R M is canonically M tensor_R C. Both are C-modules
  with C acting on its own factor. The explicitly normalized A-linear
  equivalence α with B tensor_A M is the node's alternative presentation
  M tensor_A B, again under symmetry. Its formula is
  `(s tensor b) tensor m ↦ b tensor (s • m)`, exactly the node's
  `m tensor (s tensor b) ↦ (s • m) tensor b` in these conventions.
* The two `PresentsSupportedKernel` conjuncts, with t = a and t = xa,
  retain the inclusions into the same ambient sheaf E. `inclusion` is the
  actual `tilde.map` of `(Submodule.powTorsion C N t).subtype` followed by
  E.hom, not an arbitrary embedding. For EVERY open V and section s, the
  predicate says that restriction to V intersect D(t) is zero iff s is in
  the image of this inclusion on V; it also records that this is a mono.
  These equalities of subfunctors on all opens say exactly that the
  restrictions of K and L are the two associated torsion subsheaves,
  including their actual inclusions. Naming globally chosen sheaf objects
  K and L is unnecessary: their defining sectionwise kernel is recorded
  directly. The preimage equations identify their complements with D(t).
* `Submodule.powTorsion` is the recorded power torsion, including exponent
  zero. The same E is used for both torsion subobjects. There is no
  x-torsion-freeness assumption on M and no nonzerodivisor assumption on x.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`, `Scheme.ΓSpecIso`.
* `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `Scheme.IdealSheafData.ofIdealTop`.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`.
* `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`,
  `AffineBlowup.homogeneousAwayEquivChart` (including its full signature).
* `WeilConjectures.Blowup.Affine.StrictTransformChart`:
  `AffineBlowup.BaseChangeChart`.
* `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`,
  `AffineBlowup.chart`, its open-immersion instance and `opensRange_chart`.
* `WeilConjectures.Mathlib.Algebra.Module.Torsion`: `Submodule.powTorsion`
  and the membership signature `Submodule.mem_powTorsion_iff`.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsQuasicoherent` for pqf-def-coherent; the conjunction with
  finite type is NOT imposed.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: exposes the
  recorded `Scheme.Modules.tensorPullback` and its normalized adjunction.
* `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.map`,
  `tilde.toOpen`, `tilde.toOpen_res`, `tilde.adjunction`, and the
  quasi-coherent counit interface.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and their universal property.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  was read as recorded; no arbitrary closed-immersion hypothesis is added
  merely to refer to the closed sets V(I) and V(x).

Available proof-dependency modules are imported privately:
`WeilConjectures.Blowup.FiniteDegree.Algebra` (finite chart cover),
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections` (canonical
section tensor comparison), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` (quasi-coherent
pullback). Mathlib affine fibre products, open-immersion base change,
principal-open localization, compactness, and tilde-Gamma are already
available through the imports. The proof-only node
lem-trf-supported-sections-quasi-coherent has no published Lean record in the
read DAG, so there is no module of that node to import. Its statement is
used in the natural-language proof, not assumed as a hypothesis.

Edge cases checked: A the zero ring; I = 0 (all standard chart rings are zero,
and the blowup and T are empty); I = A; a zero or nilpotent generator (its
chart is empty); repeated generators; r = 0; X empty; F or M zero; x = 0
(the second support is all of W and its power torsion is all of N); x a unit
(the two supports and kernels agree); x a zero divisor; and modules with
nonzero x-torsion. Exponent zero kills only the zero element and causes no
exception. No cancellation of a or x occurs. All module and scheme size
binders are explicit, and `autoImplicit` is disabled.

Searches actually run with the prescribed msearch wrapper:

* LeanFinder: “On affine blowup base change charts supported subsheaves of a
  pulled back quasi coherent module identify with power torsion including
  their inclusions”. Eight results, concerning scheme structure-sheaf
  restriction, ideal sheaves and localization, not the module statement.
* Loogle: `Submodule.powTorsion, AlgebraicGeometry.tilde`. The public service
  does not know the project's `Submodule.powTorsion`; no hits. Its declaration
  was instead read directly in the upstream module above.
* Mathlib grep: `supportedSections|sectionsSupported|powTorsion` under
  AlgebraicGeometry: no hits.
* LeanSearch: “For a quasi coherent module on a base change of a blowup the
  supported section kernel on an affine chart is the sheaf of power torsion”.
  Eight results, primarily quasicoherence definitions and ideal sheaf kernels;
  none is this theorem.
* `rg` in the upstream source found the existing power-torsion definition and
  strict-transform chart calculation, whose ring-kernel theorem concerns C
  itself rather than the two supported subsheaves of an arbitrary pulled-back
  module. Search for the item id in upstream had no hits.
* `rg` in lean/Sheaf found supported étale/derived-section constructions but
  no `PresentsSupportedKernel` or `supported_kernel_blowup_charts` declaration.

No statement correction, dependency repair, new node, or mathematical dispute.

## Second reading by Q63

Independent reading (maintainer second reader, 2026-10-24), with the node
`lem-trf-supported-kernel-blowup-charts`, its eleven stmt_deps, the Stacks places
(divisors 0804, 080H (2); properties 07ZP) and the module
`Sheaf.AlgebraicGeometry.SupportedKernelBlowupCharts` open. It replaces the
author's own second pass. Does the Lean say exactly what the node says? Yes.

Node objects and hypotheses:

- A commutative ring, I = (f_0,…,f_r), x ∈ A: `A : Type u` `[CommRing A]`,
  `g : Fin (r+1) → A`, `hg : Ideal.span (Set.range g) = I`, `x : A`. Exact; at
  least one generator as in the node; no regularity of x.
- S = Spec A, Z = V(I), D = V(x): `Spec (.of A)`, `PrimeSpectrum.zeroLocus`.
  Exact (the closed sets are only used through their points/complements).
- b : Bl_I(S) → S: `(center I).blowup`, `.blowupMap` = recorded
  def-nagata-global-blowup, with `center I = ofIdealTop (I.map ΓSpecIso.inv)`, the
  ideal sheaf Ĩ. Exact; no second blowup definition.
- f : X → S arbitrary, F quasi-coherent: `X : Scheme.{u}`, `f`, `F : X.Modules`,
  `[F.IsQuasicoherent]` (pqf-def-coherent record lists SheafOfModules.IsQuasicoherent).
  No finite-type assumption. Exact.
- T, p, q: `pullback f (center I).blowupMap`, `pullback.fst/snd` in `Scheme.{u}`. Exact.
- U = Spec R affine open with F|_U = M~: `R`, `[Algebra A R]`, open immersion
  `v : Spec R ⟶ X`, `_hv : v ≫ f = Spec.map (algebraMap A R)` (forces the algebra
  structure induced by f), `_eM : v^*F ≅ tilde M`. Every affine open admits such a
  presentation; nothing stronger is assumed.
- B = A[I/a], C = R ⊗_A B: recorded `AffineBlowup.chartRing I (g i)` and
  `AffineBlowup.BaseChangeChart R I (g i)`. Exact.

Conclusion clauses:

- e : Bl ≅ AffineBlowup I over S. Existential but unique (S-endomorphisms of a
  blowup are the identity by its universal property), so `chart I e (g i) _` is
  the canonical standard chart Spec A[I/a] → Bl (homogeneousAwayEquivChart, upstream
  AffineBlowup.chart at reesX a). Not arbitrary.
- W = U ×_S Spec B ≅ Spec C as an open cover of T: j open immersion, both projection
  equations with the canonical algebraMap/includeRight maps (determine j), range =
  p⁻¹U ∩ q⁻¹(chart), and the pointwise cover clause. Exact.
- closed subsets V(a), V(xa): preimage equations of V(I) and V(I) ∪ V(x) under
  Spec C → S, with a, x acting through A → C. Exact.
- pullback module Ñ, N = C ⊗_R M (symmetry of M ⊗_R C): ∃ E. E is existential, but
  every automorphism of Ñ is C-linear on N and preserves Γ_(t)(N), so the subsheaf
  assertions below do not depend on the choice. The alternative presentation
  M ⊗_A B: ∃ α pinned on generators by (s⊗b)⊗m ↦ b⊗(s m); checked well defined
  (R- and A-balanced) and bijective (inverse b⊗m ↦ (1⊗b)⊗m).
- K|_W, L|_W with inclusions: `PresentsSupportedKernel` for t = a and t = xa:
  `inclusion` = tilde.map of the actual `(powTorsion C N t).subtype` followed by E,
  mono, and on every open V a section lies in its image iff it restricts to zero on
  V ∩ D(t) — i.e. iff it vanishes off V(t) = W ∩ q⁻¹b⁻¹(Z) (resp. Z ∪ D). This is
  07ZP's subsheaf of sections supported in the closed set, on every open. Exact.

Edge cases: I = 0 (empty blowup and T; clauses vacuous/true), a nilpotent (empty
chart), x = 0 (V(xa) = W and Γ_(0)(N) = N since 0^1 kills N; D(0) = ∅ so every
section is supported), x a unit (K = L), repeated
generators, X empty, M = 0. Universes: one universe u throughout, as forced by
f : X ⟶ Spec A and Mathlib's tilde. Statement field equals the file signature
verbatim; the only `sorry` is the theorem's proof; the four helpers carry real
data and source/blueprint docstrings; the theorem docstring carries the node proof.

Searches: upstream `IdealSheafData.blowupChart` (ChartProbe) is the chart over an
affine open with Γ(X,V)-coefficients, not over A; the delivered chart is the same
map transported along the unique e (advisory, not a duplicate notion). Sister
lem-trf-supported-kernel-flat-pullback (Q74) encodes supported kernels as kernels of
restriction units in its own theorem module; not a recorded def node, so no reuse
obligation (advisory). No Mathlib/project declaration states this result.

Change: this section only (the author's second pass was a self-audit).
