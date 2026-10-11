## Worker report

The module `Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology` states
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_cohomology_eq_zero` with
one `sorry` and no definitions or proofs. The node is unchanged except for `lean`.

Source read: Stacks Project, Cohomology of Schemes, Lemma 30.17.4, Tag 01XR,
https://stacks.math.columbia.edu/tag/01XR (the local literature checkout is absent).
Its statement and proof agree with the node; the proof uses localization 09MR and
affine vanishing 01XB. Both steps are included in the declaration docstring.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`, with an explicit arbitrary universe `u`.
- Quasi-compact: `[CompactSpace X]`, the recorded Mathlib declaration of
  def-weil-pbc-quasi-compact-scheme (Topology.Defs.Filter).
- Quasi-separated: `[QuasiSeparatedSpace X]`, the Mathlib scheme convention
  collected by def-weil-pbc-scheme-conventions; this requires compact intersections
  of compact opens and is the scheme quasi-separatedness condition.
- Invertible module L: `(L : X.Modules) [L.IsInvertible]`, from the recorded
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (def-sc-invertible-module).
- Global section s: `(s : Γ(L, ⊤))` is a section of L over the whole scheme.
- Affine principal open: `(U : X.Opens)` with
  `hU : (U : Set X) = nonvanishingLocus L s` and `hAffine : IsAffineOpen U`.
  U is a presentation of X_s as an open, with its precise underlying set, rather
  than an arbitrary affine open. `nonvanishingLocus` is the recorded declaration
  in `Sheaf.AlgebraicGeometry.Ample` (def-weil-pbc-ample-invertible-module).
  Introducing U with its equality does not change the hypothesis: the node
  regards X_s as an open subscheme, and this presentation is unique.
- Every quasi-coherent F: `(F : X.Modules) [F.IsQuasicoherent]`. The recorded
  module `Sheaf.AlgebraicGeometry.Coherent` explicitly uses the existing
  `SheafOfModules.IsQuasicoherent` for this clause of pqf-def-coherent; its
  `IsCoherent` declaration is not the quasi-coherent condition and is not imposed.
- Every positive degree: `(p : ℕ) (hp : 0 < p)`.
- Every class: `xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F`.
  This is precisely the module-valued right-derived global sections, as used in
  the recorded `Sheaf.Paper.PQFCohomology` for pqf-def-cohomology; its underlying
  definition is `AlgebraicGeometry.RingedSpace.moduleCohomology` in
  `Sheaf.Topology.RingedSpaceModuleCohomology`. No abelian-sheaf Ext replacement.
- Nonnegative exponent: `∃ e : ℕ` includes zero.
- Target module is `F ⊗ L.tensorPow e` by the type of the displayed morphism;
  `tensorPow` is the existing declaration in Modules.Invertible, also used by
  the recorded Ample module.
- Map `f ↦ f ⊗ s^e`: `(ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e`.
  The inverse right unitor sends f to f tensor 1, and the second-factor morphism
  sends 1 to the tensor power of s. These existing declarations are in
  `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` and its import
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`.
  The full signatures and docstrings were read, including the recursive zero
  and successor cases of tensorPowSection and homOfGlobalSection_app_one.
- Induced map on H^p and vanishing: `.map (...) xi = 0`, using the same recorded
  cohomology functor on source and target.

Dependency source files read: Mathlib's Scheme (including Scheme.Hom),
Topology.Defs.Filter (CompactSpace), Topology.QuasiSeparated
(QuasiSeparatedSpace), Algebra.Category.ModuleCat.Sheaf.Quasicoherent;
WeilConjectures Modules.Invertible; and the three recorded Sheaf modules Ample,
Coherent, PQFCohomology, plus RingedSpaceModuleCohomology. The conventions node
intentionally has no single declaration. No dependency record is unusable.

Edge cases checked before writing: the empty scheme is allowed; zero F and zero
xi are allowed; e = 0 is allowed and its map is the inverse right unitor into
F tensor the unit; p = 0 is correctly excluded (a nonzero global section on an
affine scheme is not generally killed); s = 0 gives the empty affine open and
positive powers give the zero map; s nowhere vanishing forces X itself affine,
so positive cohomology vanishes. There is no characteristic, field, separated,
Noetherian, coherent or finite-type restriction. For X = P^1, L = O(1), the
standard coordinate section and F = O(-2), the nonzero H^1 class is killed in
the first twist O(-1), consistent with the assertion.

Searches actually run via msearch.py with group H1 and this item:

- leansearch: `invertible sheaf section affine open kills positive cohomology classes`:
  unavailable, HTTP Internal Server Error (not a no-match result).
- leanfinder: `cohomology class killed by power of section of invertible sheaf with affine nonvanishing locus`:
  eight hits, including exists_of_res_zero_of_qcqs_of_top and affine structure
  sheaf section annihilation results; none is a positive-cohomology statement.
- loogle: `AlgebraicGeometry.Scheme.Modules.tensorPow`: unknown identifier, zero hits
  (this declaration belongs to the source project, not Mathlib).
- grep: `kills.*cohomology|cohomology.*kills|affine.*section` in AlgebraicGeometry:
  17 hits on affine section rings, ideals and morphisms, no matching theorem.
- Local rg on WeilConjectures and lean/Sheaf for
  `section-affine-open-kills-cohomology|kills.*cohomology|cohomology.*kills`:
  no declaration of this statement. Search for `01XR` finds only a citation in
  Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening, not a declaration.
- Local rg for tensor powers, sections and their maps found the existing
  tensorPowSection, homOfGlobalSection and mulTensorPowSection declarations;
  these were read and reused, not duplicated.
- `tools/lean_names_upstream.py show lem-sc-section-affine-open-kills-cohomology`
  and rg of dag/lean_names_upstream.json found no recorded declaration for this item.
- Local rg of Mathlib located the full definitions used above; local rg of the
  source and Sheaf modules found no existing declaration with the proposed name.

Validation: scompile.py compiled the 50-line module cleanly on the server in
2.5 seconds, exit code 0, without warnings. No statement dispute or correction.

## Second reading by H1

The node's objects and hypotheses match the Lean declaration as follows:

- `X` is `Scheme.{u}`, with `[CompactSpace X]` for quasi-compactness and
  `[QuasiSeparatedSpace X]` for quasi-separatedness; no field, characteristic,
  separatedness, Noetherian, or finite-type hypothesis is added.
- `L : X.Modules` with `[L.IsInvertible]` is the node's invertible
  `O_X`-module, and `s : Γ(L, ⊤)` is its global section.
- `U : X.Opens`, `hU : (U : Set X) = nonvanishingLocus L s`, and
  `hAffine : IsAffineOpen U` render the node's assertion that `X_s` is affine.
- `F : X.Modules` with `[F.IsQuasicoherent]` is an arbitrary
  quasi-coherent module; `p : ℕ` and `hp : 0 < p` render every positive degree;
  `xi : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F` is a class in
  the recorded module-valued `H^p(X,F)`.
- The conclusion `∃ e : ℕ` includes `e = 0`. The displayed map is
  `((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) e)`, namely
  `F ≅ F ⊗ O_X` followed by tensoring with `s^e`, and `.map ... xi = 0` is
  precisely the required vanishing in `H^p(X,F ⊗ L^{⊗e})`.

Edge cases were checked: empty schemes, zero modules and zero classes remain
allowed; `e = 0` is allowed; `p = 0` is excluded; `s = 0` gives the empty
principal open; and no characteristic or universe case is excluded.

I searched the source project, Mathlib, and the local Sheaf tree for the
statement and its alternate names (`01XR`, affine-section/cohomology-killing,
and tensor-power section maps). No existing statement was found. The existing
notions `nonvanishingLocus`, `IsInvertible`, `tensorPowSection`,
`homOfGlobalSection`, `moduleCohomology`, and `IsQuasicoherent` were read and
reused; no duplicate definition or dependency module was needed.

No mismatch was found, so no source, node, or Lean repair was made. The remote
`scompile.py` retry was attempted but the SSH server timed out during banner
exchange; the worker report records the earlier clean server compilation.
