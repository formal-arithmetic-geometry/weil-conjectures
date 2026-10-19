## Worker report

The delivery states `AlgebraicGeometry.Etale.gabber_open_immersion_sheaf_finiteness`
in `Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness`. Its only theorem
has proof `sorry`; no definition or proof is supplied. The retained earlier draft
compiled cleanly through scompile.py before the documentation/import completion.
The node's natural-language statement is unchanged.

Hypotheses and clauses, in the order of the node:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The finite field B of
  characteristic ell is `(B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]`.
- Schemes U and T are `{U T : Scheme.{u}}`. Noetherian T is `[IsNoetherian T]`,
  the Mathlib class combining locally Noetherian and quasi-compact. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with the node's
  finite affine cover by Noetherian coordinate rings.
- Quasi-excellence of every affine coordinate ring is
  `(hT : ∀ V : T.affineOpens, IsQuasiExcellent Γ(T, V.1))`.
- Invertibility of ell in every local ring is
  `(hℓ : ∀ t : T, IsUnit (ell : T.presheaf.stalk t))`.
- The open immersion is `(j : U ⟶ T) [IsOpenImmersion j]`. No density,
  separatedness of T, irreducibility, global finite-dimensionality or properness
  is imposed.
- A module sheaf over the constant B sheaf on the ordinary small etale site is
  `(M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B))`.
  Constructibility is `(hM : Scheme.IsConstructibleEtaleModuleSheaf M)`, the
  recorded finite stratification with finite locally constant module values.
- A sheaf in degree zero is `DerivedCategory.Plus.singleFunctor ... 0`.
  Applying `rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) j` and then
  `DerivedCategory.Plus.homologyFunctor ... q` is precisely R^q j_* M in
  `def-weil-pbc-direct-image`.
- Constructibility of every higher direct image is the first conjunct,
  `∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (...)`. The direct-image
  definition indexes q by integers; the negative terms vanish for degree-zero
  input, so this does not impose an extra nontrivial condition.
- The second conjunct is `∃ N : ℕ, ∀ q : ℤ, (N : ℤ) < q → IsZero (...)`.
  The natural-number binder means N_M ≥ 0. `IsZero` is used on a sheaf in an
  abelian category, not on a bare Type. It is exactly zero as a module sheaf.
  N is inside the statement with M already bound, so it may depend on M.
  No assertion for nonconstructible sheaves or uniform bound is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; through
  `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsNoetherian` and
  `isNoetherian_iff_of_finite_affine_openCover`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, with its actual
  Noetherian, G-ring and open-regular-locus clauses. The node's primary
  declaration `IsExcellent` also exposes this quasi-excellent predicate.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` reads
  constructibility of its homology through the publicly imported
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. We use exactly
  this predicate for the degree-zero input and each higher direct image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, objectwise sections over base change.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, literally the bounded
  below right derived functor of that `lowerStar`.

The module imports all currently recorded proof-dependency modules, with
non-public imports. The as-yet unstated proof nodes for prime-to-ell standard
uniformization, birational bad-locus comparison, regular-boundary constant
image, finite-open constant generation and the thick Verdier quotient kernel
have no module to import. They remain explicit in the theorem's proof
docstring, which transcribes every step of the DAG proof. The Mathlib leaves
for finite-presentation over Noetherian bases, truncation triangles and finite
Krull dimension of Noetherian local rings are imported at their recorded files.

Edge cases checked before finalizing the statement: empty T (and hence empty
U), empty U, M = 0, and the identity open immersion all permit N = 0. The
statement allows each of these without additional binders. For q < 0,
right-derived image of a degree-zero sheaf is zero. There is no assumption of
finite Krull dimension for the whole Noetherian scheme: the proof uses finite
heights of individual local rings and a finite open subcover. Universe u is
explicit; B and modules live in u+1 as required by the existing ordinary small
etale coefficient API, without equating different site universes.

Sources checked: the local ILO PDF, Expose XIII Theorem 1.1.1, its equivalent
bounded-constructible version 1.1.2, Lemma 3.1.3 and Sections 3.2--3.7, including
3.7.2 and 3.7.4. The D-plus typo in Lemma 3.1.3 is already documented in the
DAG proof; the stated theorem here does not inherit it. The theorem gives
constructibility and eventual vanishing, without a bound uniform in the sheaf.
Finite-field coefficients specialize the finite torsion coefficient form.

Searches (retained actual results in searches.jsonl, and fresh source checks):

- Loogle, `"IsOpenImmersion", "constructible"`: no hits.
- LeanFinder, "Higher direct images of a constructible finite field etale module
  sheaf under an open immersion into a Noetherian quasi excellent scheme are
  constructible and vanish in sufficiently high degrees": eight unrelated
  scheme-module pushforward and constructible-image hits, no exact theorem.
- LeanSearch, "Higher direct images of constructible torsion etale sheaves under
  open immersions are constructible on quasi excellent schemes": eight hits on
  scheme restriction/open immersions, no etale finiteness theorem.
- Mathlib grep through msearch.py, `(constructib|[Ee]tale).*(higherDirectImage|rightDerived)|[Qq]uasi.?[Ee]xcellent`
  in AlgebraicGeometry: no hits. A second query
  `Gabber|quasi.?excellent|constructible.*direct` likewise found no hits.
- Direct rg in WeilConjectures, Mathlib/AlgebraicGeometry and lean/Sheaf for
  `gabber_open_immersion_sheaf_finiteness`, `Gabber.*finiteness` and
  quasi-excellence: no existing declaration of this theorem. Upstream
  `Etale/Derived/Stability.lean` only mentions Gabber finiteness as a condition
  for preservation, rather than proving this assertion. Project
  `QuasiExcellentEtaleDirectImageFiniteness.lean` is a more general theorem
  whose proof explicitly uses this item; it cannot replace this prerequisite.
  `OpenClosedConstructibleTest.lean` likewise cites this item in its proof.
- The retained draft's declaration name has no collision in Mathlib, upstream
  WeilConjectures or the published project modules.

No new node, dependency-interface repair, statement correction, disputed
statement or mathematical node fault was needed. Final wrapper compilation
and preflight results are recorded below after they run.

## Second reading by Q35

This resumed worker read the retained earlier draft independently of its
original author, with the current node and the actual dependency sources open.
The finite-field/characteristic hypotheses, Noetherian and affine-local
quasi-excellent conditions, local invertibility and arbitrary open immersion
all match. The input is the recorded constructible module-sheaf predicate;
R^q is the recorded homology of the right-derived ordinary direct image of
M[0]. The two conclusions are constructibility in each degree and a
nonnegative bound depending on M. The integer degree convention agrees with
the direct-image node and causes no negative-degree strengthening because
these terms vanish. No mathematical signature mismatch was found. Repairs
were documentation and delivery completeness: a source/blueprint declaration
docstring, the complete eleven-step proof, proof-dependency imports, the node's
Lean record and this report. The maintainer's independent delivery review is
still to follow; no separate sub-agent was started.

## Final verification

The resumed packet passed `deliver2.py Q35
lem-per-gabber-open-immersion-sheaf-finiteness --no-push`: preflight and the
single-file compilation both succeeded (dry-run commit `2e136349d4`). A final
reading against the current node and the recorded dependency source signatures
confirmed the hypothesis and conclusion correspondence above. The node copy
changes only `lean`; its signature matches the file. The Lean module was retained
without edits. No repair note exists for this item.
