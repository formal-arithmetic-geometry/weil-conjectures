## Worker report

This delivery states `AlgebraicGeometry.PrimeToEllAlteration.alteration_cover_standard_refinement`
in `Sheaf.AlgebraicGeometry.AlterationCoverStandardRefinement`. The only postponed proof is
this theorem, whose docstring includes all five steps of the DAG proof and the cited node IDs.
No new definitions, statement corrections, or semantic dependency repairs are introduced.
The exact recorded source module for `def-per-prime-to-ell-alteration-topology` is included
as a dependency module because the published live build had no `.olean` for it; its
declarations and interfaces are unchanged.
The source was read in the local ILO PDF, Exposé II 2.2.4 and 3.2.3 (printed pp. 27,
30--31). The latter gives the proper birational / completely decomposed étale / finite
flat standard form; the node's explicit integral, finite, constant-rank formulation is
rendered without changing its statement.

Hypotheses and objects, clause by clause:

- Integral Noetherian base: `(S : Scheme.{u}) [IsIntegral S] [IsNoetherian S]`.
  Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the stipulated
  finite affine Noetherian cover. `IsIntegral` includes nonemptiness.
- Quasi-excellence of every affine coordinate ring:
  `hS : ∀ V : S.affineOpens, IsQuasiExcellent Γ(S, V.1)`.
- Prime invertible on the base: `(ell : ℕ) [Fact ell.Prime]` and
  `hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)`.
- Arbitrary finite index set and objects of alt/S: `{B : Type w} [Finite B]`
  and `T : B → Alt S`. The supplied structure maps are precisely `(T b).obj.hom`.
  No integrality or Noetherianity is imposed separately on the input sources.
- Covering: `hcover` uses the recorded `IsCoveringFamily ell T q`. Its existential
  `base` is required to have `base.obj = Over.mk (𝟙 S)`, so this is a family covering
  S itself, not a different target. The arrows in the full subcategory are S-arrows;
  their underlying maps to S are therefore the given structure maps. This packages
  identity-object membership inside the covering hypothesis rather than adding a new
  hypothesis, theorem, or private construction of alt/S.

Conclusions, clause by clause:

- `∃ (S' : Scheme.{u}) (p : S' ⟶ S)` with `IsIntegral S'`, `IsNoetherian S'`
  and `IsProper p` gives exactly the integral Noetherian proper modification.
- `∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (p ∣_ U)` means p is an isomorphism
  over a dense open of S. The restriction has the full inverse-image source.
- `LocallyOfFiniteType p ∧ QuasiCompact p` states finite type of S' over S.
- `(n : ℕ) (E W : Fin n → Scheme.{u})` gives the finite family, and
  `∀ i, IsIntegral (E i) ∧ IsNoetherian (E i) ∧ IsIntegral (W i) ∧ IsNoetherian (W i)`
  retains every integrality and Noetherianity clause.
- `e : ∀ i, E i ⟶ S'` with `IsSeparated`, `Etale`, `LocallyOfFiniteType`, and
  `QuasiCompact` renders separated étale finite-type e_i.
- `a : ∀ i, W i ⟶ E i`, `r : Fin n → ℕ` with
  `(a i).IsFiniteLocallyFreeOfDegree (r i) ∧ Surjective (a i) ∧
  0 < r i ∧ Nat.Coprime (r i) ell` states finite locally free surjections of constant
  positive ranks prime to ell. The recorded upstream degree definition measures
  `fiberDegree`, the dimension of global sections of the scheme fibre.
- The pairs of `LocallyOfFiniteType` and `QuasiCompact` on `e i ≫ p` and
  `a i ≫ e i ≫ p` state finite type of E_i and W_i over S.
- `∀ s' : S', ∃ (i : Fin n) (z : E i), e i z = s' ∧
  IsIso ((e i).residueFieldMap z)` is complete decomposition, using the actual
  induced residue-field map. This spells out the node's defining clause. The
  recorded `IsCompletelyDecomposedEtaleFamily` only accepts families in alt/S;
  no extra alt/S object condition is imposed on the output schemes.
- `b : Fin n → B` and `h : ∀ i, W i ⟶ (T (b i)).obj.left` choose b(i), h_i;
  `h i ≫ (T (b i)).obj.hom = a i ≫ e i ≫ p` is q_b h_i = p e_i a_i.
  This equality is precisely the assertion that h_i is an S-morphism.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, as used by the
  finite-affine characterization of `AlgebraicGeometry.IsNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (from the recorded
  `def-exc-excellent-ring` module).
- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt` and `IsCoveringFamily`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; separatedness is
  `IsSeparated` from `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree` and its parent `IsFiniteLocallyFree`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.

The proof imports include the recorded modules for `lem-fin-etale-normal-components`,
`lem-weil-pbc-reduced-induced-closed-subscheme` (the side declaration, avoiding its
upstream duplicate), and `lem-per-quasi-excellent-finite-type-stability`.
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty` supplies the recorded étale
base-change leaf. The other Mathlib proof leaves are in the public import closure.
The proper-normal-form, integral-chart-flatification and finite-flat-exchange nodes
have no recorded Lean modules yet, so their imports cannot be added in this delivery;
their IDs and full roles remain in the theorem docstring.

Edge cases checked: empty S is excluded exactly by integrality. Empty B is not given
an artificial Nonempty assumption; it cannot satisfy the covering hypothesis over the
nonempty base. Empty output indexing (`n = 0`) is syntactically allowed but is ruled
out by complete decomposition and nonempty S'. No empty E_i or W_i can satisfy the
integrality conclusions. Zero ranks are explicitly excluded; rank 1 and ell = 2 are
included. All primes, including residue characteristic zero, are allowed subject only
to stalkwise invertibility. Input B lives in an independent universe w, so all finite
index sets are included; the finite output is enumerated by Fin n. No normality,
separatedness of S, regularity, characteristic, dimension, or coefficient assumption
is added. No disputed statement or node fault was found.

Searches made (2026-10-19):

- `msearch.py ... leanfinder`: "A prime to ell alteration cover admits a refinement
  by a proper dense open modification a completely decomposed etale family and finite
  locally free surjections of positive coprime rank". Eight ordinary cover / affine
  transition-limit hits, including `Scheme.Cover`; none states this refinement.
- `msearch.py ... loogle`: `IsProper, Etale, Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
  Zero hits; the service reported unknown identifier IsProper (unqualified query).
- `msearch.py ... grep`: `alteration|completely.decomposed|standard.refinement`,
  restricted to Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch`: "An alteration cover has standard refinement by proper
  modification completely decomposed etale and finite flat prime to ell maps".
  Eight ordinary étale site / cover / standard étale algebra hits; no match.
- `rg` in upstream WeilConjectures, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node ID, alteration / standard-refinement
  names and the family predicates. Only the owning topology module and the downstream
  uniformization theorem cite the relevant notion; there is no existing theorem.

Validation: the source and node record were checked for 100-character line width,
explicit universes/binders, a signature copied verbatim, and a single `sorry` proof.
The initial prescribed `scompile.py` call exited 75 before elaboration, reporting a
missing published live `PrimeToEllAlterationTopology.olean`. The wrapper's `--source`
mode confirms the recorded source exists and has the interface used here. Further
validation results are recorded below.

## Dependency modules

`def-per-prime-to-ell-alteration-topology`: the recorded module `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology` was present in the project source but absent from the published live `.olean`, causing the initial compile failure. The included module is an exact copy of that recorded source and the copied node keeps its original `lean` record; it supplies the existing `Alt` and `IsCoveringFamily` declarations without changing their statements.

## Second reading by Q47

Author self-check, not an independent agent review: the dispatch brief forbids starting
other agents and assigns independent review to the maintainer. With the node and module
open, I checked the hypotheses and every conclusion against the mapping above. In
particular, the target of the covering family is forced to be the identity object,
not an arbitrary object of alt/S; the refinement maps land in the given T_b; all three
output schemes have their Noetherian and finite-type assertions; and complete
decomposition uses IsIso on the induced map, not merely an abstract field isomorphism.
The degree predicate was read in the upstream source: it extends finite / flat /
locally finite presentation and asserts fibre dimension at every target point.
No strengthening or dropped clause was found. The independent maintainer review is
still required by the brief.

Final wrapper results: a second `scompile.py` invocation again exited 75 with the
same `INFRASTRUCTURE RETRY (stale live olean)` diagnostic. Then the required
`deliver2.py Q47 lem-per-alteration-cover-standard-refinement --no-push` exited 1:
`COMPILE FAILED on the server, nothing pushed`, followed by the same missing
`Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology.olean` path. No delivery push
was attempted, and the statement has not been elaborated. Resolving this requires
the published live dependency artifact; its source is present and was confirmed by
`scompile.py --source`. No launcher tool, read-only source, or live build was modified.

## Saved-packet retry by Q47

On 2026-10-18 UTC, retained the saved module and node unchanged and began with the
prescribed `deliver2.py Q47 lem-per-alteration-cover-standard-refinement --no-push`.
It again exited 1 before elaboration, reporting `COMPILE FAILED on the server,
nothing pushed` and `INFRASTRUCTURE RETRY (stale live olean)` for the missing
published `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology.olean`.
A fresh prescribed `scompile.py` invocation on the saved module independently
exited 75 with the same missing artifact. `scompile.py --source
Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology` succeeded, and its current
`Alt` and `IsCoveringFamily` signatures agree with the interfaces used in the
saved statement. This is an unavailable published build artifact, not a missing
notion or an unusable dependency declaration. No statement/module repair addresses
it within the worker's read-only live-library scope. No push was attempted.
