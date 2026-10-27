## Worker report

The module `Sheaf.AlgebraicGeometry.ExistsAmpleOfReductionCharP` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_reduction_charP`, with one
`sorry` proof and no new definitions. The item is unchanged outside `lean`.
The source read is `literature/stacks-project/divisors.tex`,
`proposition-push-down-ample` case (3), Tag 0BD4, together with
`lemma-Frobenius-gives-norm-for-reduction` (0BDZ) and `lemma-norm-ample` (0BD0).
The theorem docstring records all five DAG proof steps.

Hypothesis and conclusion correspondence:

- A prime number is `(p : ℕ) (hp : p.Prime)`.
- The scheme is `(X : Scheme.{u})`, with arbitrary explicitly bound universe `u`.
- The finite affine cover by spectra of Noetherian rings is `[IsNoetherian X]`.
  Mathlib `AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover`
  (Noetherian.lean:305) identifies this with precisely the stated cover condition;
  `isNoetherian_iff_of_finite_iSup_eq_top` (line 284) gives the affine-open version.
- The condition `p O_X = 0` in every local ring is
  `hchar : ∀ x : X, (p : X.presheaf.stalk x) = 0`. Natural-number casting is
  multiplication of the unit by `p`. This uses annihilation, without imposing
  an exact characteristic on empty-section rings or additional algebra data.
- The reduction is exactly `X.nilradical.subscheme`, the dependency's recorded
  nilradical closed subscheme, with no abstract replacement scheme.
- Existence of an absolutely ample invertible module on the reduction is
  `hred : ∃ (M : X.nilradical.subscheme.Modules) (_ : M.IsInvertible),
  IsAmple X.nilradical.subscheme M`. The dependent existential makes the
  invertibility proof available to the existing ampleness predicate.
- The conclusion is `∃ (L : X.Modules) (_ : L.IsInvertible), IsAmple X L`.
  Its witness is independent of the module witnessing `hred`; no pullback
  identification or lift of that module is asserted.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg`; the scheme-cover encoding uses
  `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` and `subschemeι`;
  `Scheme.nilradical` is defined in IdealSheaf.Basic as the radical of zero.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, locally isomorphic to the unit.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, exactly quasi-compactness plus affine
  nonvanishing neighbourhoods of positive-power sections; `nonvanishingLocus`.

Plain proof imports cover the stated proof dependencies:
`Mathlib.AlgebraicGeometry.Morphisms.Finite` (closed immersions are finite),
`Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections`,
`Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`, and
`WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen`.
`lem-sfb-reduction-frobenius-sheaf-norm` has no Lean record or Mathlib match in
this checkout, so there is no module to import for that proof-only prerequisite.
It is named in the proof docstring; the theorem signature does not need it.

Edge cases checked before writing: the empty scheme is allowed (the local-ring
condition is vacuous there, and ampleness has no pointwise obligation);
a reduced scheme is allowed without any nontrivial thickening condition;
nonreduced characteristic-p schemes such as Spec(F_p[ε]/ε²) meet the intended
hypotheses; no separatedness, finite-type-over-a-field, nonemptiness, fixed
nilpotence exponent, or specified line-bundle lift is assumed. Prime `2` is
included; `0` and `1` are excluded exactly by primality. No auxiliary indexing
universe or bound on dimension is introduced. The theorem has no tensor-power
binder that would accidentally include exponent zero in the ampleness test.

Searches actually run with `batch2/msearch.py` (group NE, this item):

- LeanFinder: `A Noetherian scheme in positive prime characteristic admits an ample
  invertible sheaf if its reduction does`: eight results about Noetherian/reduced
  schemes and stalks; none asserts this conclusion.
- LeanSearch: `Existence of an ample invertible module on a Noetherian scheme in
  positive characteristic descends from the reduction`: eight general morphism
  descent results; none states this theorem.
- Loogle: `IsAmple, Scheme.nilradical`: zero hits, unknown identifier `IsAmple`.
- Mathlib grep: `ample.*reduc|reduc.*ample|Frobenius.*norm` in AlgebraicGeometry:
  one irrelevant comment in IdealSheaf/IrreducibleComponent.lean.
- Local `rg` across both `lean/WeilConjectures` and `lean/Sheaf` for ample/reduction
  and characteristic/ampleness combinations, followed by a targeted search for
  `exists.*ample.*(reduc|nilradical)|exists.*(reduc|nilradical).*ample|exists_isAmple_of`.
  Read `Modules/AmpleReduced.lean`: its
  `AlgebraicGeometry.exists_isAffineOpen_compl_support_zeroLocus_of_nilradical`
  handles finitely many sections of one invertible module, using
  `SheafOfModules.IsInvertible` and zero-locus ideals. It does not have the
  item's existential absolute `IsAmple` statement, and is not recorded as an
  exact existing match. The other results concern dimension-one schemes or
  finite morphisms with normal target, not this item.
- Local search for the item id in `lean/WeilConjectures` returned no declaration.
  Search for the proposed full declaration's final component across both
  project trees and `dag/lean_names_upstream.json` returned no clash.

No new nodes, dependency interface repairs, statement correction, or disputed
statement is needed. No proof has been supplied at stage 2.

Validation: `scompile.py NE lem-sfb-ample-existence-characteristic-p-reduction`
compiled this module in both sandbox and library mode cleanly. The delivery dry
run passed server preflight and per-file compilation (dry-run commit
`e04f02fbf61`). A final source comparison finds only the item's `lean` field
changed, no Lean line exceeds 100 characters, and the one postponed theorem
has the matching DAG id and full five-step proof docstring. No independent
second reader was started, as the dispatcher expressly forbids other agents;
the maintainer's independent review remains the review of this delivery.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
