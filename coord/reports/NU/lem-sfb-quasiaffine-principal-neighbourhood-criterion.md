## Worker report

The module states `AlgebraicGeometry.Scheme.quasiAffinePrincipalNeighbourhoodCriterion`,
with its sole proof `sorry`. No definition or statement correction is needed. Only the
item's `lean` record changes. The declaration docstring gives all five proof steps with
their DAG references.

Clause-by-clause correspondence:

- An arbitrary scheme is `{Y : Scheme.{u}}`, with explicit universe `u` and
  `set_option autoImplicit false`.
- The subset is `{E : Set Y}`; `(hE : IsCompact E)` means quasi-compactness in the
  subspace topology. Mathlib's IsCompact does not impose Hausdorffness.
- Condition (i) is `∃ U : Y.Opens, E ⊆ U ∧ U.toScheme.IsQuasiAffine`.
  `Y.Opens` carries the canonical open subscheme structure. `IsQuasiAffine`
  already includes `CompactSpace U.toScheme`, exactly the required quasi-compactness,
  so a redundant compactness conjunct is unnecessary. Its canonical morphism to
  `Spec Γ(U, ⊤)` is an open immersion. Conversely a quasi-compact open subscheme of
  any affine scheme satisfies this class, by `IsQuasiAffine.of_isImmersion`.
- The equivalence of (i) and (ii) is the displayed `↔`.
- Every point of E in (ii) is `∀ e : E`; `∃ V : Y.Opens, E ⊆ V` requires a
  neighbourhood of the whole subset, separately for each e.
- `QuasiSeparatedSpace V.toScheme` is precisely quasi-separatedness of V, equivalent
  to compact intersections of affine opens (`quasiSeparatedSpace_iff_forall_affineOpens`).
  There is no quasi-separatedness assumption on Y.
- `∃ g : Γ(Y, V)` is a section on V of the restricted structure sheaf, canonically
  Γ(V, O_V). `Y.basicOpen g` is the corresponding open in Y contained in V;
  `Scheme.mem_basicOpen` identifies membership with invertibility of the germ.
  Thus `(Y.basicOpen g).toScheme.IsQuasiAffine` is precisely the requested
  quasi-affineness of V_g, and `(e : Y) ∈ Y.basicOpen g` puts e in it.

Statement dependencies read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; read full signatures and docstrings in Scheme.lean.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; opens use `Scheme.Opens.toScheme`, the canonical
  restriction of the locally ringed space. Its abbreviation is an open immersion of
  underlying locally ringed spaces.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; read signatures/docstrings.
  Mathlib `Scheme.IsQuasiAffine` uses this Spec, not a second affine construction.

The public Mathlib imports expose these dependencies, quasi-affineness and
quasi-separatedness. Proof-only imports are `Mathlib.AlgebraicGeometry.ResidueField`
and `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`; together with the public
imports they supply the recorded Mathlib leaves for the finite affine cover, affine
basis, affine qcqs, principal-open affineness/localization, and the canonical affine
embedding. The source module also contains the exact fixed-scheme criterion
`Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen`, used by the final proof
step. The corresponding proof-dependency node currently has no Lean record, but no
new statement is needed since the exact upstream theorem exists. No dependency node
was changed.

Edge cases checked before writing: E = ∅ has the empty open (Spec of the zero ring)
as a witness; the universal condition is vacuous. If Y is empty this is the same
case. E may be nonclosed, nonopen, infinite, or non-Hausdorff. No nonemptiness,
finite-set, global compactness or global quasi-separatedness assumption was added.
Neither V nor Y is required quasi-compact in (ii); only the principal open is
quasi-affine and hence quasi-compact. For a nonempty E the finite-cover argument
has a nonempty set of indices, so it can use a chosen V_i for quasi-separatedness.
Unit sections witness the forward implication, including E = Y when Y is
quasi-affine. All schemes and opens stay in universe u without a restriction on u.

Source check: opened the primary Numdam scan
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf , printed p. 14,
Lemma 3.7, equivalence (i)--(ii), and its finite-cover proof; it agrees with the
node. In particular it assumes quasi-separatedness of the chosen V, not of Y.
The final fixed-scheme input is the preceding Lemma 3.6. No STATEMENT-DISPUTED flag
and no node fault.

Searches (the exact machine records are in searches.jsonl in the sandbox):

- msearch.py grep: `(IsQuasiAffine|quasi.affine).*(basicOpen|neigh)|(basicOpen|neigh).*(IsQuasiAffine|quasi.affine)` in `AlgebraicGeometry`. 6 hits: Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean.
- msearch.py loogle: `"IsQuasiAffine", "basicOpen"`. 2 hits: AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen, AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen.
- msearch.py leanfinder: `A quasi-compact subset of a scheme has a quasi-affine open neighbourhood if every point lies in a quasi-affine principal open of a function on a quasi-separated neighbourhood of the whole subset`. 8 hits: AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen, AlgebraicGeometry.isLocalization_basicOpen_of_qcqs, AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated, AlgebraicGeometry.isCompact_basicOpen, AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact, AlgebraicGeometry.quasiSeparatedSpace_iff_affine, AlgebraicGeometry.compact_open_induction_on, AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens.
- msearch.py leansearch: `Quasi-compact subset quasi-affine open neighbourhood equivalent principal open neighbourhood on quasi-separated opens`. 8 hits: AlgebraicGeometry.quasiSeparatedSpace_iff_affine, AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens, AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens, AlgebraicGeometry.Scheme.IsQuasiAffine.mk, QuasiSeparatedSpace, AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens, IsQuasiSeparated, AlgebraicGeometry.IsAffineOpen.isQuasiSeparated.

- `rg -n` on lean/WeilConjectures and lean/Sheaf for
  `(IsQuasiAffine|quasi.affine).*(basicOpen|neigh)|(basicOpen|neigh).*(IsQuasiAffine|quasi.affine)`:
  found the fixed-qcqs-scheme theorem in WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean
  at line 142, but no varying-neighbourhood equivalence for a compact subset.
- `rg -n` for the item id on lean/WeilConjectures: no match.
- Read Mathlib/AlgebraicGeometry/QuasiAffine.lean in full: its affine-basic-open
  criterion has one fixed compact scheme and does not state this subset criterion.

These searches found all needed notions, but no exact statement to reuse.

Validation: scompile.py compiles this module on the server; the delivery dry run
and actual delivery are performed through deliver2.py. Expected sorry warning only.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
