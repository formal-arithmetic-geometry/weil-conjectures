## Worker report

Bind `sk-d-real-setup` to the existing definition bundle in
`Sheaf.Paper.RealSheavesSetup`, main declaration `RealSheaves.Setup`.
The DAG attachment changes only the item's `lean` field; no mathematical
statement changes. The definition performance repair below is additionally
required by the resumption brief. The sketch `_section.md` and
expanded `d-real-setup.md` in blueprint main-20261015 have identical mathematical
text; each node records the other in `blueprint.same_as`. The expanded twin already
owns this module. I opened both sources and the complete existing definitions,
and confirmed the module's current server source with `scompile.py --source`.
The full associated declaration list is recorded so the bundle, rather than just
the first paragraph's structure, is attached to this node.

Clause-by-clause correspondence (names below are in namespace `RealSheaves`):

| Source hypothesis or convention | Existing Lean rendering |
| --- | --- |
| Prime power `q = p^a` | `Setup.p : ℕ`, `p_prime : p.Prime`, `a : ℕ`, `a_pos : 1 ≤ a`, and `Setup.q D := D.p ^ D.a` |
| Fixed finite field with `q` elements | `k₀ : Type u`, `[Field k₀]`, `[Fintype k₀]`, `card_eq : Fintype.card k₀ = p ^ a` |
| Chosen algebraic closure `k` of that field | `k : Type u`, `[Field k]`, `[Algebra k₀ k]`, `[IsAlgClosure k₀ k]` |
| Prime `ℓ ≠ p` | `l : ℕ`, `[l_prime : Fact l.Prime]`, `l_ne_p : l ≠ p` |
| Algebraic closure of the ℓ-adic numbers | `Qbar : Type v`, `[Field Qbar]`, `[Algebra ℚ_[l] Qbar]`, `[IsAlgClosure ℚ_[l] Qbar]` |
| Fixed field embedding into `ℂ` | `iota : Qbar →+* ℂ`; a unital homomorphism from a field is injective; no continuity or surjectivity requirement |
| Scheme over the fixed finite field | `C₀ : Scheme.{u}` and `[C₀.Over (Spec (.of D.k₀))]`; the structure map is `C₀ ↘ Spec (.of D.k₀)` |
| Curve is nonempty | First conjunct `Nonempty C₀` of `Setup.IsCurve` |
| Separated | Second conjunct `IsSeparated (C₀ ↘ Spec (.of D.k₀))` |
| Smooth | Third conjunct `Smooth (C₀ ↘ Spec (.of D.k₀))` |
| Finite type | Fourth and fifth conjuncts `LocallyOfFiniteType` and `QuasiCompact` on that structure map |
| Pure dimension one | Sixth conjunct `C₀.IsPureDimension 1` |
| Base change `C = C₀ ×_{k₀} k` | `Setup.geometricCurve`, the pullback of the structure map along `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))` |
| Connected geometric base change | Final conjunct `ConnectedSpace (D.geometricCurve C₀)` |
| Closed point `x` | Argument `x : closedPoints C₀`, the subtype of points whose singleton is closed |
| `e_x = [κ(x) : F_q]` | `Setup.closedPointDegree`, defined as `(C₀ ↘ Spec (.of D.k₀)).residueDegree x.1`; the residue field of the image in `Spec k₀` identifies canonically with `k₀` |
| `q_x = q^(e_x)` | `Setup.closedPointCardinality D C₀ x := D.q ^ D.closedPointDegree C₀ x` |
| Geometric Frobenius, inverse of `t ↦ t^q` | `Setup.frobenius`, the existing `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`, defined as the inverse of Mathlib's arithmetic Frobenius |
| Local version `F_x` | `Setup.localFrobenius D C₀ x Ω` on any algebraic closure `Ω` of `C₀.residueField x.1`; it is the same geometric Frobenius construction over that finite residue field |
| Nonempty open subscheme | `Setup.IsAffineOpen D j` requires `Nonempty U₀`, `IsOpenImmersion j`, and the equation making `j` a morphism over `k₀` |
| Spectrum of a finitely generated `F_q`-algebra | Its remaining existential supplies a commutative `k₀`-algebra `A`, `Algebra.FiniteType D.k₀ A`, and `e : U₀ ≅ Spec (.of A)` compatible with the structure maps |

The prime `p` in the prime-power notation is the characteristic prime, as specified
by dependency `def-weil-finite-field-q-elements`; this is the same interpretation
already made explicit in the expanded twin and its review. The canonical field
need not literally be `GaloisField p a`: a field with the stipulated cardinality
is exactly the dependency's notion. Similarly, `IsAlgClosure` allows the chosen
closures rather than making a second algebraic-closure construction.

The local Frobenius's `LocallyOfFiniteType` instance is supplied by `IsCurve`'s
fourth conjunct. Its residue-field finiteness is obtained internally from
`Scheme.Hom.finite_residueField_of_isClosed` (`WeilConjectures.PointCount`), not
added as an extra mathematical assumption. A finite field extension has
cardinality `q` to its degree, so its inverse cardinality-power Frobenius is the
stated inverse `q_x`-power Frobenius. No path, fundamental-group lift, or absolute
scheme Frobenius is substituted for the field automorphism.

The affine-open compatibility equations merely record the structure of an open
subscheme over `k₀`. In the standing finite-type curve context, an affine open's
induced coordinate algebra is finitely generated over `k₀`. They do not require
the curve to be affine, the open to be proper, or a chosen presentation of `A`.

Dependencies read and reused (all 17 statement dependencies were opened):

- `def-weil-finite-field-q-elements`: `GaloisField` in
  `Mathlib.FieldTheory.Finite.GaloisField`, with cardinality represented by
  `Setup.card_eq` for the fixed arbitrary model.
- `def-weil-algebraic-closure`: `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `IsAlgClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`.
- `def-weil-l-adic-numbers`: `Padic` (`ℚ_[l]`) in
  `Mathlib.NumberTheory.Padics.PadicNumbers`.
- `def-pc-scheme`, `def-weil-affine-spectrum`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over` in
  `Mathlib.AlgebraicGeometry.Over`.
- `def-weil-proper-morphism`: its separated clause,
  `AlgebraicGeometry.IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, publicly provided by the
  recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper` import. Properness itself
  is not imposed.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, used as their conjunction.
- `def-weil-pure-dimension`: `AlgebraicGeometry.Scheme.IsPureDimension` in
  `Sheaf.AlgebraicGeometry.PureDimension`, quantifying over irreducible components
  with their subspace Krull dimension.
- `def-pc-base-change`: the recorded `Limits.pullback` convention and projections
  in `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; the node's
  `moduleBaseChange` declaration concerns modules and is not used as a substitute
  for scheme base change.
- `def-weil-connected-scheme`: `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, which includes nonemptiness.
- `def-weil-closed-points`: `closedPoints` in `Mathlib.Topology.JacobsonSpace`.
- `def-weil-residue-field`, `def-weil-closed-point-degree`:
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `Scheme.Hom.residueDegree` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-frobenius-substitution`:
  `FiniteField.frobeniusAlgEquivOfAlgebraic` in
  `Mathlib.FieldTheory.Finite.Basic`; its inverse is already named
  `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` in
  `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.

Edge cases checked by reading the definitions:

- `a = 0` is excluded by `a_pos`; `a = 1` and characteristic two are allowed.
  `l = p` is excluded, with no constraint beyond primality on the other primes.
- `iota` is a plain field embedding, so no topological restriction is introduced.
- The empty scheme is excluded even though `IsPureDimension 1` alone admits it.
  `Spec F_q` fails pure dimension one. A disjoint union of two affine lines fails
  connectedness after base change; an affine line over a nontrivial finite
  extension viewed over `F_q` also fails geometric connectedness. The affine line
  and projective line over `F_q` satisfy the intended curve convention, so neither
  properness nor affineness of the curve is accidentally required.
- Pure dimension one is tested component by component, not merely by an upper
  dimension bound. Smoothness excludes nonreduced curves.
- Closed points of degree greater than one use the residue-field cardinality,
  not `q`; degree-one points specialize to `q_x = q`.
- An empty affine open is excluded. Nonempty proper affine opens are allowed;
  the whole affine curve is allowed. The zero ring's empty spectrum cannot
  witness a nonempty open.
- The existing bundle has explicit universe variables `u v w`, independent
  coefficient universe `v`, and arbitrary local closure universe `w`. No new
  universe equality or size assumption is introduced by this attachment.

Searches actually run for this item:

- `msearch.py leanfinder` query: `finite field algebraic closure geometric
  Frobenius smooth separated geometrically connected curve ell-adic embedding`.
  Eight hits: arithmetic Frobenius and its apply/inverse declarations, finite
  extension embedding, perfect-ring Frobenius, Witt-vector isocrystal,
  `arithFrobAt`, and `FunctionField`. No combined setup declaration in Mathlib.
- `msearch.py leansearch` with the same query: eight hits including
  `FiniteField.Extension.frob`, `Field.Emb`, and arithmetic Frobenius declarations.
  These do not supply the combined setup.
- `msearch.py loogle` query: `FiniteField.frobeniusAlgEquivOfAlgebraic,
  AlgebraicGeometry.Smooth, AlgebraicGeometry.Scheme.IsPureDimension`.
  Zero hits; reported unknown identifier
  `AlgebraicGeometry.Scheme.IsPureDimension` (a project declaration).
- `msearch.py grep` query:
  `frobeniusAlgEquivOfAlgebraic|IsPureDimension|structure Setup`, subdirectory
  `FieldTheory`: fourteen Frobenius hits in Mathlib's finite-field modules.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `d-real-setup|sk-d-real-setup` located the
  exact combined definitions in `lean/Sheaf/Paper/RealSheavesSetup.lean`.
  Its source lines 45–136 contain all nine recorded declarations. Searching
  Frobenius, pure dimension, closed points and residue degree also confirmed
  the underlying shared interfaces. The twin `d-real-setup` node's `lean`
  record identifies the same module and declarations.

No statement dispute or node fault was found. This is the prescribed
`existing: true` case: the signature `structure Setup` is copied verbatim up to
`where`, and no duplicate statement module is introduced. The delivery wrapper compiles an import and
`#check` probe for every recorded declaration against the live published build.

Validation history: the earlier worker's three dry runs failed in the compiler
overlay on a missing object file for
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic`, although a direct
`scompile.py` import probe succeeded. On resumption, the first two dry runs
instead failed while loading `FinitePresentationSupportReductionFiltration`:
`WeilConjectures.Topology.PresheafModuleStalkFunctor.olean` was missing in both
the overlay compile and its server confirmation. A sandbox probe importing
`WeilConjectures.Topology.PresheafModuleStalkFunctor` and checking
`PresheafOfModules.stalkObj` then compiled cleanly through `scompile.py`.
The following dry run passed that failure and advanced through the dependency
closure. All probes use the prescribed wrapper, and no library or launcher
script has been edited.

Validation result on resumption: four dry runs were attempted. The first two
failed on the missing stalk-functor artifact described above. The third advanced
through that failure; its overlay timed out on
`WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardAcyclic`, but server
confirmation compiled it in 56.4 seconds and then timed out on
`WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChange`. The fourth dry run
compiled `PushforwardAcyclic` in 52.7 seconds in the overlay, then both its overlay
and server confirmation again timed out on `FlatBaseChange` at 60 seconds.

To isolate the remaining failure from the existing-declaration check, I added
only a sandbox scratch probe, `scratch/ImportFlatBaseChange.lean`, containing a
module header and an import of
`WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChange`. The prescribed
`scompile.py Q39 sk-d-real-setup <probe>` failed identically in both its overlay
and server confirmation, before compiling the probe. The exact terminal
server diagnostic is:

```
WeilConjectures/AlgebraicGeometry/Cohomology/FlatBaseChange.lean: timeout after 60 s
```

The package's other completed dependencies were reused as cached overrides in
that confirmation. Thus the remaining compiler-gate failure also occurs when
importing the existing dependency alone, independently of the delivered node
record or any new statement. No Lean source module is submitted by this
existing-declaration packet. The read-only library and launcher scripts were
not modified, the per-file time limit was not raised, and nothing was pushed.
The node record and this report remain in the sandbox for the next retry.


## Current-source recheck (2026-10-21)

Reopened the item, its 17 dependency records and their declarations, the current
server RealSheavesSetup source, and both identical blueprint source texts. The
existing bundle still matches the sketch clause by clause. Refreshed the
LeanFinder search (eight separate Frobenius/function-field hits), the Loogle
query `FiniteField.frobeniusAlgEquivOfAlgebraic, AlgebraicGeometry.Smooth`
(zero hits), and Mathlib FieldTheory grep for Frobenius/setup (14 separate
Frobenius hits). No replacement for the existing bundle was found.

The required initial dry run again timed out compiling FlatBaseChange in both
the overlay and server confirmation. All subsequent experiments are sandbox
copies compiled only by scompile.py; the shared repository remains read-only.
The ring-action constructors with no_expose and the replacement of base-change
abbreviations by ordinary definitions did not eliminate the timeout. These
unsuccessful experiments are retained only under scratch and are not submitted.

Profiling a sequential sandbox copy identified the concrete hot definitions:
`TopCat.Sheaf.extFreeSheafZeroAddEquiv` took 13.9–14.7 seconds;
`AlgebraicGeometry.Scheme.Modules.sectionsLinearEquiv` took 31.8 seconds.
The associated value elaboration was much shorter, showing that merely
changing reducibility of the surrounding maps did not fix the expensive
structure construction/checking. A diagnostic prefix (not a proposed split
or delivery) compiled in 16.2/15.4 seconds, confirming that the consumer
linear-equivalence definition accounts for the additional cost.

## Definition performance repair

The full repaired FlatBaseChange module compiled with no warnings or errors in
both scompile.py passes: sandbox 56.0 seconds and library 55.6 seconds, each
under the standard 60-second limit. No timeout limit was changed.

The candidate is retained at
`lean/WeilConjectures/AlgebraicGeometry/Cohomology/FlatBaseChange.lean` in this
sandbox; the complete unified diff is `scratch/flat-base-change-repair.patch`.
It factors the free-sheaf evaluation equivalence as an additive equivalence,
then composes using AddEquiv.trans. It replaces the two concrete linear
structure literals by AddEquiv.toLinearEquiv, with the explicit sectionsModule
target ensuring the intended scalar action is selected. The canonical forward
and inverse maps and every existing public signature are preserved. The
existing consumer proofs in the full module compile against the replacement;
no new axioms or sorry proofs are introduced. The shared repository was never
edited. This is the definition-level timeout repair explicitly requested in
the resumption brief, rather than a split of the timed-out module.

## Delivery tool refusal

After the complete successful compile, the required dry run was attempted with
the repaired source file in the sandbox packet. deliver2.py rejected it before
compilation or preflight, with exit code 1 and exactly:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/Cohomology/FlatBaseChange.lean
```

The latest brief explicitly requires changing the definition responsible for
this dependency timeout. The source file cannot be renamed to a Sheaf module:
its existing imports and declaration names belong to the adopted upstream
module, and the original import would still compile the unfixed source. No
launcher tool was edited, copied, or bypassed. Nothing was pushed. The blocker
is the delivery wrapper's refusal of the authorized source repair, rather
than an uninvestigated compile timeout. The existing item record, complete
source repair and unified diff remain in this sandbox.

## Original-module-path follow-up

The same repaired text was subsequently compiled from its retained original
module path using scompile.py. Unlike the two earlier successful temporary
module passes (56.0 and 55.6 seconds), this call exceeded 60 seconds in both
the sandbox pass and server confirmation:

```
LOCAL COMPILE (exit 124)
sandbox Sheaf.Stage2.Sandbox0
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit
SERVER CONFIRMATION
WeilConjectures/AlgebraicGeometry/Cohomology/FlatBaseChange.lean: timeout after 60 s
```

Thus the candidate is not ready to land: its timing is not robustly below the
limit. The successful temporary-module probes are evidence of a partial
performance improvement, not certification of the original module. Further
work on this source definition is required. Independently of that work, the
required delivery wrapper rejects this original upstream source path before
any preflight; that actual path refusal is the tool blocker being reported.
No script was altered and no delivery was pushed.

## Retry against the current published library (2026-10-21)

The first required dry run reproduced the exact upstream-path refusal.
The retained candidate repair has been moved to
`scratch/retained-upstream-repair/FlatBaseChange.lean` (no work discarded),
to test the original existing-declaration packet against current published
artifacts. This does not submit or bypass the rejected source repair.

## Final validation (2026-10-21)

The current published library resolves the previous dependency-build failures.
With the historical upstream repair retained only under scratch, the prescribed
dry run returned:

```
OK (dry run): commit 4542d4e74b4 passes the preflight and compiles; nothing pushed
```

The delivered packet consists solely of this report and the item node with its
`lean` field attached to the existing RealSheavesSetup bundle. A final self-check
confirmed that `lean` is the only changed node field, the recorded signature is
verbatim, both blueprint source texts still agree, and no Lean source file is
submitted. The existing bundle was reread clause by clause against the source;
no mathematical change or unresolved statement dispute was found. The earlier
compile timeouts and path refusals above are historical, not current blockers.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
