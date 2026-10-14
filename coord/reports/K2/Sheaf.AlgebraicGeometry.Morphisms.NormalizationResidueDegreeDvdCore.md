## What changed

Corrected `AlgebraicGeometry.Scheme.normalization_residue_degree_dvd_core` to the actual
finite flat Galois domain calculation with a subgroup `T` of `G`. Proved it from Mathlib's
fundamental identity and Lagrange's theorem. Its old unrelated scheme/group interface was false.
Added `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkGaloisModel` for the
geometric comparison the caller previously omitted. Adapted only the forced proof and proof
imports of `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd`;
its existing signature, visibility and docstring stay identical. Updated both existing DAG
routes and the core's statement correction; added the model node.

## Proved and sorry left

Old hole retired by statement correction:
`AlgebraicGeometry.Scheme.normalization_residue_degree_dvd_core`, node
`lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core`.
The corrected arithmetic theorem is fully proved from Mathlib (no sorry dependency).
The unchanged root-chart theorem is proved by obtaining a geometric model, transporting the
residue-degree equality and applying the arithmetic theorem.

One hole added:
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_galois_model`, node
`lem-sbc-root-normalization-generic-stalk-galois-model`.
Its entire proof is `by sorry`; its docstring and node give the full local-model construction.
No original false statement is claimed proved. This is an interface repair and a decomposition
of the caller's geometric/arithmetic argument, not a net hole reduction (closed 1, added 1).
There are no other sorries in the delivered files and no data definitions.

## No longer needed

The corrected core no longer imports:
- `Mathlib.AlgebraicGeometry.Normalization`;
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`;
- `WeilConjectures.AlgebraicGeometry.Regular`.

Their geometry remains necessary in the caller and new model module; no claim is made that
these modules leave the targets' closure. The arithmetic core no longer needs its old geometric
statement dependencies: `def-weil-etale-morphism`, `def-weil-finite-integral-morphism`,
`def-nagata-effective-cartier-ideal`, `def-weil-regular-scheme`, `def-pc-integral-scheme`,
`def-weil-residue-field`, `def-weil-vector-space-dimension`. These remain in the model/caller.
No blueprint unit step is bypassed, and no other node or module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier counterexample is valid. The original core allows G trivial and a normalization
residue extension C/R of degree two. Its plan has no proof dependencies, and the asserted
Galois factor step cannot follow from a group with no action. Regularity of D also does not
imply regularity of the ambient generic divisor stalk. The source Tag 09EB assumes a DVR and
an actual finite Galois fraction-field extension. The root-chart caller retains the missing
regular local hypotheses, torsor and compatibility; the new model uses all of them.
The earlier product-factorization split was false and equivalent to divisibility; it remains
removed. The new model instead constructs a finite flat Galois domain over the actual stalk,
a subgroup action and a prime, and compares its inertia degree; it does not assert divisibility
or a numerical factorization of |G|. The arithmetic then comes from proved Mathlib declarations.

## New nodes

`lem-sbc-root-normalization-generic-stalk-galois-model`: the geometric local model and residue
comparison, in `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkGaloisModel`.
Its source is the parent root-chart argument and Stacks Tags 0307 and 09EB. Searches found only
the arithmetic ramification identity, not this scheme comparison; no matching blueprint node.
The witness is used only by existential elimination in a proof, not chosen to define data.

Change record: `coord/changes/normalization-residue-degree-dvd-core.md`.

## Statement corrected

The old scheme statement was false as recorded above. The corrected core is the arithmetic
invariant for an explicit finite flat Galois domain extension and a subgroup of G, following
Tag 09EB's actual Galois assumptions and Mathlib's generalization. The root-chart caller's
statement is untouched. There are zero DAG citers of the old core in the base: its sole Lean
caller had omitted that dependency from its DAG. Its proof route now records both the model
and the corrected core. The unit realized record is empty; all unit steps and routes stay.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd` (unclaimed):
its original final application fails against the changed core with "Invalid argument name V"
and "Application type mismatch: p ... expected Subgroup G". The signature is byte-for-byte
unchanged. The sole added proof import supplies the missing geometry; the old local aliases and
final exact application are replaced by obtaining the Galois model, installing its instances,
and transporting the inertia-degree comparison into the corrected arithmetic theorem.
The original module was compiled against the changed overlay and failed with those errors.
The adapted module is compiled in the delivered set. All changed proof lines are necessary to
supply the corrected core's hypotheses; no extra statement, visibility or docstring edits.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered core and the forced caller adaptation with the repository versions.
The corrected core intentionally changes its intermediate statement under the recorded change;
the caller's theorem signature, visibility, and docstring are unchanged. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; the arithmetic core has no
`sorry`, and the only remaining `sorry` is the named geometric model theorem with its matching
node and proof docstring. The arithmetic proof uses the Mathlib fundamental identity and
subgroup-card divisibility. Verdict: pass.
3. Checked the model statement and node for truth and strength: it exposes exactly the finite
flat Galois local model and residue-degree equality needed by the caller, while making no
divisibility claim. Searches found no existing declaration for this geometric comparison.
Verdict: pass.
4. Checked the proof downward and the imports. The core uses only the two Mathlib imports it
needs; the caller's added model import is required by its proof. The report lists removed
imports and old arithmetic dependencies, and no unnecessary route bypasses a unit step. Verdict:
pass.
5. Checked the updated node proof routes and proof dependencies against the Lean proofs, and
the model node's metadata, source, and `lean` record. The unit's realized record remains empty as
before. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof or statement edits
were needed after compilation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd
Original against changed dependencies failed:
```
/tmp/forced-adaptation-4jsk_ccj/lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericStalkResidueDegreeDvd.lean:98:66: error: Application type mismatch: The argument
  p
has type
  pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) ⟶ ↑V
of sort `Type u` but is expected to have type
  Subgroup G
of sort `Type (u + 1)` in the application
  @normalization_residue_degree_dvd_core ?m.357 ?m.358 ?m.359 ?m.360 ?m.361 ?m.362 ?m.363 ?m.364 ?m.365 G ?m.366 ?m.367
    p
/tmp/forced-adaptation-4jsk_ccj/lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericStalkResidueDegreeDvd.lean:98:46: error: Invalid argument name `V` for function `normalization_residue_degree_dvd_core`

Hint: Perhaps you meant one of the following parameter names:
  • `R`: V̵R̲
  • `S`: V̵S̲
  • `G`: V̵G̲
  • `T`: V̵T̲
  • `q`: V̵q̲

(with the modules compiled into /tmp/forced-adaptation-4jsk_ccj/.lbuild) [6.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by K2

1. Compared each delivered module with the repository version. The arithmetic core has the
intentional statement correction recorded in `coord/changes/normalization-residue-degree-dvd-core.md`;
the caller's signature is unchanged, and the new model module is separately recorded. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The arithmetic
core and caller contain no `sorry`; the sole remaining hole is the named model theorem, with a matching
docstring and DAG node. Verdict: pass.
3. Checked the corrected arithmetic statement and the model split for truth and strength. The core is
the finite-flat Galois subgroup calculation, and the model exposes only the local comparison needed by
the caller. Verdict: pass.
4. Checked proof routes and imports. The core uses the Mathlib ramification identity and private coset
import; the caller's model import is required. Removed imports and no longer-needed dependencies are
listed above, and the unit route is retained. Verdict: pass.
5. Checked DAG statements, proof dependencies, proof origins, and the forced adaptation record against
the Lean code. The model node has complete source and proof documentation; no accidental target change
appears. Verdict: pass.

Changed during this second reading: added this required review section only; no Lean proof or statement
edits were needed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd
Original against changed dependencies failed:
```
/tmp/forced-adaptation-zcupbzzq/lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericStalkResidueDegreeDvd.lean:98:66: error: Application type mismatch: The argument
  p
has type
  pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) ⟶ ↑V
of sort `Type u` but is expected to have type
  Subgroup G
of sort `Type (u + 1)` in the application
  @normalization_residue_degree_dvd_core ?m.357 ?m.358 ?m.359 ?m.360 ?m.361 ?m.362 ?m.363 ?m.364 ?m.365 G ?m.366 ?m.367
    p
/tmp/forced-adaptation-zcupbzzq/lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationGenericStalkResidueDegreeDvd.lean:98:46: error: Invalid argument name `V` for function `normalization_residue_degree_dvd_core`

Hint: Perhaps you meant one of the following parameter names:
  • `R`: V̵R̲
  • `S`: V̵S̲
  • `G`: V̵G̲
  • `T`: V̵T̲
  • `q`: V̵q̲

(with the modules compiled into /tmp/forced-adaptation-zcupbzzq/.lbuild) [4.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
