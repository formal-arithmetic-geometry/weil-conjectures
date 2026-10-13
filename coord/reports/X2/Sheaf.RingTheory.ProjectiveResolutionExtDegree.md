## What changed

Repaired the duplicate Ext criterion in Sheaf.RingTheory.ProjectiveResolutionExtDegree:
ModuleCat.projective_resolution_ext_degree now bridges the explicit bounded-resolution
predicate to Mathlib HasProjectiveDimensionLE. It uses Mathlib's constructor,
projectivity criterion and dimension shifting, retaining the concrete resolution
construction. The old name remains attached to its existing node.

Adapted the three direct callers without changing any of their signatures or
visibility: ProjectiveResolutionExtAllDegrees, ProjectiveResolutionExtCharacterization
and AffinePolynomialResolutionOfStalkwise. The first two now use Mathlib Ext criteria;
the affine caller passes its dimension bound directly. All four modules compile cleanly.
DAG proofs match the new route. Change record:
coord/changes/projective-resolution-dimension-bridge.md.

## Proved and sorry left

Zero pre-existing holes closed; zero holes added; zero sorries left in all delivered
modules. This is a duplicate-repair delivery, not a new hole-closing delivery.
The resolution/dimension bridge ModuleCat.projective_resolution_ext_degree is proved
(node lem-weil-pbc-projective-resolution-ext-degree). The caller declarations
ModuleCat.projective_resolution_ext_all_degrees,
ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing and
AlgebraicGeometry.affinePolynomial_boundedResolution_of_stalkwise remain proved.

## No longer needed

No imports removed: Projective.Ext is needed for extMk_surjective, Augment for the
concrete resolution, and the existing public imports are retained.
The item's proof no longer uses lem-weil-pbc-projective-ext-criterion or
lem-weil-pbc-ext-long-exact-first-variable; Mathlib supplies their relevant conclusions.
The characterization node's old direct dependencies def-weil-pbc-exact-sequence,
def-weil-pbc-projective-module, def-pc-ext, def-weil-pbc-free-module,
lem-weil-pbc-free-module-projective, lem-weil-pbc-projective-ext-criterion,
lem-weil-pbc-ext-long-exact-first-variable and def-weil-pbc-finite-global-dimension
are replaced as proof dependencies by the bridge and all-degrees component.
Definitions still used by its statement remain statement dependencies.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The module has no sorry; it is assigned for upstream duplicate repair. The previous
attempt treated that as a stale assignment. The earlier landed Nat.succ spelling
change did not eliminate the duplicate Ext argument. Mathlib's dimension predicate
is not the explicit bounded-resolution predicate, so a bridge remains necessary;
Ext characterizations and dimension shifting can and now do reuse Mathlib.
The other independently named modules in the review's cluster are outside this
item's forced-adaptation scope and have not been changed.

## Statement corrected

The intermediate component now states HasProjectiveResolutionLE X n iff
HasProjectiveDimensionLE X n, replacing its duplicate single-degree Ext criterion.
Both DAG citers, lem-weil-pbc-projective-resolution-ext-all-degrees and
lem-pc-affine-polynomial-resolution-of-stalkwise, remain true, with adapted proofs.
The additional direct Lean caller ProjectiveResolutionExtCharacterization also
keeps its statement. No Challenge statement or definition changes.

## Second reading by X2

1. Compared all four delivered Lean modules with the repository versions. Existing
   declarations retain their signatures and visibility; the bridge statement change
   is recorded in the accompanying change record, with forced proof adaptations only.
   Verdict: pass.
2. Compiled every delivered module with `lcompile.py --all`; there are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. Axiom
   checks show only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Reviewed the changed bridge and caller statements and searched the library and
   Mathlib-facing declarations for duplicates. The bridge is a genuine reduction
   between the explicit resolution predicate and Mathlib dimension, and the callers
   preserve their original statements. Verdict: pass.
4. Checked the proof routes and imports. The explicit resolution construction remains
   in the bridge, Mathlib supplies Ext criteria and dimension shifting, and the unit
   route is retained. Proof-only Dimension and EnoughInjectives imports are private;
   no further safe pruning was found. Verdict: pass.
5. Checked all four DAG nodes against declarations, proof steps, dependencies,
   proof origins, and the recorded statement change. The realized unit route remains
   represented by the bridge and its callers. Verdict: pass.

Changed: repaired the duplicate bridge proof and adapted the three direct callers;
updated their DAG proof routes and retained the existing change record. No holes were
closed or added, and no additional modules were introduced.


## Forced adaptations

### Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise
Original against changed dependencies failed:
```
/tmp/forced-adaptation-nnpqlquu/lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean:97:4: error: Application type mismatch: The argument
  fun N ↦ HasProjectiveDimensionLT.subsingleton M (d + 1) (d + 1) le_rfl N
has type
  ∀ (N : ModuleCat (MvPolynomial (Fin n) ↑Γ(Y, U))), Subsingleton (Abelian.Ext M N (d + 1))
but is expected to have type
  HasProjectiveDimensionLE M d
in the application
  (ModuleCat.projective_resolution_ext_degree M d).mpr fun N ↦
    HasProjectiveDimensionLT.subsingleton M (d + 1) (d + 1) le_rfl N

(with the modules compiled into /tmp/forced-adaptation-nnpqlquu/.lbuild) [3.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees
Original against changed dependencies failed:
```
/tmp/forced-adaptation-3ksgny6w/lean/Sheaf/RingTheory/ProjectiveResolutionExtAllDegrees.lean:31:17: error: Function expected at
  (projective_resolution_ext_degree X (i - 1)).mp hle
but this term has type
  HasProjectiveDimensionLE X (i - 1)

Note: Expected a function because this term is being applied to the argument
  Y
/tmp/forced-adaptation-3ksgny6w/lean/Sheaf/RingTheory/ProjectiveResolutionExtAllDegrees.lean:38:10: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

case mpr
R : Type u
inst✝ : CommRing R
X : ModuleCat R
n : ℕ
h : ∀ (Y : ModuleCat R) (i : ℕ), n + 1 ≤ i → Subsingleton (Abelian.Ext X Y i)
⊢ HasProjectiveDimensionLE X n

(with the modules compiled into /tmp/forced-adaptation-3ksgny6w/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.ProjectiveResolutionExtCharacterization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-9okvb8nj/lean/Sheaf/RingTheory/ProjectiveResolutionExtCharacterization.lean:66:9: error: Application type mismatch: The argument
  projective_resolution_ext_degree X n
has type
  X.HasProjectiveResolutionLE n ↔ HasProjectiveDimensionLE X n
but is expected to have type
  X.HasProjectiveResolutionLE n ↔ ∀ (Y : ModuleCat R), Subsingleton (Abelian.Ext X Y (n + 1))
in the application
  And.intro (projective_resolution_ext_degree X n)

(with the modules compiled into /tmp/forced-adaptation-9okvb8nj/.lbuild) [2.2 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
