## What changed

Corrected the intermediate theorem `CochainComplex.universalH0_split_factorization`
in `Sheaf.Algebra.Homology.UniversalH0SplitFactorization`: the section equation is
`r ≫ e = 𝟙 I`, rather than `e ≫ r = 𝟙 (P.X 0)`. All hypotheses, universes, maps,
and the other two conclusions stay the same. No Challenge target changes.

The corrected theorem now has a complete Lean proof from one strictly local algebra
lemma in the new module `Sheaf.Algebra.Homology.UniversalH0CokernelLocalFree`.
The proof obtains finite presentation of the cokernel from finite presentation of
P.X 1 and finite generation of the image, uses freeness of the localizations to
obtain projectivity, splits the quotient, explicitly constructs the image projection
as `id - t ∘ pi`, proves the image projective as a retract, and splits the surjection
onto the image. The intermediate module is only a proof import; the other added
proof import is `Mathlib.RingTheory.LocalProperties.Projective`.

Adapted exactly line 74 of the already proved caller
`Sheaf.Algebra.Homology.UniversalH0SplitDifferential`, retaining every signature and
visibility. Its proof now reassociates `r ≫ e ≫ p` before using the section equation.
Updated both existing nodes to the actual Lean route. The factorization node no
longer refers to its own caller for its hypotheses or proof; its statement spells
those hypotheses out. The caller node now records its existing factorization route.

Change record: `coord/changes/universalH0-split-factorization-section.md`.

Validation: the new module, corrected factorization, and adapted caller compile
individually in dependency order with lcompile.py. The original caller fails when
compiled against the corrected dependency, at its former associativity rewrite.
`scratchpad/Counterexample.lean` also compiles: it proves that the original two
retraction equations are impossible for the zero endomorphism of the Z-module Z.

## Proved and sorry left

Closed the one original hole in the corrected version of
`CochainComplex.universalH0_split_factorization`
(node `new-universal-h0-split-factorization`). The original false statement is not
claimed proved. Its correction is recorded separately below.

Added one hole: `CochainComplex.universalH0_cokernel_local_free`
(node `new-universal-h0-cokernel-local-free`), the local unit-minor and universal-kernel
part of the argument. Its proof is exactly `:= by sorry`, and its docstring gives the
full natural-language proof and source. No other sorry remains in the delivered
modules. The caller `CochainComplex.universalH0_split_differential` remains proved.

This is a decomposition (one hole closed, one added, net zero), plus correction of a
false intermediate statement. The finite-presentation argument, passage from local
freeness to global projectivity, explicit image projection, both splittings, and
composition identities are proved in Lean. The remaining theorem provides only
freeness of each localized cokernel, not global projectivity or factorization maps.

## No longer needed

No existing import removed. No module is claimed globally pruned.
The old proof dependency of `new-universal-h0-split-factorization` on
`lem-sc-universal-h0-split-differential` is removed: using that caller to prove its
own factorization would be circular in Lean. Its old statement dependency is also
removed by spelling out the unchanged hypotheses.

The caller node's former direct proof dependencies
`lem-weil-pbc-finite-projective-finitely-presented`,
`lem-weil-pbc-finite-projective-prime-local-free`, and
`lem-weil-pbc-finitely-presented-flat-module-projective` are replaced by its actual
factorization dependency. Finite presentation and local freeness remain needed
below the factorization node. The proof uses Mathlib's local projectivity theorem
instead of explicitly passing through flatness, so
`lem-weil-pbc-finitely-presented-flat-module-projective` is not needed on this route.
No blueprint unit statement or realized proof step is bypassed; this unit's
`realized` statement and steps are empty, and the fixed-affine splitting route stays.

## Where the brief, the DAG or earlier work was wrong

The original section equation had the wrong order and object. Take R = Z and P
concentrated in degree zero with P.X 0 = Z. Every scalar extension is B concentrated
in degree zero, so its H0 is B; P.X 1 and P.X (-1) are zero. The first differential
is zero. The original equations would give
`id = e r = e(p q)r = (e p)q r = 0`, a contradiction on Z. The scratch proof certifies
the algebraic contradiction, while the identification of the single-term complex
and its scalar extensions in this counterexample is stated here mathematically.

The docstring and Stacks image-splitting argument require the source-to-image
surjection to have a section. This is the corrected equation `r ≫ e = id_I`.
The generalized-inverse caller only needs that equation. The original DAG record
for the caller had not been updated when its proof was changed by G2 to use the
factorization, and the factorization node pointed back at that caller as a proof
dependency. The delivered records replace these stale routes by an acyclic one.

Searches were run with LeanFinder, Loogle, grep, and LeanSearch through msearch.py.
LeanFinder found the finite-presentation and local-projectivity ingredients;
Loogle found `Module.Projective.of_split`; grep found quotient and range lemmas.
LeanSearch returned Internal Server Error and is recorded as unavailable.
No existing theorem with the full universal H0 hypothesis was found. The sources
read were [Stacks Tag 00O0](https://stacks.math.columbia.edu/tag/00O0), its
unit-minor proof, and [Tag 00NX](https://stacks.math.columbia.edu/tag/00NX), its
finite-presentation/local-freeness equivalence. The rank-(n-1) adaptation is from
the parent node's local argument; it does not apply residue-injectivity to d itself.

## New nodes

`new-universal-h0-cokernel-local-free`, module
`Sheaf.Algebra.Homology.UniversalH0CokernelLocalFree`, isolates the local argument:
at a prime, eliminate a unit minor of size n-1; the A-algebra H0 test gives an
injective multiplication-by-c description of the last kernel, forcing the remaining
matrix column to vanish. The cokernel is then free. This stops before all global
projectivity and splitting steps, which are implemented in the item. Edge cases:
for source rank one the identity block is empty; source rank zero over a nonzero
local ring contradicts the residue-field H0 test; over the zero ring there are no
prime ideals; if P.X 1 is zero its cokernel is zero and hence locally free. No
additional hypothesis is imposed.

The change record is `coord/changes/universalH0-split-factorization-section.md`.

## Statement corrected

Old statement: under the hypotheses of
`lem-sc-universal-h0-split-differential`, there are I,e,p,r,q with `d=e p`,
`e r=id_(P.X 0)` and `p q=id_I`.

New statement: under the same hypotheses, spelled out in the node, there are the
same maps with `d=e p`, `r e=id_I` and `p q=id_I`. This is the image/quotient splitting
of Stacks Tags 00O0 and 00NX, not a weakening to obtain a proof of the false claim.
The false assertion is explicitly replaced by the source's intended intermediate
assertion. The existing node and change record preserve the old statement verbatim.

There were no pre-existing DAG citers of `new-universal-h0-split-factorization` in
stmt_deps or proof_deps. The actual Lean caller was
`CochainComplex.universalH0_split_differential`; its use still holds, with the forced
one-line reassociation adaptation. Its unchanged conclusion `d s d=d` is proved
using `s=q r`. No public definition or target type depends on the changed statement.

## Forced adaptations

`Sheaf.Algebra.Homology.UniversalH0SplitDifferential` (unclaimed in the checkout):
original line 74 fails against the corrected item:

```text
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  r ≫ e
in the target expression
  (e ≫ r) ≫ e ≫ p = P.d 0 1
her : r ≫ e = 𝟙 I
```

Changed only that line from
`rw [← Category.assoc, her, Category.id_comp, hfac]` to
`rw [← Category.assoc r e p, her, Category.id_comp, ← hfac]`.
Reassociating the inner factors is forced by the corrected section equation; the
last reverse rewrite uses the factorization in the direction now needed. The
adapted module compiles. All its signatures, declarations, visibility, imports,
and other proof lines stay identical.

## Second reading by N3

1. **Statements and interfaces.** Compared each delivered module with the
repository version. Existing declarations retain their signatures except for the
documented correction of the intermediate factorization equation; no target
statement changed. The adapted caller keeps its interface byte for byte.

2. **Proof validity.** Compiled the new local-freeness module, the corrected
factorization, and the forced caller adaptation with `lcompile.py --all`; all
three compile. The only remaining `sorry` is the named theorem
`CochainComplex.universalH0_cokernel_local_free`, with a matching node and
natural-language proof. No definitions contain `sorry`, and no forbidden
declarations occur.

3. **Split-off statement.** Checked the local-freeness theorem against the
unit-minor argument and its prime-local edge cases (empty minor, zero source,
and zero ring). It is strictly simpler than the factorization and supplies only
the missing local input. Searches found no existing theorem with this statement.

4. **Pruning and route.** The factorization proof follows the local-freeness,
finite-presentation, quotient-splitting, and retract-projectivity route. Its
proof dependencies and imports match the declarations actually used; the old
circular dependency on the caller is removed. The unit record remains
unchanged.

5. **DAG agreement.** Updated the factorization and local-freeness nodes with
the actual statements, proof steps, dependencies, source, and Lean declarations.
The forced caller adaptation is recorded with its original compiler error and
the single necessary reassociation change.

Changed after this reading: added this review record only; no further Lean or
DAG changes were needed.

## Forced adaptations

### Sheaf.Algebra.Homology.UniversalH0SplitDifferential
Original against changed dependencies failed:
```
/tmp/forced-adaptation-vjiep02h/lean/Sheaf/Algebra/Homology/UniversalH0SplitDifferential.lean:74:28: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  r ≫ e
in the target expression
  (e ≫ r) ≫ e ≫ p = P.d 0 1

R : Type v
inst✝ : CommRing R
P : CochainComplex (ModuleCat R) ℤ
hf0 : Module.Finite R ↑(P.X 0)
hf1 : Module.Finite R ↑(P.X 1)
hp0 : Module.Projective R ↑(P.X 0)
hp1 : Module.Projective R ↑(P.X 1)
hneg : IsZero (P.X (-1))
hzero :
  ∀ (B : Type v) [inst : CommRing B] (φ : R →+* B),
    let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P;
    Nonempty (PB.homology 0 ≅ ModuleCat.of B B)
I : ModuleCat R
e : P.X 0 ⟶ I
p : I ⟶ P.X 1
r : I ⟶ P.X 0
q : P.X 1 ⟶ I
hfac : P.d 0 1 = e ≫ p
her : r ≫ e = 𝟙 I
hpq : p ≫ q = 𝟙 I
⊢ (e ≫ r) ≫ e ≫ p = P.d 0 1

(with the modules compiled into /tmp/forced-adaptation-vjiep02h/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
